module Main (main) where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.ByteString as ByteString
import Data.Foldable
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Traversable
import Data.Void
import GHC.Types
import qualified Language.Haskell.Exts as HSE
import Language.Hell.Desugar
import Language.Hell.Evaluate
import Language.Hell.IRep
import Language.Hell.Parser
import Language.Hell.Term
import Language.Hell.Typecheck
import Language.Hell.UTerm
import Language.Hell.Utils
import qualified Options.Applicative as Options
import Type.Reflection (SomeTypeRep (..), typeRep, typeRepKind)
import qualified Type.Reflection as Type

------------------------------------------------------------------------------
-- Main entry point

data Command
  = Run FilePath
  | Check FilePath
  | Version
  | Exec String

main :: IO ()
main = dispatch =<< Options.execParser opts
  where
    opts =
      Options.info
        (commandParser Options.<**> Options.helper)
        ( Options.fullDesc
            <> Options.progDesc "Runs and typechecks Hell scripts"
            <> Options.header "hell - A Haskell-driven scripting language"
        )

commandParser :: Options.Parser Command
commandParser =
  Options.asum
    [ Run <$> Options.strArgument (Options.metavar "FILE" <> Options.help "Run the given .hell file")
    , Check <$> Options.strOption (Options.long "check" <> Options.metavar "FILE" <> Options.help "Typecheck the given .hell file")
    , Version <$ Options.flag () () (Options.long "version" <> Options.help "Print the version")
    , Exec <$> Options.strOption (Options.long "exec" <> Options.help "Execute the given expression" <> Options.metavar "EXPR")
    ]

dispatch :: Command -> IO ()
dispatch Version = putStrLn "2024-04-12"
dispatch (Run filePath) = do
  result <- parseFile filePath
  case result of
    Left e -> error $ e
    Right binds
      | anyCycles binds -> error "Cyclic bindings are not supported!"
      | otherwise ->
          case desugarAll binds of
            Left err -> error $ "Error desugaring! " ++ show err
            Right terms ->
              case lookup "main" terms of
                Nothing -> error "No main declaration!"
                Just main' ->
                  case inferExp mempty main' of
                    Left err -> error $ "Error inferring! " ++ show err
                    Right uterm ->
                      case check uterm Nil of
                        Left err -> error $ "Type checker error: " ++ show err
                        Right (Typed t ex) ->
                          case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                            Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                            Just Type.HRefl ->
                              case Type.eqTypeRep t (typeRep @(IO ())) of
                                Just Type.HRefl ->
                                  let action :: IO () = eval () ex
                                   in action
                                Nothing -> error $ "Type isn't IO (), but: " ++ show t
dispatch (Check filePath) = do
  result <- parseFile filePath
  case result of
    Left e -> error $ e
    Right binds
      | anyCycles binds -> error "Cyclic bindings are not supported!"
      | otherwise ->
          case desugarAll binds of
            Left err -> error $ "Error desugaring! " ++ show err
            Right terms ->
              case lookup "main" terms of
                Nothing -> error "No main declaration!"
                Just main' ->
                  case inferExp mempty main' of
                    Left err -> error $ "Error inferring! " ++ show err
                    Right uterm ->
                      case check uterm Nil of
                        Left err -> error $ "Type checker error: " ++ show err
                        Right (Typed t _ex) ->
                          case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                            Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                            Just Type.HRefl ->
                              case Type.eqTypeRep t (typeRep @(IO ())) of
                                Just Type.HRefl -> pure ()
                                Nothing -> error $ "Type isn't IO (), but: " ++ show t
dispatch (Exec string) = do
  case HSE.parseExpWithMode HSE.defaultParseMode {HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.BlockArguments, HSE.EnableExtension HSE.TypeApplications]} string of
    HSE.ParseFailed _ e -> error $ e
    HSE.ParseOk e ->
      case desugarExp mempty e of
        Left err -> error $ "Error desugaring! " ++ show err
        Right uterm ->
          case inferExp mempty uterm of
            Left err -> error $ "Type inferer error! " ++ show err
            Right iterm ->
              case check iterm Nil of
                Left err -> error $ "Type checker error: " ++ show err
                Right (Typed t ex) ->
                  case Type.eqTypeRep (typeRepKind t) (typeRep @Type) of
                    Nothing -> error $ "Kind error, that's nowhere near an IO ()!"
                    Just Type.HRefl ->
                      case Type.eqTypeRep t (typeRep @(IO ())) of
                        Just Type.HRefl ->
                          let action :: IO () = eval () ex
                           in action
                        Nothing -> error $ "Type isn't IO (), but: " ++ show t

--------------------------------------------------------------------------------
-- Infer

data InferError
  = UnifyError UnifyError
  | ZonkError ZonkError
  | ElabError ElaborateError
  deriving (Show)

-- | Note: All types in the input are free of metavars. There is an
-- intermediate phase in which there are metavars, but then they're
-- all eliminated. By the type system, the output contains only
-- determinate types.
inferExp
  :: Map String (UTerm SomeTypeRep)
  -> UTerm ()
  -> Either InferError (UTerm SomeTypeRep)
inferExp _ uterm =
  case elaborate uterm of
    Left elabError -> Left $ ElabError elabError
    Right (iterm, equalities) ->
      case unify equalities of
        Left unifyError -> Left $ UnifyError unifyError
        Right subs ->
          case traverse (zonkToStarType subs) iterm of
            Left zonkError -> Left $ ZonkError $ zonkError
            Right sterm -> pure sterm

-- | Zonk a type and then convert it to a type: t :: *
zonkToStarType :: Map IMetaVar (IRep IMetaVar) -> IRep IMetaVar -> Either ZonkError SomeTypeRep
zonkToStarType subs irep = do
  zonked <- zonk (substitute subs irep)
  toSomeTypeRep zonked

--------------------------------------------------------------------------------
-- Inference elaboration phase

newtype IMetaVar = IMetaVar0 Int
  deriving (Ord, Eq, Show)

data Elaborate = Elaborate
  { counter :: Int
  , equalities :: Set (Equality (IRep IMetaVar))
  }

data Equality a = Equality a a
  deriving (Show, Functor)

-- Equality/ordering that is symmetric.
instance (Ord a) => Eq (Equality a) where
  Equality a b == Equality c d = Set.fromList [a, b] == Set.fromList [c, d]

instance (Ord a) => Ord (Equality a) where
  Equality a b `compare` Equality c d = Set.fromList [a, b] `compare` Set.fromList [c, d]

data ElaborateError = UnsupportedTupleSize | BadInstantiationBug
  deriving (Show)

-- | Elaboration phase.
--
-- Note: The input term contains no metavars. There are just some
-- UForalls, which have poly types, and those are instantiated into
-- metavars.
--
-- Output type /does/ contain meta vars.
elaborate :: UTerm () -> Either ElaborateError (UTerm (IRep IMetaVar), Set (Equality (IRep IMetaVar)))
elaborate = fmap getEqualities . flip runStateT empty . flip runReaderT mempty . go
  where
    empty = Elaborate {counter = 0, equalities = mempty}
    getEqualities (term, Elaborate {equalities}) = (term, equalities)
    go :: UTerm () -> ReaderT (Map String (IRep IMetaVar)) (StateT Elaborate (Either ElaborateError)) (UTerm (IRep IMetaVar))
    go = \case
      UVar () string -> do
        env <- ask
        ty <- case Map.lookup string env of
          Just typ -> pure typ
          Nothing -> fmap IVar freshIMetaVar
        pure $ UVar ty string
      UApp () f x -> do
        f' <- go f
        x' <- go x
        b <- fmap IVar freshIMetaVar
        equal (typeOf f') (IFun (typeOf x') b)
        pure $ UApp b f' x'
      ULam () binding mstarType body -> do
        a <- case mstarType of
          Just ty -> pure $ fromSomeStarType ty
          Nothing -> fmap IVar freshIMetaVar
        vars <- lift $ bindingVars a binding
        body' <- local (Map.union vars) $ go body
        let ty = IFun a (typeOf body')
        pure $ ULam ty binding mstarType body'
      UForall () types forall' uniqs polyRep _ -> do
        -- Generate variables for each unique.
        vars <- for uniqs $ \uniq -> do
          v <- freshIMetaVar
          pure (uniq, v)
        -- Fill in the polyRep with the metavars.
        monoType <- for polyRep $ \uniq ->
          case List.lookup uniq vars of
            Nothing -> lift $ lift $ Left $ BadInstantiationBug
            Just var -> pure var
        -- Order of types is position-dependent, apply the ones we have.
        for_ (zip vars types) $ \((_uniq, var), someTypeRep) ->
          equal (fromSomeStarType someTypeRep) (IVar var)
        -- Done!
        pure $ UForall monoType types forall' uniqs polyRep (map (IVar . snd) vars)

bindingVars :: IRep IMetaVar -> Binding -> StateT Elaborate (Either ElaborateError) (Map String (IRep IMetaVar))
bindingVars irep (Singleton name) = pure $ Map.singleton name irep
bindingVars tupleVar (Tuple names) = do
  varsTypes <- for names $ \name -> fmap (name,) (fmap IVar freshIMetaVar)
  -- it's a left-fold:
  -- IApp (IApp (ICon (,)) x) y
  cons <- makeCons
  equal tupleVar $ foldl IApp (ICon cons) (map snd varsTypes)
  pure $ Map.fromList varsTypes
  where
    makeCons = case length names of
      2 -> pure $ SomeTypeRep (typeRep @(,))
      3 -> pure $ SomeTypeRep (typeRep @(,,))
      4 -> pure $ SomeTypeRep (typeRep @(,,,))
      _ -> lift $ Left $ UnsupportedTupleSize

equal :: (MonadState Elaborate m) => IRep IMetaVar -> IRep IMetaVar -> m ()
equal x y = modify $ \elaborate' -> elaborate' {equalities = equalities elaborate' <> Set.singleton (Equality x y)}

freshIMetaVar :: (MonadState Elaborate m) => m IMetaVar
freshIMetaVar = do
  Elaborate {counter} <- get
  modify $ \elaborate' -> elaborate' {counter = counter + 1}
  pure $ IMetaVar0 counter

--------------------------------------------------------------------------------
-- Unification

data UnifyError = OccursCheck | TypeConMismatch SomeTypeRep SomeTypeRep | TypeMismatch (IRep IMetaVar) (IRep IMetaVar)
  deriving (Show)

-- | Unification of equality constraints, a ~ b, to substitutions.
unify :: Set (Equality (IRep IMetaVar)) -> Either UnifyError (Map IMetaVar (IRep IMetaVar))
unify = foldM update mempty
  where
    update existing equality =
      fmap
        (`extends` existing)
        (examine (fmap (substitute existing) equality))
    examine (Equality a b)
      | a == b = pure mempty
      | IVar ivar <- a = bindMetaVar ivar b
      | IVar ivar <- b = bindMetaVar ivar a
      | IFun a1 b1 <- a
      , IFun a2 b2 <- b =
          unify (Set.fromList [Equality a1 a2, Equality b1 b2])
      | IApp a1 b1 <- a
      , IApp a2 b2 <- b =
          unify (Set.fromList [Equality a1 a2, Equality b1 b2])
      | ICon x <- a
      , ICon y <- b =
          if x == y
            then pure mempty
            else Left $ TypeConMismatch x y
      | otherwise = Left $ TypeMismatch a b

-- | Apply new substitutions to the old ones, and expand the set to old+new.
extends :: Map IMetaVar (IRep IMetaVar) -> Map IMetaVar (IRep IMetaVar) -> Map IMetaVar (IRep IMetaVar)
extends new old = fmap (substitute new) old <> new

-- | Apply any substitutions to the type, where there are metavars.
substitute :: Map IMetaVar (IRep IMetaVar) -> IRep IMetaVar -> IRep IMetaVar
substitute subs = go
  where
    go = \case
      IVar v -> case Map.lookup v subs of
        Nothing -> IVar v
        Just ty -> ty
      ICon c -> ICon c
      IFun a b -> IFun (go a) (go b)
      IApp a b -> IApp (go a) (go b)

-- | Do an occurrs check, if all good, return a binding.
bindMetaVar
  :: IMetaVar
  -> IRep IMetaVar
  -> Either UnifyError (Map IMetaVar (IRep IMetaVar))
bindMetaVar var typ
  | occurs var typ = Left OccursCheck
  | otherwise = pure $ Map.singleton var typ

-- | Occurs check.
occurs :: IMetaVar -> IRep IMetaVar -> Bool
occurs ivar = any (== ivar)

-- | Remove any metavars from the type.
--
-- <https://stackoverflow.com/questions/31889048/what-does-the-ghc-source-mean-by-zonk>
zonk :: IRep IMetaVar -> Either ZonkError (IRep Void)
zonk = \case
  IVar {} -> Left AmbiguousMetavar
  ICon c -> pure $ ICon c
  IFun a b -> IFun <$> zonk a <*> zonk b
  IApp a b -> IApp <$> zonk a <*> zonk b

--------------------------------------------------------------------------------
-- Parse with #!/shebangs

-- Parse a file into a list of decls, but strip shebangs.
parseFile :: String -> IO (Either String [(String, HSE.Exp HSE.SrcSpanInfo)])
parseFile filePath = do
  string <- ByteString.readFile filePath
  pure $ case HSE.parseModuleWithMode HSE.defaultParseMode {HSE.extensions = HSE.extensions HSE.defaultParseMode ++ [HSE.EnableExtension HSE.PatternSignatures, HSE.EnableExtension HSE.BlockArguments, HSE.EnableExtension HSE.TypeApplications]} (Text.unpack (dropShebang (Text.decodeUtf8 string))) >>= parseModule of
    HSE.ParseFailed _ e -> Left $ "Parse error: " <> e
    HSE.ParseOk binds -> Right binds

-- This should be quite efficient because it's essentially a pointer
-- increase. It leaves the \n so that line numbers are in tact.
dropShebang :: Text -> Text
dropShebang t = Maybe.fromMaybe t $ do
  rest <- Text.stripPrefix "#!" t
  pure $ Text.dropWhile (/= '\n') rest
