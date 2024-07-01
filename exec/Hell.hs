module Main (main) where

import qualified Control.Concurrent as Concurrent
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import qualified Data.Bool as Bool
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Builder as ByteString hiding (writeFile)
import qualified Data.ByteString.Lazy as L
import qualified Data.Either as Either
import qualified Data.Eq as Eq
import Data.Foldable
import qualified Data.Function as Function
import qualified Data.Generics.Schemes as SYB
import qualified Data.Graph as Graph
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Ord as Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Traversable
import Data.Void
import GHC.Types
import qualified Language.Haskell.Exts as HSE
import Language.Haskell.TH (Q)
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import Language.Hell.Evaluate
import Language.Hell.IRep
import Language.Hell.Parser
import Language.Hell.Term
import Language.Hell.Typecheck
import Language.Hell.UTerm
import Language.Hell.Var
import qualified Options.Applicative as Options
import qualified System.Directory as Dir
import System.Environment
import qualified System.IO as IO
import System.Process.Typed as Process
import qualified System.Timeout as Timeout
import Test.Hspec
import qualified Text.Show as Show
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep, typeRepKind, pattern TypeRep)
import qualified Type.Reflection as Type
import qualified UnliftIO.Async as Async

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
-- Desugar expressions

data DesugarError = InvalidConstructor String | InvalidVariable String | UnknownType String | UnsupportedSyntax String | BadParameterSyntax String | KindError | BadDoNotation | TupleTooBig | UnsupportedLiteral
  deriving (Show, Eq)

nestedTyApps :: HSE.Exp HSE.SrcSpanInfo -> Maybe (HSE.QName HSE.SrcSpanInfo, [HSE.Type HSE.SrcSpanInfo])
nestedTyApps = go []
  where
    go acc (HSE.App _ (HSE.Var _ qname) (HSE.TypeApp _ ty)) = pure (qname, ty : acc)
    go acc (HSE.App _ e (HSE.TypeApp _ ty)) = go (ty : acc) e
    go _ _ = Nothing

desugarExp
  :: Map String (UTerm ())
  -> HSE.Exp HSE.SrcSpanInfo
  -> Either DesugarError (UTerm ())
desugarExp globals = go
  where
    go = \case
      HSE.Paren _ x -> go x
      HSE.If _ i t e ->
        (\e' t' i' -> UApp () (UApp () (UApp () bool' e') t') i')
          <$> go e
          <*> go t
          <*> go i
      HSE.Tuple _ HSE.Boxed xs -> do
        xs' <- traverse go xs
        pure $ foldl (UApp ()) (tuple' (length xs)) xs'
      HSE.List _ xs -> do
        xs' <- traverse go xs
        pure $ foldr (\x y -> UApp () (UApp () cons' x) y) nil' xs'
      HSE.Lit _ lit' -> case lit' of
        HSE.Char _ char _ -> pure $ lit char
        HSE.String _ string _ -> pure $ lit $ Text.pack string
        HSE.Int _ int _ -> pure $ lit (fromIntegral int :: Int)
        _ -> Left $ UnsupportedLiteral
      app@HSE.App {} | Just (qname, tys) <- nestedTyApps app -> do
        reps <- traverse desugarType tys
        desugarQName globals qname reps
      HSE.Var _ qname ->
        desugarQName globals qname []
      HSE.App _ f x -> UApp () <$> go f <*> go x
      HSE.InfixApp _ x (HSE.QVarOp l f) y -> UApp () <$> (UApp () <$> go (HSE.Var l f) <*> go x) <*> go y
      HSE.Lambda _ pats e -> do
        args <- traverse desugarArg pats
        e' <- go e
        pure $ foldr (\(name, ty) inner -> ULam () name ty inner) e' args
      HSE.Con _ qname ->
        desugarQName mempty qname []
      HSE.Do _ stmts -> do
        let loop f [HSE.Qualifier _ e] = f <$> go e
            loop f (s : ss) = do
              case s of
                HSE.Generator _ pat e -> do
                  (s', rep) <- desugarArg pat
                  m <- go e
                  loop (f . (\f' -> UApp () (UApp () bind' m) (ULam () s' rep f'))) ss
                HSE.LetStmt _ (HSE.BDecls _ [HSE.PatBind _ pat (HSE.UnGuardedRhs _ e) Nothing]) -> do
                  (s', rep) <- desugarArg pat
                  value <- go e
                  loop (f . (\f' -> UApp () (ULam () s' rep f') value)) ss
                HSE.Qualifier _ e -> do
                  e' <- go e
                  loop (f . UApp () (UApp () then' e')) ss
                _ -> Left BadDoNotation
            loop _ _ = Left BadDoNotation
        loop id stmts
      e -> Left $ UnsupportedSyntax $ show e

desugarQName :: Map String (UTerm ()) -> HSE.QName HSE.SrcSpanInfo -> [SomeStarType] -> Either DesugarError (UTerm ())
desugarQName globals qname [] =
  case qname of
    HSE.UnQual _ (HSE.Ident _ string) -> pure $ UVar () string
    HSE.Qual _ (HSE.ModuleName _ "Main") (HSE.Ident _ string)
      | Just uterm <- Map.lookup string globals ->
          pure uterm
    HSE.Qual _ (HSE.ModuleName _ prefix) (HSE.Ident _ string)
      | Just uterm <- Map.lookup (prefix ++ "." ++ string) supportedLits ->
          pure $ uterm
    HSE.UnQual _ (HSE.Symbol _ string)
      | Just uterm <- Map.lookup string supportedLits ->
          pure $ uterm
    _ -> desugarPolyQName globals qname []
desugarQName globals qname treps = desugarPolyQName globals qname treps

desugarPolyQName :: (Show l) => p -> HSE.QName l -> [SomeStarType] -> Either DesugarError (UTerm ())
desugarPolyQName _ qname treps =
  case qname of
    HSE.Qual _ (HSE.ModuleName _ prefix) (HSE.Ident _ string)
      | Just (forall', vars, irep) <- Map.lookup (prefix ++ "." ++ string) polyLits -> do
          pure (UForall () treps forall' vars irep [])
    HSE.UnQual _ (HSE.Symbol _ string)
      | Just (forall', vars, irep) <- Map.lookup string polyLits -> do
          pure (UForall () treps forall' vars irep [])
    _ -> Left $ InvalidVariable $ show qname

desugarArg :: HSE.Pat HSE.SrcSpanInfo -> Either DesugarError (Binding, Maybe SomeStarType)
desugarArg (HSE.PatTypeSig _ (HSE.PVar _ (HSE.Ident _ i)) typ) =
  fmap (Singleton i,) (fmap Just (desugarType typ))
desugarArg (HSE.PatTypeSig _ (HSE.PTuple _ HSE.Boxed idents) typ)
  | Just idents' <- traverse desugarIdent idents =
      fmap (Tuple idents',) (fmap Just (desugarType typ))
desugarArg (HSE.PVar _ (HSE.Ident _ i)) =
  pure (Singleton i, Nothing)
desugarArg (HSE.PTuple _ HSE.Boxed idents)
  | Just idents' <- traverse desugarIdent idents =
      pure (Tuple idents', Nothing)
desugarArg (HSE.PParen _ p) = desugarArg p
desugarArg p = Left $ BadParameterSyntax $ show p

desugarIdent :: HSE.Pat HSE.SrcSpanInfo -> Maybe String
desugarIdent (HSE.PVar _ (HSE.Ident _ s)) = Just s
desugarIdent _ = Nothing

--------------------------------------------------------------------------------
-- Desugar types

desugarType :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeStarType
desugarType t = do
  someRep <- go t
  case someRep of
    StarTypeRep t' -> pure (SomeStarType t')
    _ -> Left KindError
  where
    go :: HSE.Type HSE.SrcSpanInfo -> Either DesugarError SomeTypeRep
    go = \case
      HSE.TyTuple _ HSE.Boxed types -> do
        tys <- traverse go types
        case tys of
          [StarTypeRep a, StarTypeRep b] ->
            pure $ StarTypeRep (Type.App (Type.App (typeRep @(,)) a) b)
          [StarTypeRep a, StarTypeRep b, StarTypeRep c] ->
            pure $ StarTypeRep (Type.App (Type.App (Type.App (typeRep @(,,)) a) b) c)
          [StarTypeRep a, StarTypeRep b, StarTypeRep c, StarTypeRep d] ->
            pure $ StarTypeRep (Type.App (Type.App (Type.App (Type.App (typeRep @(,,,)) a) b) c) d)
          _ -> Left TupleTooBig
      HSE.TyParen _ x -> go x
      HSE.TyCon _ (HSE.UnQual _ (HSE.Ident _ name))
        | Just rep <- Map.lookup name supportedTypeConstructors -> pure rep
      HSE.TyCon _ (HSE.Special _ HSE.UnitCon {}) -> pure $ StarTypeRep $ typeRep @()
      HSE.TyList _ inner -> do
        rep <- go inner
        case rep of
          StarTypeRep t' -> pure $ StarTypeRep $ Type.App (typeRep @[]) t'
          _ -> Left KindError
      HSE.TyFun _ a b -> do
        a' <- go a
        b' <- go b
        case (a', b') of
          (StarTypeRep aRep, StarTypeRep bRep) ->
            pure $ StarTypeRep (Type.Fun aRep bRep)
          _ -> Left KindError
      HSE.TyApp _ f a -> do
        f' <- go f
        a' <- go a
        case applyTypes f' a' of
          Just someTypeRep -> pure someTypeRep
          _ -> Left KindError
      t' -> Left $ UnknownType $ show t'

desugarTypeSpec :: Spec
desugarTypeSpec = do
  it "desugarType" $ do
    shouldBe (try "Bool") (Right (SomeStarType $ typeRep @Bool))
    shouldBe (try "Int") (Right (SomeStarType $ typeRep @Int))
    shouldBe (try "Bool -> Int") (Right (SomeStarType $ typeRep @(Bool -> Int)))
    shouldBe (try "()") (Right (SomeStarType $ typeRep @()))
    shouldBe (try "[Int]") (Right (SomeStarType $ typeRep @[Int]))
  where
    try e = case fmap (desugarType) $ HSE.parseType e of
      HSE.ParseOk r -> r
      _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Desugar all bindings

desugarAll :: [(String, HSE.Exp HSE.SrcSpanInfo)] -> Either DesugarError [(String, UTerm ())]
desugarAll = flip evalStateT Map.empty . traverse go . Graph.flattenSCCs . stronglyConnected
  where
    go :: (String, HSE.Exp HSE.SrcSpanInfo) -> StateT (Map String (UTerm ())) (Either DesugarError) (String, UTerm ())
    go (name, expr) = do
      globals <- get
      uterm <- lift $ desugarExp globals expr
      modify' $ Map.insert name uterm
      pure (name, uterm)

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
-- Occurs check

anyCycles :: [(String, HSE.Exp HSE.SrcSpanInfo)] -> Bool
anyCycles =
  any isCycle
    . stronglyConnected
  where
    isCycle = \case
      Graph.CyclicSCC {} -> True
      _ -> False

stronglyConnected :: [(String, HSE.Exp HSE.SrcSpanInfo)] -> [Graph.SCC (String, HSE.Exp HSE.SrcSpanInfo)]
stronglyConnected =
  Graph.stronglyConnComp
    . map (\thing@(name, e) -> (thing, name, freeVariables e))

anyCyclesSpec :: Spec
anyCyclesSpec = do
  it "anyCycles" $ do
    shouldBe (try [("foo", "\\z -> x * Z.y"), ("bar", "\\z -> Main.bar * Z.y")]) True
    shouldBe (try [("foo", "\\z -> Main.bar * Z.y"), ("bar", "\\z -> Main.foo * Z.y")]) True
    shouldBe (try [("foo", "\\z -> x * Z.y"), ("bar", "\\z -> Main.mu * Z.y")]) False
    shouldBe (try [("foo", "\\z -> x * Z.y"), ("bar", "\\z -> Main.foo * Z.y")]) False
  where
    try named =
      case traverse (\(n, e) -> (n,) <$> HSE.parseExp e) named of
        HSE.ParseOk decls -> anyCycles decls
        _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Get free variables of an HSE expression

freeVariables :: HSE.Exp HSE.SrcSpanInfo -> [String]
freeVariables =
  Maybe.mapMaybe unpack
    . SYB.listify (const True :: HSE.QName HSE.SrcSpanInfo -> Bool)
  where
    unpack = \case
      HSE.Qual _ (HSE.ModuleName _ "Main") (HSE.Ident _ name) -> pure name
      _ -> Nothing

freeVariablesSpec :: Spec
freeVariablesSpec = do
  it "freeVariables" $ shouldBe (try "\\z -> Main.x * Z.y") ["x"]
  where
    try e = case fmap freeVariables $ HSE.parseExp e of
      HSE.ParseOk names -> names
      _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Supported type constructors

supportedTypeConstructors :: Map String SomeTypeRep
supportedTypeConstructors =
  Map.fromList
    [ ("Bool", SomeTypeRep $ typeRep @Bool)
    , ("Int", SomeTypeRep $ typeRep @Int)
    , ("Char", SomeTypeRep $ typeRep @Char)
    , ("Text", SomeTypeRep $ typeRep @Text)
    , ("ByteString", SomeTypeRep $ typeRep @ByteString)
    , ("ExitCode", SomeTypeRep $ typeRep @ExitCode)
    , ("Maybe", SomeTypeRep $ typeRep @Maybe)
    , ("Either", SomeTypeRep $ typeRep @Either)
    , ("IO", SomeTypeRep $ typeRep @IO)
    , ("ProcessConfig", SomeTypeRep $ typeRep @ProcessConfig)
    ]

--------------------------------------------------------------------------------
-- Support primitives

supportedLits :: Map String (UTerm ())
supportedLits =
  Map.fromList
    [ -- Text I/O
      ("Text.putStrLn", lit t_putStrLn)
    , ("Text.hPutStr", lit t_hPutStr)
    , ("Text.putStr", lit t_putStr)
    , ("Text.getLine", lit t_getLine)
    , ("Text.writeFile", lit t_writeFile)
    , ("Text.readFile", lit t_readFile)
    , ("Text.appendFile", lit t_appendFile)
    , ("Text.readProcess", lit t_readProcess)
    , ("Text.readProcess_", lit t_readProcess_)
    , ("Text.readProcessStdout_", lit t_readProcessStdout_)
    , ("Text.setStdin", lit t_setStdin)
    , -- Text operations
      ("Text.eq", lit ((==) @Text))
    , ("Text.length", lit Text.length)
    , ("Text.concat", lit Text.concat)
    , ("Text.breakOn", lit Text.breakOn)
    , ("Text.lines", lit Text.lines)
    , ("Text.words", lit Text.words)
    , ("Text.unlines", lit Text.unlines)
    , ("Text.unwords", lit Text.unwords)
    , ("Text.intercalate", lit Text.intercalate)
    , ("Text.reverse", lit Text.reverse)
    , ("Text.toLower", lit Text.toLower)
    , ("Text.toUpper", lit Text.toUpper)
    , -- Needs Char operations.
      -- ("Text.any", lit Text.any),
      -- ("Text.all", lit Text.all),
      -- ("Text.filter", lit Text.filter),
      ("Text.take", lit Text.take)
    , ("Text.splitOn", lit Text.splitOn)
    , ("Text.takeEnd", lit Text.takeEnd)
    , ("Text.drop", lit Text.drop)
    , ("Text.stripPrefix", lit Text.stripPrefix)
    , ("Text.stripSuffix", lit Text.stripSuffix)
    , ("Text.isSuffixOf", lit Text.isSuffixOf)
    , ("Text.isPrefixOf", lit Text.isPrefixOf)
    , ("Text.dropEnd", lit Text.dropEnd)
    , ("Text.strip", lit Text.strip)
    , ("Text.replace", lit Text.replace)
    , ("Text.isPrefixOf", lit Text.isPrefixOf)
    , ("Text.isSuffixOf", lit Text.isSuffixOf)
    , ("Text.isInfixOf", lit Text.isInfixOf)
    , -- Int operations
      ("Int.show", lit (Text.pack . show @Int))
    , ("Int.eq", lit ((==) @Int))
    , ("Int.plus", lit ((+) @Int))
    , ("Int.subtract", lit (subtract @Int))
    , -- Bytes I/O
      ("ByteString.hGet", lit ByteString.hGet)
    , ("ByteString.hPutStr", lit ByteString.hPutStr)
    , ("ByteString.readProcess", lit b_readProcess)
    , ("ByteString.readProcess_", lit b_readProcess_)
    , ("ByteString.readProcessStdout_", lit b_readProcessStdout_)
    , -- Handles, buffering
      ("IO.stdout", lit IO.stdout)
    , ("IO.stderr", lit IO.stderr)
    , ("IO.stdin", lit IO.stdin)
    , ("IO.hSetBuffering", lit IO.hSetBuffering)
    , ("IO.NoBuffering", lit IO.NoBuffering)
    , ("IO.LineBuffering", lit IO.LineBuffering)
    , ("IO.BlockBuffering", lit IO.BlockBuffering)
    , -- Concurrent stuff
      ("Concurrent.threadDelay", lit Concurrent.threadDelay)
    , -- Bool
      ("Bool.True", lit Bool.True)
    , ("Bool.False", lit Bool.False)
    , ("Bool.not", lit Bool.not)
    , -- Get arguments
      ("Environment.getArgs", lit $ fmap (map Text.pack) getArgs)
    , ("Environment.getEnvironment", lit $ fmap (map (bimap Text.pack Text.pack)) getEnvironment)
    , ("Environment.getEnv", lit $ fmap Text.pack . getEnv . Text.unpack)
    , -- Current directory
      ("Directory.createDirectoryIfMissing", lit (\b f -> Dir.createDirectoryIfMissing b (Text.unpack f)))
    , ("Directory.createDirectory", lit (Dir.createDirectory . Text.unpack))
    , ("Directory.getCurrentDirectory", lit (fmap Text.pack Dir.getCurrentDirectory))
    , ("Directory.listDirectory", lit (fmap (fmap Text.pack) . Dir.listDirectory . Text.unpack))
    , ("Directory.setCurrentDirectory", lit (Dir.setCurrentDirectory . Text.unpack))
    , ("Directory.renameFile", lit (\x y -> Dir.renameFile (Text.unpack x) (Text.unpack y)))
    , ("Directory.copyFile", lit (\x y -> Dir.copyFile (Text.unpack x) (Text.unpack y)))
    , -- Process
      ("Process.proc", lit $ \n xs -> proc (Text.unpack n) (map Text.unpack xs))
    , ("Process.setEnv", lit $ Process.setEnv @() @() @() . map (bimap Text.unpack Text.unpack))
    , ("Process.runProcess", lit $ runProcess @IO @() @() @())
    , ("Process.runProcess_", lit $ runProcess_ @IO @() @() @())
    , -- Lists
      ("List.and", lit (List.and @[]))
    , ("List.or", lit (List.or @[]))
    ]

--------------------------------------------------------------------------------
-- Derive prims TH

polyLits :: Map String (Forall, [TH.Uniq], IRep TH.Uniq)
polyLits =
  Map.fromList
    $( let -- Derive well-typed primitive forms.
           derivePrims :: Q TH.Exp -> Q TH.Exp
           derivePrims m = do
            e <- m
            case e of
              TH.DoE Nothing binds -> do
                TH.listE $ map makePrim binds
              _ -> error $ "Expected plain do-notation, but got: " ++ show e

           nameUnique (TH.Name _ (TH.NameU i)) = i
           nameUnique _ = error "Bad TH problem in nameUnique."

           toTy :: TH.Type -> Q TH.Exp
           toTy = \case
            TH.AppT (TH.AppT TH.ArrowT f) x -> [|IFun $(toTy f) $(toTy x)|]
            TH.AppT f x -> [|IApp $(toTy f) $(toTy x)|]
            TH.ConT name -> [|ICon (SomeTypeRep $(TH.appTypeE (TH.varE 'typeRep) (TH.conT name)))|]
            TH.VarT a -> [|IVar $(TH.litE $ TH.IntegerL $ nameUnique a)|]
            TH.ListT -> [|ICon (SomeTypeRep (typeRep @[]))|]
            TH.TupleT 2 -> [|ICon (SomeTypeRep (typeRep @(,)))|]
            TH.TupleT 3 -> [|ICon (SomeTypeRep (typeRep @(,,)))|]
            TH.TupleT 4 -> [|ICon (SomeTypeRep (typeRep @(,,,)))|]
            TH.TupleT 0 -> [|ICon (SomeTypeRep (typeRep @()))|]
            t -> error $ "Uexpected type shape: " ++ show t

           -- Make a well-typed primitive form. Expects a very strict format.
           makePrim :: TH.Stmt -> Q TH.Exp
           makePrim
            ( TH.NoBindS
                ( TH.SigE
                    (TH.AppE (TH.LitE (TH.StringL string)) expr)
                    (TH.ForallT vars constraints typ)
                  )
              ) =
              let constrained = foldl getConstraint mempty constraints
                  vars0 =
                    map
                      ( \case
                          (TH.PlainTV v TH.SpecifiedSpec) -> TH.litE $ TH.IntegerL $ nameUnique v
                          _ -> error "The type variable isn't what I expected."
                      )
                      vars
                  ordEqShow = Set.fromList [''Ord, ''Eq, ''Show]
                  monadics = Set.fromList [''Functor, ''Applicative, ''Monad]
                  builder =
                    foldr
                      ( \case
                          (TH.PlainTV v TH.SpecifiedSpec) -> \rest ->
                            TH.appE
                              ( TH.conE
                                  ( case Map.lookup v constrained of
                                      Nothing -> 'NoClass
                                      Just constraints'
                                        | Set.isSubsetOf constraints' ordEqShow -> 'OrdEqShow
                                        | Set.isSubsetOf constraints' monadics -> 'Monadic
                                      _ -> error "I'm not sure what to do with this variable."
                                  )
                              )
                              ( TH.lamE
                                  [pure $ TH.ConP 'TypeRep [TH.VarT v] []]
                                  rest
                              )
                          _ -> error "Did not expect this type of variable!"
                      )
                      [|Final $ typed $(TH.sigE (pure expr) (pure typ))|]
                      vars
               in [|(string, ($builder, $(TH.listE vars0), $(toTy typ)))|]
           makePrim e = error $ "Should be of the form \"Some.name\" The.name :: T\ngot: " ++ show e

           -- Just tells us whether a given variable is constrained by a
           -- type-class or not.
           getConstraint m (TH.AppT (TH.ConT cls') (TH.VarT v)) =
            Map.insertWith Set.union v (Set.singleton cls') m
           getConstraint _ _ = error "Bad constraint!"
        in derivePrims
            [|
              do
                -- Operators
                "$" (Function.$) :: forall a b. (a -> b) -> a -> b
                "." (Function..) :: forall a b c. (b -> c) -> (a -> b) -> a -> c
                -- Monad
                "Monad.bind" (Prelude.>>=) :: forall m a b. (Monad m) => m a -> (a -> m b) -> m b
                "Monad.then" (Prelude.>>) :: forall m a b. (Monad m) => m a -> m b -> m b
                "Monad.return" return :: forall a m. (Monad m) => a -> m a
                -- Monadic operations
                "Monad.mapM_" mapM_ :: forall a m. (Monad m) => (a -> m ()) -> [a] -> m ()
                "Monad.forM_" forM_ :: forall a m. (Monad m) => [a] -> (a -> m ()) -> m ()
                "Monad.mapM" mapM :: forall a b m. (Monad m) => (a -> m b) -> [a] -> m [b]
                "Monad.forM" forM :: forall a b m. (Monad m) => [a] -> (a -> m b) -> m [b]
                "Monad.when" when :: forall m. (Monad m) => Bool -> m () -> m ()
                -- IO
                "IO.mapM_" mapM_ :: forall a. (a -> IO ()) -> [a] -> IO ()
                "IO.forM_" forM_ :: forall a. [a] -> (a -> IO ()) -> IO ()
                "IO.pure" pure :: forall a. a -> IO a
                "IO.print" (t_putStrLn . Text.pack . Show.show) :: forall a. (Show a) => a -> IO ()
                "Timeout.timeout" Timeout.timeout :: forall a. Int -> IO a -> IO (Maybe a)
                -- Show
                "Show.show" (Text.pack . Show.show) :: forall a. (Show a) => a -> Text
                -- Eq/Ord
                "Eq.eq" (Eq.==) :: forall a. (Eq a) => a -> a -> Bool
                "Ord.lt" (Ord.<) :: forall a. (Ord a) => a -> a -> Bool
                "Ord.gt" (Ord.>) :: forall a. (Ord a) => a -> a -> Bool
                -- Tuples
                "Tuple.(,)" (,) :: forall a b. a -> b -> (a, b)
                "Tuple.(,)" (,) :: forall a b. a -> b -> (a, b)
                "Tuple.(,,)" (,,) :: forall a b c. a -> b -> c -> (a, b, c)
                "Tuple.(,,,)" (,,,) :: forall a b c d. a -> b -> c -> d -> (a, b, c, d)
                -- Exceptions
                "Error.error" (error . Text.unpack) :: forall a. Text -> a
                -- Bool
                "Bool.bool" Bool.bool :: forall a. a -> a -> Bool -> a
                -- Function
                "Function.id" Function.id :: forall a. a -> a
                "Function.fix" Function.fix :: forall a. (a -> a) -> a
                -- Lists
                "List.cons" (:) :: forall a. a -> [a] -> [a]
                "List.nil" [] :: forall a. [a]
                "List.length" List.length :: forall a. [a] -> Int
                "List.concat" List.concat :: forall a. [[a]] -> [a]
                "List.drop" List.drop :: forall a. Int -> [a] -> [a]
                "List.take" List.take :: forall a. Int -> [a] -> [a]
                "List.map" List.map :: forall a b. (a -> b) -> [a] -> [b]
                "List.lookup" List.lookup :: forall a b. (Eq a) => a -> [(a, b)] -> Maybe b
                "List.sort" List.sort :: forall a. (Ord a) => [a] -> [a]
                "List.reverse" List.reverse :: forall a. [a] -> [a]
                "List.sortOn" List.sortOn :: forall a b. (Ord b) => (a -> b) -> [a] -> [a]
                -- Maybe
                "Maybe.maybe" Maybe.maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
                "Maybe.Nothing" Maybe.Nothing :: forall a. Maybe a
                "Maybe.Just" Maybe.Just :: forall a. a -> Maybe a
                "Maybe.listToMaybe" Maybe.listToMaybe :: forall a. [a] -> Maybe a
                -- Either
                "Either.either" Either.either :: forall a b x. (a -> x) -> (b -> x) -> Either a b -> x
                "Either.Left" Either.Left :: forall a b. a -> Either a b
                "Either.Right" Either.Right :: forall a b. b -> Either a b
                -- Async
                "Async.concurrently" Async.concurrently :: forall a b. IO a -> IO b -> IO (a, b)
                "Async.race" Async.race :: forall a b. IO a -> IO b -> IO (Either a b)
                "Async.pooledMapConcurrently_" Async.pooledMapConcurrently_ :: forall a. (a -> IO ()) -> [a] -> IO ()
                "Async.pooledForConcurrently_" Async.pooledForConcurrently_ :: forall a. [a] -> (a -> IO ()) -> IO ()
                "Async.pooledMapConcurrently" Async.pooledMapConcurrently :: forall a b. (a -> IO b) -> [a] -> IO [b]
                "Async.pooledForConcurrently" Async.pooledForConcurrently :: forall a b. [a] -> (a -> IO b) -> IO [b]
              |]
     )

--------------------------------------------------------------------------------
-- Internal-use only, used by the desugarer

cons' :: UTerm ()
cons' = unsafeGetForall "List.cons"

nil' :: UTerm ()
nil' = unsafeGetForall "List.nil"

bool' :: UTerm ()
bool' = unsafeGetForall "Bool.bool"

then' :: UTerm ()
then' = unsafeGetForall "Monad.then"

bind' :: UTerm ()
bind' = unsafeGetForall "Monad.bind"

tuple' :: Int -> UTerm ()
tuple' 0 = unsafeGetForall "Tuple.()"
tuple' 2 = unsafeGetForall "Tuple.(,)"
tuple' 3 = unsafeGetForall "Tuple.(,,)"
tuple' 4 = unsafeGetForall "Tuple.(,,,)"
tuple' _ = error "Bad compile-time lookup for tuple'."

unsafeGetForall :: String -> UTerm ()
unsafeGetForall key = Maybe.fromMaybe (error $ "Bad compile-time lookup for " ++ key) $ do
  (forall', vars, irep) <- Map.lookup key polyLits
  pure (UForall () [] forall' vars irep [])

--------------------------------------------------------------------------------
-- UTF-8 specific operations without all the environment gubbins
--
-- Much better than what Data.Text.IO provides

t_setStdin :: Text -> ProcessConfig () () () -> ProcessConfig () () ()
t_setStdin text = setStdin (byteStringInput (L.fromStrict (Text.encodeUtf8 text)))

t_readProcess :: ProcessConfig () () () -> IO (ExitCode, Text, Text)
t_readProcess c = do
  (code, out, err) <- b_readProcess c
  pure (code, Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcess_ :: ProcessConfig () () () -> IO (Text, Text)
t_readProcess_ c = do
  (out, err) <- b_readProcess_ c
  pure (Text.decodeUtf8 out, Text.decodeUtf8 err)

t_readProcessStdout_ :: ProcessConfig () () () -> IO Text
t_readProcessStdout_ c = do
  out <- b_readProcessStdout_ c
  pure (Text.decodeUtf8 out)

t_putStrLn :: Text -> IO ()
t_putStrLn = ByteString.hPutBuilder IO.stdout . (<> "\n") . ByteString.byteString . Text.encodeUtf8

t_hPutStr :: IO.Handle -> Text -> IO ()
t_hPutStr h = ByteString.hPutBuilder h . ByteString.byteString . Text.encodeUtf8

t_putStr :: Text -> IO ()
t_putStr = t_hPutStr IO.stdout

t_getLine :: IO Text
t_getLine = fmap Text.decodeUtf8 ByteString.getLine

t_writeFile :: Text -> Text -> IO ()
t_writeFile fp t = ByteString.writeFile (Text.unpack fp) (Text.encodeUtf8 t)

t_appendFile :: Text -> Text -> IO ()
t_appendFile fp t = ByteString.appendFile (Text.unpack fp) (Text.encodeUtf8 t)

t_readFile :: Text -> IO Text
t_readFile fp = fmap Text.decodeUtf8 (ByteString.readFile (Text.unpack fp))

--------------------------------------------------------------------------------
-- ByteString operations

b_readProcess :: ProcessConfig () () () -> IO (ExitCode, ByteString, ByteString)
b_readProcess c = do
  (code, out, err) <- readProcess c
  pure (code, L.toStrict out, L.toStrict err)

b_readProcess_ :: ProcessConfig () () () -> IO (ByteString, ByteString)
b_readProcess_ c = do
  (out, err) <- readProcess_ c
  pure (L.toStrict out, L.toStrict err)

b_readProcessStdout_ :: ProcessConfig () () () -> IO ByteString
b_readProcessStdout_ c = do
  out <- readProcessStdout_ c
  pure (L.toStrict out)

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

--------------------------------------------------------------------------------
-- Spec

_spec :: Spec
_spec = do
  freeVariablesSpec
  anyCyclesSpec
  desugarTypeSpec
