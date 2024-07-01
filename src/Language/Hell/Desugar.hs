module Language.Hell.Desugar where

import Control.Monad.Reader
import Control.Monad.State.Strict
import qualified Data.Graph as Graph
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Text as Text
import qualified Language.Haskell.Exts as HSE
import Language.Hell.IRep
import Language.Hell.TH
import Language.Hell.UTerm
import Language.Hell.Utils
import Type.Reflection (SomeTypeRep (..), typeRep)
import qualified Type.Reflection as Type

--------------------------------------------------------------------------------
-- Desugar expressions

data DesugarError
  = InvalidConstructor String
  | InvalidVariable String
  | UnknownType String
  | UnsupportedSyntax String
  | BadParameterSyntax String
  | KindError
  | BadDoNotation
  | TupleTooBig
  | UnsupportedLiteral
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
