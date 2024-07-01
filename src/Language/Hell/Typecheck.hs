module Language.Hell.Typecheck where

import Data.ByteString (ByteString)
import Data.Text (Text)
import GHC.Types
import Language.Hell.IRep
import Language.Hell.Term
import Language.Hell.UTerm
import Language.Hell.Var
import System.Exit
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep, typeRepKind)
import qualified Type.Reflection as Type

--------------------------------------------------------------------------------
-- The type checker

data TypeCheckError
  = NotInScope String
  | TupleTypeMismatch
  | TypeCheckMismatch
  | TupleTypeTooBig
  | TypeOfApplicandIsNotFunction
  | LambdaIsNotAFunBug
  | InferredCheckedDisagreeBug
  | LambdaMustBeStarBug
  deriving (Show)

typed :: (Type.Typeable a) => a -> Typed (Term g)
typed l = Typed (Type.typeOf l) (Lit l)

-- The type environment and lookup
data TyEnv g where
  Nil :: TyEnv g
  Cons :: Binding -> TypeRep (t :: Type) -> TyEnv h -> TyEnv (h, t)

-- The top-level checker used by the main function.
check :: (UTerm SomeTypeRep) -> TyEnv () -> Either TypeCheckError (Typed (Term ()))
check = tc

-- Type check a term given an environment of names.
tc :: (UTerm SomeTypeRep) -> TyEnv g -> Either TypeCheckError (Typed (Term g))
tc (UVar _ v) env = do
  Typed ty v' <- lookupVar v env
  pure $ Typed ty (Var v')
tc (ULam (StarTypeRep lam_ty) s _ body) env =
  case lam_ty of
    Type.Fun bndr_ty' _
      | Just Type.HRefl <- Type.eqTypeRep (typeRepKind bndr_ty') (typeRep @Type) ->
          case tc body (Cons s bndr_ty' env) of
            Left e -> Left e
            Right (Typed body_ty' body') ->
              let checked_ty = Type.Fun bndr_ty' body_ty'
               in case Type.eqTypeRep checked_ty lam_ty of
                    Just Type.HRefl -> Right $ Typed lam_ty (Lam bndr_ty' body')
                    Nothing -> Left InferredCheckedDisagreeBug
    _ -> Left LambdaIsNotAFunBug
tc (ULam (SomeTypeRep {}) _ _ _) _ =
  Left LambdaMustBeStarBug
tc (UApp _ e1 e2) env =
  case tc e1 env of
    Left e -> Left e
    Right (Typed (Type.Fun bndr_ty body_ty) e1') ->
      case tc e2 env of
        Left e -> Left e
        Right (Typed arg_ty e2') ->
          case Type.eqTypeRep arg_ty bndr_ty of
            Nothing ->
              -- error $ "Type error: " ++ show arg_ty ++ " vs " ++ show bndr_ty
              Left TypeCheckMismatch
            Just (Type.HRefl) ->
              let kind = typeRepKind body_ty
               in case Type.eqTypeRep kind (typeRep @Type) of
                    Just Type.HRefl -> Right $ Typed body_ty (App e1' e2')
                    _ -> Left TypeCheckMismatch
    Right {} -> Left TypeOfApplicandIsNotFunction
-- Polytyped terms, must be, syntactically, fully-saturated
tc (UForall _ _ fall _ _ reps0) _env = go reps0 fall
  where
    go :: [SomeTypeRep] -> Forall -> Either TypeCheckError (Typed (Term g))
    go [] (Final typed') = pure typed'
    go (StarTypeRep rep : reps) (NoClass f) = go reps (f rep)
    go (StarTypeRep rep : reps) (OrdEqShow f) =
      if
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Int) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Bool) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Char) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Text) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @ByteString) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @ExitCode) -> go reps (f rep)
        | otherwise -> error $ "type doesn't have enough instances " ++ show rep
    go (SomeTypeRep rep : reps) (Monadic f) =
      if
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @IO) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @Maybe) -> go reps (f rep)
        | Just Type.HRefl <- Type.eqTypeRep rep (typeRep @[]) -> go reps (f rep)
        | Type.App either' _ <- rep
        , Just Type.HRefl <- Type.eqTypeRep either' (typeRep @Either) ->
            go reps (f rep)
        | otherwise -> error $ "type doesn't have enough instances " ++ show rep
    go _ _ = error "forall type arguments mismatch."

-- Make a well-typed literal - e.g. @lit Text.length@ - which can be
-- embedded in the untyped AST.
lookupVar :: String -> TyEnv g -> Either TypeCheckError (Typed (Var g))
lookupVar str Nil = Left $ NotInScope str
lookupVar v (Cons (Singleton s) ty e)
  | v == s = pure $ Typed ty (ZVar id)
  | otherwise = do
      Typed ty' v' <- lookupVar v e
      pure $ Typed ty' (SVar v')
lookupVar v (Cons (Tuple ss) ty e)
  | Just i <- lookup v $ zip ss [0 :: Int ..] =
      case ty of
        Type.App (Type.App tup x) y
          | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,)) ->
              case i of
                0 -> pure $ Typed x $ ZVar $ \(a, _) -> a
                1 -> pure $ Typed y $ ZVar $ \(_, b) -> b
                _ -> Left TupleTypeMismatch
        Type.App (Type.App (Type.App tup x) y) z
          | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,,)) ->
              case i of
                0 -> pure $ Typed x $ ZVar $ \(a, _, _) -> a
                1 -> pure $ Typed y $ ZVar $ \(_, b, _) -> b
                2 -> pure $ Typed z $ ZVar $ \(_, _, c) -> c
                _ -> Left TupleTypeMismatch
        Type.App (Type.App (Type.App (Type.App tup x) y) z) z'
          | Just Type.HRefl <- Type.eqTypeRep tup (typeRep @(,,,)) ->
              case i of
                0 -> pure $ Typed x $ ZVar $ \(a, _, _, _) -> a
                1 -> pure $ Typed y $ ZVar $ \(_, b, _, _) -> b
                2 -> pure $ Typed z $ ZVar $ \(_, _, c, _) -> c
                3 -> pure $ Typed z' $ ZVar $ \(_, _, _, d) -> d
                _ -> Left TupleTypeMismatch
        _ -> Left TupleTypeTooBig
  | otherwise = do
      Typed ty' v' <- lookupVar v e
      pure $ Typed ty' (SVar v')
