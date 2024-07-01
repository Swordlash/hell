module Language.Hell.IRep where

import Data.Void
import GHC.Types
import Type.Reflection (SomeTypeRep (..), TypeRep, typeRep, typeRepKind)
import qualified Type.Reflection as Type

--------------------------------------------------------------------------------
-- Some type of kind *

data SomeStarType = forall (a :: Type). SomeStarType (TypeRep a)

deriving instance Show SomeStarType

instance Eq SomeStarType where
  SomeStarType x == SomeStarType y = Type.SomeTypeRep x == Type.SomeTypeRep y

pattern StarTypeRep t <- (toStarType -> Just (SomeStarType t))
  where
    StarTypeRep t = SomeTypeRep t

toStarType :: SomeTypeRep -> Maybe SomeStarType
toStarType (SomeTypeRep t) = do
  Type.HRefl <- Type.eqTypeRep (typeRepKind t) (typeRep @Type)
  pure $ SomeStarType t

-- | Supports up to 3-ary type functions, but not more.
applyTypes :: SomeTypeRep -> SomeTypeRep -> Maybe SomeTypeRep
applyTypes (SomeTypeRep f) (SomeTypeRep a) = do
  Type.HRefl <- Type.eqTypeRep (typeRepKind a) (typeRep @Type)
  if
    | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type)) ->
        pure $ SomeTypeRep $ Type.App f a
    | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type -> Type)) ->
        pure $ SomeTypeRep $ Type.App f a
    | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type -> Type -> Type)) ->
        pure $ SomeTypeRep $ Type.App f a
    | Just Type.HRefl <- Type.eqTypeRep (typeRepKind f) (typeRep @(Type -> Type -> Type -> Type -> Type)) ->
        pure $ SomeTypeRep $ Type.App f a
    | otherwise -> Nothing

--------------------------------------------------------------------------------
-- Inference type representation

data IRep v
  = IVar v
  | IApp (IRep v) (IRep v)
  | IFun (IRep v) (IRep v)
  | ICon SomeTypeRep
  deriving (Functor, Traversable, Foldable, Eq, Ord, Show)

data ZonkError
  = ZonkKindError
  | AmbiguousMetavar
  deriving (Show)

-- | A complete implementation of conversion from the inferer's type
-- rep to some star type, ready for the type checker.
toSomeTypeRep :: IRep Void -> Either ZonkError SomeTypeRep
toSomeTypeRep t = do
  go t
  where
    go :: IRep Void -> Either ZonkError SomeTypeRep
    go = \case
      IVar v -> pure (absurd v)
      ICon someTypeRep -> pure someTypeRep
      IFun a b -> do
        a' <- go a
        b' <- go b
        case (a', b') of
          (StarTypeRep aRep, StarTypeRep bRep) ->
            pure $ StarTypeRep (Type.Fun aRep bRep)
          _ -> Left ZonkKindError
      IApp f a -> do
        f' <- go f
        a' <- go a
        case applyTypes f' a' of
          Just someTypeRep -> pure someTypeRep
          _ -> Left ZonkKindError

-- | Convert from a type-indexed type to an untyped type.
fromSomeStarType :: forall void. SomeStarType -> IRep void
fromSomeStarType (SomeStarType r) = go r
  where
    go :: forall a. TypeRep a -> IRep void
    go = \case
      Type.Fun a b -> IFun (go a) (go b)
      Type.App a b -> IApp (go a) (go b)
      rep@Type.Con {} -> ICon (SomeTypeRep rep)
