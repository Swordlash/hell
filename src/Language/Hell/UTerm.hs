module Language.Hell.UTerm where

-- Things used within the host language.

import GHC.Types
import qualified Language.Haskell.TH.Syntax as TH
import Language.Hell.IRep
import Language.Hell.Term
import Type.Reflection (TypeRep)
import qualified Type.Reflection as Type

--------------------------------------------------------------------------------
-- The "untyped" AST
--
-- This is the AST that is not interpreted, and is just
-- type-checked. The HSE AST is desugared into this one.

data UTerm t
  = UVar t String
  | ULam t Binding (Maybe SomeStarType) (UTerm t)
  | UApp t (UTerm t) (UTerm t)
  | -- IRep below: The variables are poly types, they aren't metavars,
    -- and need to be instantiated.
    UForall t [SomeStarType] Forall [TH.Uniq] (IRep TH.Uniq) [t]
  deriving (Traversable, Functor, Foldable)

typeOf :: UTerm t -> t
typeOf = \case
  UVar t _ -> t
  ULam t _ _ _ -> t
  UApp t _ _ -> t
  UForall t _ _ _ _ _ -> t

data Binding = Singleton String | Tuple [String]

data Forall where
  NoClass :: (forall (a :: Type). TypeRep a -> Forall) -> Forall
  OrdEqShow :: (forall (a :: Type). (Ord a, Eq a, Show a) => TypeRep a -> Forall) -> Forall
  Monadic :: (forall (m :: Type -> Type). (Monad m) => TypeRep m -> Forall) -> Forall
  Final :: (forall g. Typed (Term g)) -> Forall

lit :: (Type.Typeable a) => a -> UTerm ()
lit l = UForall () [] (Final (Typed (Type.typeOf l) (Lit l))) [] (fromSomeStarType (SomeStarType (Type.typeOf l))) []
