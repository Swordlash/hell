module Spec where

import Test.Hspec
import qualified Language.Haskell.Exts as HSE

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

freeVariablesSpec :: Spec
freeVariablesSpec = do
  it "freeVariables" $ shouldBe (try "\\z -> Main.x * Z.y") ["x"]
  where
    try e = case freeVariables <$> HSE.parseExp e of
      HSE.ParseOk names -> names
      _ -> error "Parse failed."


desugarTypeSpec :: Spec
desugarTypeSpec = do
  it "desugarType" $ do
    shouldBe (try "Bool") (Right (SomeStarType $ typeRep @Bool))
    shouldBe (try "Int") (Right (SomeStarType $ typeRep @Int))
    shouldBe (try "Bool -> Int") (Right (SomeStarType $ typeRep @(Bool -> Int)))
    shouldBe (try "()") (Right (SomeStarType $ typeRep @()))
    shouldBe (try "[Int]") (Right (SomeStarType $ typeRep @[Int]))
  where
    try e = case desugarType <$> HSE.parseType e of
      HSE.ParseOk r -> r
      _ -> error "Parse failed."

--------------------------------------------------------------------------------
-- Spec

main :: Spec
main = do
  freeVariablesSpec
  anyCyclesSpec
  desugarTypeSpec
