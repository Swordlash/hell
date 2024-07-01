module Language.Hell.Parser where

import qualified Language.Haskell.Exts as HSE

--------------------------------------------------------------------------------
-- Get declarations from the module

parseModule :: HSE.Module HSE.SrcSpanInfo -> HSE.ParseResult [(String, HSE.Exp HSE.SrcSpanInfo)]
parseModule (HSE.Module _ Nothing [] [] decls) =
  traverse parseDecl decls
  where
    parseDecl (HSE.PatBind _ (HSE.PVar _ (HSE.Ident _ string)) (HSE.UnGuardedRhs _ exp') Nothing) =
      pure (string, exp')
    parseDecl _ = fail "Can't parse that!"
parseModule _ = fail "Module headers aren't supported."
