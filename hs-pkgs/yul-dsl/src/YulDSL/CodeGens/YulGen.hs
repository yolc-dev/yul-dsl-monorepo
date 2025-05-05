{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

Generate solidity/yul code for Fn, YulCat, and YulObject.

-}

module YulDSL.CodeGens.YulGen
  ( Code
  , CodeGenConfig (..), defaultCodeGenConfig
  , compileCat
  , compileFn
  , compileYulObject
  ) where
-- CodeGenUtils
import CodeGenUtils.CodeFormatters              (Code, init_ind)
--
import YulDSL.Core                              (NamedYulCat, YulCat, YulO2, YulObject)
--
import YulDSL.CodeGens.Yul.Internal.CodeGen     (CodeGenConfig (..), cg_create_vars, cg_run)
import YulDSL.CodeGens.Yul.Internal.FunctionGen (compile_cat, compile_named_cat)
import YulDSL.CodeGens.Yul.Internal.ObjectGen   (compile_object)


defaultCodeGenConfig :: CodeGenConfig
defaultCodeGenConfig = MkCodeGenConfig
  { cg_config_debug_level = 1
  , cg_config_dummy = True
  }

compileCat :: forall eff a b. YulO2 a b => CodeGenConfig -> YulCat eff a b -> Code
compileCat config cat =  cg_run config $ do
  vars_a <- cg_create_vars @a
  vars_b <- cg_create_vars @b
  compile_cat init_ind cat (vars_a, vars_b)

-- | Compiling a named yul function.
compileFn :: forall eff a b. YulO2 a b => CodeGenConfig -> NamedYulCat eff a b -> Code
compileFn config fn = cg_run config $ do
  compile_named_cat init_ind fn

-- | Compiling the yul object.
compileYulObject :: CodeGenConfig -> YulObject -> Code
compileYulObject config obj = cg_run config $ do
  compile_object init_ind obj
