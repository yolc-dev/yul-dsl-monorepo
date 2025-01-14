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
  , compileCatWithConfig
  , compileCat
  , compileFn
  , compileYulObject
  ) where
-- CodeGenUtils
import CodeGenUtils.CodeFormatters              (Code, init_ind)
--
import YulDSL.Core                              (NamedYulCat, YulCat, YulO2, YulObject)
--
import YulDSL.CodeGens.Yul.Internal.CodeGen     (CodeGenConfig (..), cg_create_vars, gen_code)
import YulDSL.CodeGens.Yul.Internal.FunctionGen (compile_cat, compile_named_cat)
import YulDSL.CodeGens.Yul.Internal.ObjectGen   (compile_object)


defaultCodeGenConfig :: CodeGenConfig
defaultCodeGenConfig = MkCodeGenConfig { cg_config_debug_level = 1 }

-- | Compiling a unamed yul function
compileCatWithConfig :: forall eff a b. YulO2 a b => CodeGenConfig -> YulCat eff a b -> Code
compileCatWithConfig config cat = gen_code config $ do
  vars_a <- cg_create_vars @a
  vars_b <- cg_create_vars @b
  compile_cat init_ind cat (vars_a, vars_b)

compileCat :: forall eff a b. YulO2 a b => YulCat eff a b -> Code
compileCat cat = compileCatWithConfig defaultCodeGenConfig cat

-- | Compiling a named yul function.
compileFn :: forall eff a b. YulO2 a b => NamedYulCat eff a b -> Code
compileFn fn = gen_code defaultCodeGenConfig $ do
  compile_named_cat init_ind fn

-- | Compiling the yul object.
compileYulObject :: YulObject -> Code
compileYulObject obj = gen_code defaultCodeGenConfig $ do
  compile_object init_ind obj
