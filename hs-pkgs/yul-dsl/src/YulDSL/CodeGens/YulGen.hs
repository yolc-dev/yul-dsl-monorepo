{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

Generate solidity/yul code for Fn, YulCat, and YulObject.

-}

module YulDSL.CodeGens.YulGen
  ( compileFn
  , compileYulObject
  ) where
-- CodeGenUtils
import CodeGenUtils.CodeFormatters              (Code, init_ind)
--
import YulDSL.Core                              (NamedYulCat, YulO2, YulObject)
--
import YulDSL.CodeGens.Yul.Internal.CodeGen     (gen_code)
import YulDSL.CodeGens.Yul.Internal.FunctionGen (compile_named_cat)
import YulDSL.CodeGens.Yul.Internal.ObjectGen   (compile_object)


-- | Compiling a yul function.
compileFn :: forall eff a b. YulO2 a b => NamedYulCat eff a b -> Code
compileFn fn = gen_code $ do
  compile_named_cat init_ind fn

-- | Compiling the yul object.
compileYulObject :: YulObject -> Code
compileYulObject obj = gen_code $ do
  compile_object init_ind obj
