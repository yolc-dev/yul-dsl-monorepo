{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module YulDSL.Haskell.Lib
  -- * YulDSL/Haskell's pure effect support
  ( module YulDSL.Haskell.Effects.Pure
  -- * YulDSL/Haskell Lib
  , module YulDSL.Haskell.Lib.PureFn
  , module YulDSL.Haskell.Lib.TH
  , module YulDSL.Haskell.YulCatObj.NP
  -- ** Extra YulCat Helpers
  , yulKeccak256
  , yulRevert
  , emptyCtor
  -- * Control Flow Extensions
  , module Control.IfThenElse
  , module Control.PatternMatchable
  ) where
-- eth-abi
import Ethereum.ContractABI
-- (data-control-extra)
import Control.IfThenElse
import Control.PatternMatchable
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec     ()
import YulDSL.StdBuiltIns.Exception    ()
import YulDSL.StdBuiltIns.ValueType    ()
--
import YulDSL.Haskell.YulCatObj.Maybe  ()
import YulDSL.Haskell.YulCatObj.NP
import YulDSL.Haskell.YulCatObj.TUPLEn ()
--
import YulDSL.Haskell.Effects.Pure
--
import YulDSL.Haskell.Lib.Instances    ()
import YulDSL.Haskell.Lib.PureFn
import YulDSL.Haskell.Lib.TH


-- | Revert without any message.
yulRevert :: forall eff a b. (YulO2 a b) => YulCat eff a b
yulRevert = YulDis >.> YulJmpB (MkYulBuiltIn @"__const_revert0_c_" @() @b)

-- | Wrapper for built-in keccak256 yul function.
yulKeccak256 :: forall eff a r. YulO2 r a => YulCat eff r a -> YulCat eff r B32
yulKeccak256 x = x >.> YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32)

-- | Empty object constructor.
emptyCtor :: AnyYulCat
emptyCtor = MkAnyYulCat (YulDis @Pure @())
