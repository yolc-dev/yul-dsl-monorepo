module YulDSL.Haskell.YulUtils.LinearSMC
  ( -- * Yul Utilities For LinearSMC
    yulKeccak256'l
  --   -- * Type Operations
  --   -- $TypeOps
  --   , coerceType'l, reduceType'l, extendType'l, cons'l, uncons'l
  ) where
-- yul-dsl
import YulDSL.Core
import YulDSL.StdBuiltIns.ABICodec              ()
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort


yulKeccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
yulKeccak256'l = encode'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))
