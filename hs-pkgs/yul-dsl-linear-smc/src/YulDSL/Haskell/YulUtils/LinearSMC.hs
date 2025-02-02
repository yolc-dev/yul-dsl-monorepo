{-# LANGUAGE FunctionalDependencies #-}
module YulDSL.Haskell.YulUtils.LinearSMC
  ( yulKeccak256'l
  , yulCaller'l
    -- $PatternMatching
  , match'l
  ) where
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
import YulDSL.Haskell.YulUtils.Pure
import YulDSL.StdBuiltIns.ABICodec                   ()
--
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YulPort


yulKeccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
yulKeccak256'l = encode'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))

yulCaller'l :: forall r eff. YulO1 r => P'x eff r () ⊸ P'x eff r ADDR
yulCaller'l = encode'x YulCaller

------------------------------------------------------------------------------------------------------------------------
-- $PatternMatching
------------------------------------------------------------------------------------------------------------------------

-- | Provide necessary injectivity for the match function.
class MatchableOutputPortEffect (ioe :: PortEffect) (eff :: k) | ioe -> eff
instance MatchableOutputPortEffect (VersionedPort v) (VersionedInputOutput 0)
instance MatchableOutputPortEffect PurePort Pure

-- | Pattern match a yul port and outputs another yul port.
match'l :: forall p c b r m eff ioe.
  ( YulO3 r p b
  , YulCat eff p ~ m
  , MatchableOutputPortEffect ioe eff
  , PatternMatchable m YulCatObj p c
  , EncodableYulPortDiagram eff ioe ioe
  ) => P'x ioe r p ⊸ (c -> m b) -> P'x ioe r b
match'l p f = let mb = match (YulId :: YulCat eff p p) f in encodeWith'l id mb p
