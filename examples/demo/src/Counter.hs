module Counter where
import Prelude.Linear                           (fromString)
import YulDSL.Core                              (ADDR, NP, REF, U256, YulO1, mkYulObject, pureFn, yulNoop)
import YulDSL.Haskell.Effects.LinearSMC.YulPort (P'P, extendType'l )
import YulDSL.Haskell.Effects.LinearSMC.LinearFn (lfn')
import YulDSL.Haskell.Effects.Pure              (PureFn)
import YulDSL.Haskell.LibLinearSMC              (keccak256'l)


-- | Get a storage reference from the storage hash-map.
getCounterRef' :: forall b r.
  ( YulO1 b
  , YulO1 r
  -- , YulO1 (REF b)
  ) =>
  P'P r (NP '[ADDR]) ⊸ P'P r (REF b)
getCounterRef' a = extendType'l (keccak256'l a)

getCounterRef :: PureFn (ADDR -> REF U256)
getCounterRef = lfn' "getRef" getCounterRef'

object = mkYulObject "Counter" yulNoop
  [ pureFn "getCounterRef" getCounterRef
  ]
