module Counter where
import Prelude.Linear                           (String)
import YulDSL.Core                              (ADDR, NP, REF, U256 )
import  YulDSL.Core.YulCat (YulO1)
import YulDSL.Haskell.Effects.LinearSMC.YulPort (P'P, extendType'l, lfn', keccak256'l )


-- | Get a storage reference from the storage hash-map.
getCounterRef' :: forall b r.
  ( YulO1 b
  , YulO1 r
  -- , YulO1 (REF b)
  ) =>
  P'P r (NP '[ADDR]) ⊸ P'P r (REF b)
getCounterRef' a = extendType'l (keccak256'l a)

object :: String
object = lfn' @(REF U256) getCounterRef'
