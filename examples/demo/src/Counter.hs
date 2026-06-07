module Counter where
import YulDSL.Core ( bytesnToInteger, stringKeccak256
                   , staticFn, mkYulObject
                   , yulNoop, ADDR, U256
                   , YulO1, REF)
import Prelude.Linear (fromString, ($))
import Control.LinearlyVersionedMonad qualified as LVM
import YulDSL.Haskell.LibLinearSMC (lfn, keccak256'l, embed, merge'l, extendType'l)
import YulDSL.Haskell.Effects.LinearSMC.YulPort (P'x, P'V)
import YulDSL.Haskell.Effects.LinearSMC.YulMonad (YulMonad, yulmonad'p)
import YulDSL.Haskell.Effects.LinearSMC.LinearFn (StaticFn)
import YulDSL.Haskell.Effects.LinearSMC.Storage (SReferenceable, sget, sput)


-- base
import GHC.TypeLits                   (KnownNat)
-- linear-base
import Prelude.Linear                 (String, fromInteger, undefined)


-- constraints
import Data.Constraint hiding ((\\))
import Data.Constraint.Nat    (leTrans)
-- deepseq
import Control.DeepSeq (rnf)
-- linear-base
import Prelude.Linear  (Consumable (consume), flip)
import Unsafe.Linear   qualified as UnsafeLinear


-- Linear version of (\\) for internal use.
(\\) :: HasDict c e => (c => r) ⊸ e ⊸ r
(\\) = flip (UnsafeLinear.toLinear2 (withDict))
infixl 1 \\





lvmBind :: forall ctx va vb vc a b.
  (KnownNat va, KnownNat vb, KnownNat vc) =>
  LVM.LVM ctx va vb a ⊸ (a ⊸ LVM.LVM ctx vb vc b) ⊸ LVM.LVM ctx va vc b
ma `lvmBind` f = LVM.MkLVM \ctx -> let !(aleb, ctx', a) = LVM.unLVM ma ctx
                                       !(blec, ctx'', a') = LVM.unLVM (f a) ctx'
                                   in  (Dict \\ leTrans @va @vb @vc \\ aleb \\ blec, ctx'', a')



-- | A Storage Hash-Map (SHMap) with a U256 root-key.
newtype SHMap a b = SHMap U256

-- | Create a storage hash-map with a root-key represented by a string.
shmap :: forall s a b. s ~ (a -> b) => String -> SHMap a b
shmap key = SHMap (fromInteger (bytesnToInteger (stringKeccak256 key)))

-- | Get a storage reference from the storage hash-map.
shmapRef :: forall a b ie r v.
  ( KnownNat v
  , YulO1 r
  , YulO1 a
  , YulO1 b
  ) =>
  SHMap a b ->
  P'x ie r a ⊸
  YulMonad v v r (P'x ie r (REF b))
shmapRef (SHMap key) a =
  lvmBind (embed key) \key' ->
      LVM.pure (extendType'l (keccak256'l (merge'l (key', a))))

-- | Get a value from the storage hash-map.
shmapGet :: forall a b ie r v.
  ( YulO1 r
  , YulO1 a
  , YulO1 b
  , SReferenceable ie v r (REF b) b
  ) =>
  SHMap a b ->
  P'x ie r a ⊸
  YulMonad v v r (P'V v r b)
shmapGet m a = shmapRef m a `lvmBind` sget


object = mkYulObject "Counter" yulNoop
  [ staticFn "getCounter" getCounter
  ]

-- | Storage map of user counters
counterMap :: SHMap ADDR U256
counterMap = shmap "Yolc.Demo.Counter.Storage.Counter.PerUser"

getCounter :: StaticFn (ADDR -> U256)
getCounter = $lfn $ yulmonad'p
  \acc -> counterMap `shmapGet` acc
