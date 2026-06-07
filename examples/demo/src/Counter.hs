module Counter where
import Control.LinearlyVersionedMonad            qualified as LVM
import Prelude.Linear                            (fromString, ($))
import YulDSL.Core                               (ADDR, REF, U256, YulO1, mkYulObject, staticFn, yulNoop)
import YulDSL.Haskell.Effects.LinearSMC.LinearFn (StaticFn)
import YulDSL.Haskell.Effects.LinearSMC.Storage  (SReferenceable, sget, sput)
import YulDSL.Haskell.Effects.LinearSMC.YulMonad (YulMonad, yulmonad'p)
import YulDSL.Haskell.Effects.LinearSMC.YulPort  (P'V, P'x)
import YulDSL.Haskell.LibLinearSMC               (embed, extendType'l, keccak256'l, lfn', merge'l)


-- base
import GHC.TypeLits                              (KnownNat, type (+))
-- linear-base
import Prelude.Linear                            (String, fromInteger, undefined)


-- constraints
import Data.Constraint                           hiding ((\\))
import Data.Constraint.Nat                       (leTrans)
-- deepseq
import Control.DeepSeq                           (rnf)
-- linear-base
import Prelude.Linear                            (Consumable (consume), flip)
import Unsafe.Linear                             qualified as UnsafeLinear


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

-- | Get a storage reference from the storage hash-map.
shmapRef :: forall ie r b v.
  ( KnownNat v
  , YulO1 b
  , YulO1 r
  -- , YulO1 (REF b)
  ) =>
  SHMap ADDR b ->
  P'x ie r ADDR ⊸
  YulMonad v v r (P'x ie r (REF b))
shmapRef (SHMap key) a =
  lvmBind (embed key) \key' -> LVM.pure (extendType'l (keccak256'l (merge'l (key', a))))

-- | Get a value from the storage hash-map.
shmapGet :: forall ie r v.
  ( YulO1 r
  , SReferenceable ie v r (REF U256) U256
  ) =>
  SHMap ADDR U256 ->
  P'x ie r ADDR ⊸
  YulMonad v v r (P'V v r U256)
shmapGet m@(SHMap key) a =
  lvmBind
    (shmapRef m a)
    sget

getCounter :: StaticFn (ADDR -> U256)
getCounter = lfn' "asdfasdf" $ yulmonad'p f

f :: ( KnownNat v
     , YulO1 r
     , SReferenceable ie v r (REF U256) U256
     ) => P'x ie r ADDR %1 -> YulMonad v v r (P'V v r U256)
f = \acc -> SHMap (fromInteger 10) `shmapGet` acc


object = mkYulObject "Counter" yulNoop
  [ staticFn "getCounter" getCounter
  ]
