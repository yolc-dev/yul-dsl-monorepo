module Counter where
import Control.LinearlyVersionedMonad            qualified as LVM
import Prelude.Linear                            (fromString, ($))
import YulDSL.Core
    ( ADDR
    , REF
    , U256
    , YulCat (YulSGet)
    , YulO1
    , mkYulObject
    , staticFn
    , yulNoop
    )
import YulDSL.Haskell.Effects.LinearSMC.LinearFn (StaticFn)
import YulDSL.Haskell.Effects.LinearSMC.Storage  (SReferenceable)
import YulDSL.Haskell.Effects.LinearSMC.YulMonad (YulMonad, ypure, yulmonad'p)
import YulDSL.Haskell.Effects.LinearSMC.YulPort
    ( P'P
    , P'V
    , P'x
    , PortEffect (PurePort)
    , Versionable'L
    , encodeP'x
    , reduceType'l
    , ver'l
    )
import YulDSL.Haskell.LibLinearSMC               (embed, extendType'l, keccak256'l, lfn', merge'l)


-- base
import GHC.TypeLits                              (KnownNat)
-- linear-base
import Prelude.Linear                            (fromInteger)


-- constraints
import Data.Constraint                           hiding ((\\))
import Data.Constraint.Nat                       (leTrans)
-- linear-base
import Prelude.Linear                            (flip)
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

lvmMap :: forall ctx va vb a b.
  (KnownNat va, KnownNat vb) =>
  (a ⊸ b) %1 -> LVM.LVM ctx va vb a ⊸ LVM.LVM ctx va vb b
lvmMap f ma = LVM.MkLVM \ctx -> let !(aleb, ctx', a) = LVM.unLVM ma ctx
                                    !a' = f a
                                in  (aleb, ctx', a')


-- | A Storage Hash-Map (SHMap) with a U256 root-key.
newtype SHMap b = SHMap U256

sget' :: ( KnownNat v
         , YulO1 r
         , Versionable'L ie v
         ) => P'x ie r (REF U256) ⊸ YulMonad v v r (P'V v r U256)
sget' s = ypure (encodeP'x YulSGet (reduceType'l (ver'l s)))

-- | Get a storage reference from the storage hash-map.
shmapRef :: forall ie r b v.
  ( KnownNat v
  , YulO1 b
  , YulO1 r
  -- , YulO1 (REF b)
  ) =>
  SHMap b ->
  P'x ie r ADDR ⊸
  YulMonad v v r (P'x ie r (REF b))
shmapRef (SHMap key) a =
  lvmMap (\key' -> extendType'l (keccak256'l (merge'l (key', a)))) (embed key)


-- | Get a value from the storage hash-map.
shmapGet :: forall r v.
  ( YulO1 r
  , SReferenceable PurePort v r (REF U256) U256
  ) =>
  P'P r ADDR ⊸
  YulMonad v v r (P'V v r U256)
shmapGet a = lvmBind (shmapRef (SHMap (fromInteger 10) :: SHMap U256) a) sget'

getCounter :: StaticFn (ADDR -> U256)
getCounter = lfn' "test" $ yulmonad'p shmapGet


object = mkYulObject "Counter" yulNoop
  [ staticFn "getCounter" getCounter
  ]
