module YulDSL.Haskell.Data.SHMap
  ( SHMap (SHMap), shmap
  , shmapRef'l, shmapGet'l, shmapPut'l
  , shmapRef, (.->), shmapGet
  ) where
-- base
import GHC.TypeLits                       (KnownNat, type (+), type (<=))
-- yul-dsl
import YulDSL.Core
--
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import YulDSL.Haskell.LibLinearSMC


-- | A Storage Hash-Map (SHMap) with a U256 root-key.
newtype SHMap a b = SHMap U256

-- | Create a storage hash-map with a root-key represented by a string.
shmap :: forall sig a b. sig ~ (a -> b) => String -> SHMap a b
shmap key = SHMap (fromInteger (bytesnToInteger (stringKeccak256 key)))

-- | Get a storage reference from the storage hash-map.
shmapRef'l :: forall a b ie r.
  YulO4 r a b (REF b) =>
  SHMap a b ->
  P'x ie r a ⊸
  P'x ie r (REF b)
shmapRef'l (SHMap key) a =
  let !(a1, a2) = dup'l a
      key' = emb'l key a2
      bslot = extendType'l (keccak256'l (merge'l (key', a1)))
  in bslot

-- | Get a value from the storage hash-map.
shmapGet'l :: forall a b r v.
  ( YulO3 r a b
  , SReferenceable v r (REF b) b
  ) =>
  SHMap a b ->
  P'V v r a ⊸
  P'V v r b
shmapGet'l hmp a = let bslot = shmapRef'l hmp a in sget'l bslot

-- | Get a value from the storage hash-map.
shmapPut'l :: forall a b ie r v.
  ( KnownNat v, v <= v + 1, YulO3 r a b
  , VersionableYulPort ie v
  , SReferenceable v r (REF b) b
  ) =>
  SHMap a b ->
  VersionThread r ⊸
  P'x ie r a ⊸
  P'V v r b ⊸
  (VersionThread r, P'V (v + 1) r ())
shmapPut'l hmp vt a b = let bslot = shmapRef'l hmp a in sput'l vt (ver'l bslot) b

-- | Get a storage reference from the storage hash-map.
(.->), shmapRef :: forall a b ie r v ref_a xref_.
  ( YulO4 a b (REF b) r
  , ReferenciableYulVar v r ref_a
  , DereferenceYulVarRef ref_a ~ P'x ie r a
  , DereferenceXv (xref_ (REF b)) ~ P'x ie r (REF b)
  , MakeableYulVarRef v r (P'x ie r) xref_
  ) =>
  SHMap a b ->
  ref_a ->
  YLVM v v r (xref_ (REF b))
shmapRef hmp avar = ytake1 avar LVM.>>= ymkref . shmapRef'l hmp
(.->) = shmapRef

-- | Get a value from the storage hash-map.
shmapGet :: forall a b ie r v ref_a.
  ( YulO3 r a b
  , ReferenciableYulVar v r ref_a
  , DereferenceYulVarRef ref_a ~ P'x ie r a
  , LinearlyVersionRestrictedYulPort v r (P'x ie r a) ~ P'V v r a
  , SReferenceable v r (REF b) b
  ) =>
  SHMap a b ->
  ref_a ->
  YLVM v v r (Rv v r b)
shmapGet hmp avar = ytakev1 avar LVM.>>= ymkref . shmapGet'l hmp

-- -- | Get a value from the storage hash-map.
-- shmapPut :: forall a b iea ieb r v ref_a ref_b.
--   ( KnownNat (v + 1), v <= v + 1, YulO3 r a b
--   , ReferenciableYulVar v r ref_a
--   , DereferenceYulVarRef ref_a ~ P'x iea r a
--   , VersionableYulPort iea v
--   -- ref_b
--   , ReferenciableYulVar v r ref_b
--   , DereferenceYulVarRef ref_b ~ P'x ieb r b
--   , LinearlyVersionRestrictedYulPort v r (P'x ieb r b) ~ P'V v r b
--   -- b
--   , SReferenceable v r (REF b) b
--   , ABIWordValue b -- FIXME
--   ) =>
--   SHMap a b ->
--   ref_a ->
--   ref_b ->
--   YLVM v (v + 1) r ()
-- shmapPut hmp avar bvar = LVM.do
--   a <- ytake1 avar
--   b <- ytakev1 bvar
--   u <- yrunvt (\vt -> shmapPut'l hmp vt a b)
--   ygulp u
