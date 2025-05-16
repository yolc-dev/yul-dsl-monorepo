{-# LANGUAGE UndecidableInstances #-}
module YulDSL.Haskell.Data.SMap
  ( SMap, makeSMap
  , MagicHashMapReader ((#->))
  ) where
-- base
import GHC.TypeLits                       (type (+), type (<=))
-- yul-dsl
import YulDSL.Core
--
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import YulDSL.Haskell.LibLinearSMC


newtype HMapNP as b = MkHMapNP
  (forall v r {a'} {as'}. ((a':as') ~ as, YulO3 a' b r) => P'V v r a' ⊸ P'V v r B32)

type SMap path = HMapNP (UncurryNP'Fst path) (UncurryNP'Snd path)

makeSMap :: forall path a as b.
  ( EquivalentNPOfFunction path (a:as) b
  , SMap path ~ HMapNP (a:as) b
  ) =>
  String -> SMap path
makeSMap key = MkHMapNP \a ->
  let !(a', u) = mkunit'l a
      key' = emb'l (fromInteger (bytesnToInteger (stringKeccak256 key)) :: U256) u
      bslot = extendType'l (keccak256'l (merge'l (key', a')))
  in bslot

class MagicHashMapReader hmap vref_a result v r | hmap vref_a v r -> result where
  (#->) :: forall.
    (KnownNat v, v <= v + 1 , YulO1 r) =>
    hmap -> vref_a -> YLVM v v r result

instance ( YulO2 a b
         , YulVarRef v r (P'x ie r) ref_a_
         , VersionableYulVarRef v r a (ref_a_ a)
         ) =>
         MagicHashMapReader
         (YLVM v v r (Ur (HMapNP '[a] b)))
         (ref_a_ a)
         (Ur (Rv v r (REF b)))
         v r where
  mhmap #-> aVar = mhmap LVM.>>= \(Ur hmap) -> hmap #-> aVar

instance ( YulO2 a b
         , YulVarRef v r (P'x ie r) ref_a_
         , VersionableYulVarRef v r a (ref_a_ a)
         ) =>
         MagicHashMapReader
         (HMapNP (a:a':as') b)
         (ref_a_ a)
         (Ur (HMapNP (a':as') b))
         v r where
  -- (MkHMapNP h) #-> aVar = ytkvarv aVar LVM.>>= \a -> LVM.pure $ Ur $ MkHMapNP \a' ->
  --   let key = h @v @r a
  --       bslot = extendType'l (keccak256'l (merge'l (key, a')))
  --   in bslot
    -- g (h (\key_a -> extendType'l (keccak256'l (merge'l (key_a, a')))) a)

instance ( YulO2 a b
         , YulVarRef v r (P'x ie r) ref_a_
         , VersionableYulVarRef v r a (ref_a_ a)
         ) =>
         MagicHashMapReader
         (HMapNP '[a] b)
         (ref_a_ a)
         (Ur (Rv v r (REF b)))
         v r where
  (MkHMapNP h) #-> aVar = ytkvarv aVar LVM.>>= ymkvar . extendType'l . h
