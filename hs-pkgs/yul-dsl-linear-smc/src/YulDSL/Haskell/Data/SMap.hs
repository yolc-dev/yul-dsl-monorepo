{-# LANGUAGE UndecidableInstances #-}
module YulDSL.Haskell.Data.SMap
  ( SMap, makeSMap
  , SMapMagicHashReader ((#->))
  ) where
-- base
import Data.Kind                          (Type)
-- yul-dsl
import YulDSL.Core
--
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import YulDSL.Haskell.LibLinearSMC


type SMap path = SMap' (UncurryNP'Fst path) (UncurryNP'Snd path)

type SMap' :: [Type] -> Type -> Type
newtype SMap' as b = MkSMap B32
type role SMap' nominal nominal

makeSMap :: forall path as b.
  ( EquivalentNPOfFunction path as b
  , SMap path ~ SMap' as b
  ) =>
  String -> SMap path
makeSMap key = MkSMap (stringKeccak256 key)

class SMapMagicHashReader p q b v r | p -> b where
  (#->) :: forall. (KnownNat v, YulO2 b r) => p -> q -> YLVM v v r (Ur (Rv v r (REF b)))

instance ( YulO1 a
         , YulVarRef v r (P'x ioe r) vref_a_
         ) =>
         SMapMagicHashReader
         (SMap' '[a] b)
         (vref_a_ a)
         b v r where
  (MkSMap key) #-> aVar = LVM.do
    a <- yrtakev aVar
    let !(a', u) = mkunit'l a
    let key1 = keccak256'l (merge'l (emb'l key u, a'))
    ymakev (extendType'l key1)

-- TODO, inductive implementation

instance ( YulO2 a1 a2
         , YulVarRef v r (P'x ioe r) vref_a1_
         , YulVarRef v r (P'x ioe r) vref_a2_
         ) =>
         SMapMagicHashReader
         (SMap' '[a1, a2] b)
         (vref_a1_ a1, vref_a2_ a2)
         b v r where
  (MkSMap key) #-> (a1Var, a2Var) = LVM.do
    a1 <- yrtakev a1Var
    let !(a1', u) = mkunit'l a1
    let key1 = keccak256'l (merge'l (emb'l key u, a1'))

    a2 <- yrtakev a2Var
    let key2 = keccak256'l (merge'l (key1, a2))

    ymakev (extendType'l key2)

instance ( YulO3 a1 a2 a3
         , YulVarRef v r (P'x ioe r) vref_a1_
         , YulVarRef v r (P'x ioe r) vref_a2_
         , YulVarRef v r (P'x ioe r) vref_a3_
         ) =>
         SMapMagicHashReader
         (SMap' '[a1, a2, a3] b)
         (vref_a1_ a1, vref_a2_ a2, vref_a3_ a3)
         b v r where
  (MkSMap key) #-> (a1Var, a2Var, a3Var) = LVM.do
    a1 <- yrtakev a1Var
    let !(a1', u) = mkunit'l a1
    let key1 = keccak256'l (merge'l (emb'l key u, a1'))

    a2 <- yrtakev a2Var
    let key2 = keccak256'l (merge'l (key1, a2))

    a3 <- yrtakev a3Var
    let key3 = keccak256'l (merge'l (key2, a3))

    ymakev (extendType'l key3)
