{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module provides yul monads that work with contract storage.

-}
module YulDSL.Haskell.Effects.LinearSMC.Storage
  ( SReferenceable (sget'l, sput'l)
  , sget, SGettableNP (sgetNP), sgetN
  , StorageAssignment ((:=)), NonEmpty ((:|))
  , sput, sputs
  -- , sgets
  ) where
-- base
import Data.List.NonEmpty                       (NonEmpty ((:|)))
import GHC.TypeLits                             (type (+), type (<=))
-- linear-base
import Prelude.Linear                           (Ur (Ur), type (~), ($), (.))
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad.LVM       qualified as LVM
--
import YulDSL.Haskell.Effects.LinearSMC.YLVM
import YulDSL.Haskell.Effects.LinearSMC.YulPort


class (KnownNat v, YulO3 a b r) => SReferenceable v r a b where
  sget'l :: forall. P'V v r a ⊸ P'V v r b
  sput'l :: forall. VersionThread r ⊸ P'V v r a ⊸ P'V v r b ⊸ (VersionThread r, P'V (v + 1) r ())

instance ( KnownNat v, v <= v + 1, YulO2 b r
         , ABIWordValue b
         ) => SReferenceable v r B32 b where
  sget'l s = encodeP'x YulSGet (ver'l s)
  sput'l vt s x =
    let !(x1, x2) = dup'l x
    in vtseq vt x1 (unsafeCoerceYulPort (encodeP'x YulSPut (merge'l (ver'l s, x2))))

instance ( KnownNat v, v <= v + 1, YulO2 a r
         , ABIWordValue a
         ) => SReferenceable v r (REF a) a where
  sget'l s = encodeP'x YulSGet (reduceType'l (ver'l s))
  sput'l vt s x =
    let !(x1, x2) = dup'l x
    in vtseq vt x1 (unsafeCoerceYulPort (encodeP'x YulSPut (merge'l (reduceType'l (ver'l s), x2))))

sget :: forall a b ie r v vref_.
  ( YulO3 r a b
  , YulVarRef v r (P'x ie r) vref_
  , ReferenciableYulVar v r (vref_ a)
  , DereferenceYulVarRef (vref_ a) ~ P'x ie r a
  , VersionableYulVarRef v r a (vref_ a)
  , SReferenceable v r a b
  ) =>
  vref_ a ⊸ YLVM v v r (Ur (Rv v r b))
sget avar = ytkvarv avar LVM.>>= ymkvar . sget'l

------------------------------------------------------------------------------------------------------------------------
-- sgetNP, sgetN, (<==)
------------------------------------------------------------------------------------------------------------------------

class (KnownNat v, YulO1 r) => SGettableNP v r np b where
  sgetNP :: forall. np ⊸ YLVM v v r b

instance (KnownNat v, YulO1 r) =>
         SGettableNP v r (NP '[]) (Ur (NP '[])) where
  sgetNP Nil = LVM.pure $ Ur Nil

instance ( YulO3 r a b
         , YulVarRef v r (P'x ie r) vref_
         , ReferenciableYulVar v r (vref_ a)
         , DereferenceYulVarRef (vref_ a) ~ P'x ie r a
         , VersionableYulVarRef v r a (vref_ a)
         , SReferenceable v r a b
         , SGettableNP v r (NP as) (Ur (NP bs))
         ) =>
         SGettableNP v r (NP (vref_ a : as)) (Ur (NP (Rv v r b : bs))) where
  sgetNP (a :* as) = LVM.do
    Ur b <- sget a
    Ur bs <- sgetNP as
    LVM.pure $ Ur (b :* bs)

sgetN :: forall tpl_a tpl_b v r.
  ( KnownNat v
  , ConvertibleTupleNtoNP tpl_a, ConvertibleTupleNtoNP tpl_b
  , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
  ) => tpl_a ⊸ YLVM v v r tpl_b
sgetN tpl_a = let np_a = fromTupleNtoNP tpl_a
                  np_b = sgetNP np_a :: YLVM v v r (TupleNtoNP tpl_b)
              in np_b LVM.>>= LVM.pure . fromNPtoTupleN

------------------------------------------------------------------------------------------------------------------------
-- sassign StorageAssignment; sputs NonEmpty StorageAssignment
------------------------------------------------------------------------------------------------------------------------

data StorageAssignment v r = forall a b iea ieb vref_a_ vref_b_.
  ( -- ref_a
    YulVarRef v r (P'x iea r) vref_a_
  , ReferenciableYulVar v r (vref_a_ a)
  , DereferenceYulVarRef (vref_a_ a) ~ P'x iea r a
  , VersionableYulVarRef v r a (vref_a_ a)
    -- ref_b
  , YulVarRef v r (P'x ieb r) vref_b_
  , ReferenciableYulVar v r (vref_b_ b)
  , DereferenceYulVarRef (vref_b_ b) ~ P'x ieb r b
  , VersionableYulVarRef v r b (vref_b_ b)
    -- b
  , SReferenceable v r a b
  ) =>
  YLVM v v r (Ur (vref_a_ a)) := vref_b_ b

sput :: forall v r.
  (KnownNat (v + 1), v <= v + 1, YulO1 r) =>
  StorageAssignment v r ⊸ YLVM v (v + 1) r ()
sput (aVarM := bVar) = LVM.do
  Ur aVar <- aVarM
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure ()

sputs :: forall v r.
  ( KnownNat v, KnownNat (v + 1), v <= v + 1, YulO1 r
  ) => NonEmpty (StorageAssignment v r) ⊸ YLVM v (v + 1) r ()
sputs (sa :| []) = sput sa
sputs (sa :| (sa':sas)) =
  let x  = sput sa            :: YLVM v (v + 1) r ()
      x' = LVM.unsafeCoerceLVM x :: YLVM v      v  r ()
      xs = sputs (sa' :| sas)
  in x' LVM.>> xs
