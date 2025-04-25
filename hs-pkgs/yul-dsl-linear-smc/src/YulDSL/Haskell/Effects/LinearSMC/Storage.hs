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
  ( SReferenceable (sget'l, sput'l), sget, sput
  , SGettableNP (sgetNP), sgetN
  , SPuttableNP (sputNP), sputN
  , StorageAssignment ((:=)), NonEmpty ((:|))
  , sputs_1, sputs
  -- , sgets
  ) where
-- base
import Data.List.NonEmpty                       (NonEmpty ((:|)))
import GHC.TypeLits                             (KnownNat, type (+), type (<=))
-- constraints
import Data.Constraint.Unsafe                   (unsafeAxiom)
-- linear-base
import Prelude.Linear                           (type (~), (.))
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad.LVM       (LVM (MkLVM))
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

sget :: forall a b ie r v ref_a.
  ( YulO3 r a b
  , VersionableYulPort ie v
  , ReferenciableYulVar v r ref_a
  , DereferenceYulVarRef ref_a ~ P'x ie r a
  , SReferenceable v r a b
  ) =>
  ref_a ⊸ YLVM v v r (Rv v r b)
sget avar = ytake1 avar LVM.>>= ymkref . sget'l . ver'l

sput :: forall a b iea ieb r v ref_a ref_b.
  ( KnownNat (v + 1), v <= v + 1, YulO3 r a b
  -- ref_a
  , VersionableYulPort iea v
  , ReferenciableYulVar v r ref_a
  , DereferenceYulVarRef ref_a ~ P'x iea r a
  , LinearlyVersionRestrictedYulPort v r (P'x iea r a) ~ P'V v r a
  -- ref_b
  , ReferenciableYulVar v r ref_b
  , DereferenceYulVarRef ref_b ~ P'x ieb r b
  , LinearlyVersionRestrictedYulPort v r (P'x ieb r b) ~ P'V v r b
  -- b
  , SReferenceable v r a b
  ) =>
  ref_a ⊸ ref_b ⊸ YLVM v (v + 1) r ()
sput avar bvar = LVM.do
  a <- ytakev1 avar
  b <- ytakev1 bvar
  u <- yrunvt (\vt -> sput'l vt a b)
  ygulp u

------------------------------------------------------------------------------------------------------------------------
-- sgetNP, sgetN, (<==)
------------------------------------------------------------------------------------------------------------------------

class (KnownNat v, YulO1 r) => SGettableNP v r a b where
  sgetNP :: forall. a ⊸ YLVM v v r b

instance (KnownNat v, YulO1 r) => SGettableNP v r (NP '[]) (NP '[]) where
  sgetNP Nil = LVM.pure Nil

instance ( YulO3 r a b
         , VersionableYulPort ie v
         , ReferenciableYulVar v r ref_a
         , DereferenceYulVarRef ref_a ~ P'x ie r a
         , SReferenceable v r a b
         , SGettableNP v r (NP as) (NP bs)
         ) => SGettableNP v r (NP (ref_a : as)) (NP (Rv v r b : bs)) where
  sgetNP (a :* as) = LVM.do
    b <- sget a
    bs <- sgetNP as
    LVM.pure (b :* bs)

sgetN :: forall tpl_a tpl_b v r.
  ( KnownNat v
  , ConvertibleTupleNtoNP tpl_a, ConvertibleTupleNtoNP tpl_b
  , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
  ) => tpl_a ⊸ YLVM v v r tpl_b
sgetN tpl_a = let np_a = fromTupleNtoNP tpl_a
                  np_b = sgetNP np_a :: YLVM v v r (TupleNtoNP tpl_b)
              in np_b LVM.>>= LVM.pure . fromNPtoTupleN

------------------------------------------------------------------------------------------------------------------------
-- sputN
------------------------------------------------------------------------------------------------------------------------

class (KnownNat v, KnownNat (v + 1), YulO1 r) => SPuttableNP v r a where
  sputNP :: forall. a ⊸ YLVM v (v + 1) r ()

instance (KnownNat v, KnownNat (v + 1), YulO1 r) => SPuttableNP v r (NP '[]) where
  sputNP Nil = MkLVM (unsafeAxiom, , ())

instance ( KnownNat v, KnownNat (v + 1), v <= v + 1, YulO1 r
           -- ref_a
         , ReferenciableYulVar v r ref_a
         , DereferenceYulVarRef ref_a ~ P'x iea r a
         , VersionableYulPort iea v
         , LinearlyVersionRestrictedYulPort v r (P'x iea r a) ~ P'V v r a
           -- ref_b
         , ReferenciableYulVar v r ref_b
         , DereferenceYulVarRef ref_b ~ P'x ieb r b
         , LinearlyVersionRestrictedYulPort v r (P'x ieb r b) ~ P'V v r b
         -- b
         , SReferenceable v r a b
         , SPuttableNP v r (NP xs)
         ) => SPuttableNP v r (NP ((ref_a, ref_b):xs)) where
  sputNP ((a, b) :* xs) = let x'  = sput a b               :: YLVM v (v + 1) r ()
                              x'' = LVM.unsafeCoerceLVM x' :: YLVM v      v  r ()
                              xs' = sputNP xs              :: YLVM v (v + 1) r ()
                          in x'' LVM.>> xs'

sputN :: forall tpl v r.
  ( ConvertibleTupleNtoNP tpl
  , SPuttableNP v r (TupleNtoNP tpl)
  ) =>
  tpl ⊸ YLVM v (v + 1) r ()
sputN tpl = sputNP (fromTupleNtoNP tpl)

------------------------------------------------------------------------------------------------------------------------
-- sassign StorageAssignment; sputs NonEmpty StorageAssignment
------------------------------------------------------------------------------------------------------------------------

data StorageAssignment v r = forall a b iea ieb xref_a_ ref_b.
  ( -- ref_a
    ReferenciableXv v r (xref_a_ a)
  , DereferenceXv (xref_a_ a) ~ P'x iea r a
  , VersionableYulPort iea v
  , UnwrappableXv v r (P'x iea r) xref_a_
--  , LinearlyVersionRestrictedYulPort v r (P'x iea r a) ~ P'V v r a
  -- ref_b
  , ReferenciableYulVar v r ref_b
  , DereferenceYulVarRef ref_b ~ P'x ieb r b
  , LinearlyVersionRestrictedYulPort v r (P'x ieb r b) ~ P'V v r b
    -- b
  , SReferenceable v r a b
  ) =>
  YLVM v v r (xref_a_ a) := ref_b
-- infix 5 :=

sputs_1 :: forall v r.
  (KnownNat (v + 1), v <= v + 1, YulO1 r) =>
  StorageAssignment v r ⊸ YLVM v (v + 1) r ()
sputs_1 (maxref := bvar) = LVM.do
  axref <- maxref
  a <- yunref axref
  b <- ytakev1 bvar
  yrunvt (\vt -> sput'l vt (ver'l a) b)
  LVM.pure ()

sputs :: forall v r.
  ( KnownNat v, KnownNat (v + 1), v <= v + 1, YulO1 r
  ) => NonEmpty (StorageAssignment v r) ⊸ YLVM v (v + 1) r ()
sputs (sa :| []) = sputs_1 sa
sputs (sa :| (sa':sas)) =
  let x  = sputs_1 sa            :: YLVM v (v + 1) r ()
      x' = LVM.unsafeCoerceLVM x :: YLVM v      v  r ()
      xs = sputs (sa' :| sas)
  in x' LVM.>> xs

-- (<==), sgets :: forall tpl_a tpl_b v r.
--   ( ConvertibleTupleNtoNP tpl_a, ConvertibleTupleNtoNP tpl_b
--   , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
--   ) => tpl_a ⊸ YLVM v v r tpl_b
-- sgets = sgetN
-- (<==) = sgetN
