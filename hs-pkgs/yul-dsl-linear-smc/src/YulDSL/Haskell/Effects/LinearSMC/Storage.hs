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
  ( SReferenceable (sget, sput)
  , SGettableNP (sgetNP), sgetN, (<==)
  , SPuttableNP (sputNP), sputN
  , StorageAssignment ((:=)), NonEmpty ((:|)), sassign, sputs
  ) where
-- base
import Data.List.NonEmpty                       (NonEmpty ((:|)))
import GHC.TypeLits                             (KnownNat, type (+))
-- constraints
import Data.Constraint.Unsafe                   (unsafeAxiom)
-- linear-base
import Prelude.Linear                           ((&), (.))
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad.LVM       (LVM (MkLVM))
import Control.LinearlyVersionedMonad.LVM       qualified as LVM
import Data.LinearContext                       (contextualEmbed)
--
import YulDSL.Haskell.Effects.LinearSMC.YulLVM
import YulDSL.Haskell.Effects.LinearSMC.YulPort


class ( KnownNat v, KnownNat (v + 1)
      , YulO2 a b, VersionableYulPort ie v
      ) => SReferenceable ie v r a b where
  sget :: forall. YulO1 r => P'x ie r a ⊸ YulLVM v v r (P'V v r b)
  sput :: forall. YulO1 r => P'x ie r a ⊸ P'V v r b ⊸ YulLVM v (v + 1) r (P'V (v + 1) r ())

instance ( KnownNat v, KnownNat (v + 1)
         , YulO1 b, ABIWordValue b, VersionableYulPort ie v
         ) => SReferenceable ie v r B32 b where
  sget s = LVM.pure (encodeP'x YulSGet (ver'l s))
  sput s x = encodeP'x YulSPut (merge'l (ver'l s, x))
             & \u -> MkLVM (unsafeAxiom, , unsafeCoerceYulPort u)

instance ( KnownNat v, KnownNat (v + 1)
         , YulO1 a, ABIWordValue a, VersionableYulPort ie v
         ) => SReferenceable ie v r (REF a) a where
  sget s = LVM.pure (encodeP'x YulSGet (reduceType'l (ver'l s)))
  sput s x = encodeP'x YulSPut (merge'l (reduceType'l (ver'l s), x))
              & \u -> MkLVM (unsafeAxiom, , unsafeCoerceYulPort u)

------------------------------------------------------------------------------------------------------------------------
-- sgetNP, sgetN, (<==)
------------------------------------------------------------------------------------------------------------------------

class (KnownNat v, YulO1 r) => SGettableNP v r a b where
  sgetNP :: forall. a ⊸ YulLVM v v r b

instance (KnownNat v, YulO1 r) => SGettableNP v r (NP '[]) (NP '[]) where
  sgetNP Nil = LVM.pure Nil

instance ( YulO1 r
         , VersionableYulPort ie v
         , SReferenceable ie v r a b
         , SGettableNP v r (NP as) (NP bs)
         ) => SGettableNP v r (NP (P'x ie r a : as)) (NP (P'V v r b : bs)) where
  sgetNP (a :* as) = LVM.do
    b <- sget a
    bs <- sgetNP as
    LVM.pure (b :* bs)

sgetN :: forall tpl_a tpl_b v r.
  ( KnownNat v
  , ConvertibleTupleNtoNP tpl_a, ConvertibleTupleNtoNP tpl_b
  , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
  ) => tpl_a ⊸ YulLVM v v r tpl_b
sgetN tpl_a = let np_a = fromTupleNtoNP tpl_a
                  np_b = sgetNP np_a :: YulLVM v v r (TupleNtoNP tpl_b)
              in np_b LVM.>>= LVM.pure . fromNPtoTupleN

(<==) :: forall tpl_a tpl_b v r.
  ( ConvertibleTupleNtoNP tpl_a, ConvertibleTupleNtoNP tpl_b
  , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
  ) => tpl_a ⊸ YulLVM v v r tpl_b
(<==) = sgetN

------------------------------------------------------------------------------------------------------------------------
-- sputN
------------------------------------------------------------------------------------------------------------------------

class (KnownNat v, KnownNat (v + 1), YulO1 r) => SPuttableNP v r a where
  sputNP :: forall. a ⊸ YulLVM v (v + 1) r (P'V (v + 1) r ())

instance (KnownNat v, KnownNat (v + 1), YulO1 r) => SPuttableNP v r (NP '[]) where
  sputNP Nil = MkLVM \ctx -> let !(ctx', u) = contextualEmbed ctx ()
                             in (unsafeAxiom, ctx', u)

instance ( KnownNat v, KnownNat (v + 1), YulO1 r
         , VersionableYulPort ie v
         , SReferenceable ie v r a b
         , SPuttableNP v r (NP xs)
         ) => SPuttableNP v r (NP ((P'x ie r a, P'V v r b):xs)) where
  sputNP ((a, b) :* xs) = let x'  = sput a b :: YulLVM v (v + 1) r (P'V (v + 1) r ())
                              x'' = LVM.unsafeCoerceLVM x' :: YulLVM v v r (P'V (v + 1) r ())
                              xs' = sputNP xs :: YulLVM v (v + 1) r (P'V (v + 1) r ())
                          in x'' LVM.>> xs'

sputN :: forall tpl v r.
  ( ConvertibleTupleNtoNP tpl
  , SPuttableNP v r (TupleNtoNP tpl)
  ) => tpl ⊸ YulLVM v (v + 1) r (P'V (v + 1) r ())
sputN tpl = sputNP (fromTupleNtoNP tpl)

------------------------------------------------------------------------------------------------------------------------
-- sputs
------------------------------------------------------------------------------------------------------------------------

data StorageAssignment v r = forall a b ie. SReferenceable ie v r a b => P'x ie r a := P'V v r b

sassign :: forall v r. YulO1 r => StorageAssignment v r ⊸ YulLVM v (v + 1) r (P'V (v + 1) r ())
sassign (to := x) = sput to x

sputs :: forall v r.
  ( KnownNat v, KnownNat (v + 1), YulO1 r
  ) => NonEmpty (StorageAssignment v r) ⊸ YulLVM v (v + 1) r (P'V (v + 1) r ())
sputs (sa :| []) = sassign sa
sputs (sa :| (sa':sas)) =
  let x  = sassign sa LVM.>>= LVM.pure . unsafeCoerceYulPort:: YulLVM v (v + 1) r (P'V v r ())
      x' = LVM.unsafeCoerceLVM x :: YulLVM v v r (P'V v r ())
      xs = sputs (sa' :| sas)
  in x' LVM.>> xs
