{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module provides VersionThread and YLVM APIs that work with contract storages.

-}
module YulDSL.Haskell.Effects.LinearSMC.Storage
  ( SReferenceable (sget'l, sput'l)
  , sget, sgetM, SGettableNP (sgetNP), sgetN
  , sput, (<:=), sputM, (<<:=), sputMM, (<<:=<<)
  ) where
-- base
import GHC.TypeLits                             (type (+), type (<=))
-- linear-base
import Prelude.Linear                           (($), (.))
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad.LVM       qualified as LVM
--
import YulDSL.Haskell.Effects.LinearSMC.YLVM
import YulDSL.Haskell.Effects.LinearSMC.YulPort


class (KnownNat v, YulO3 a b r) => SReferenceable v r a b where
  sget'l :: forall. P'V v r a ⊸ P'V v r b
  sput'l :: forall. v <= v + 1 => VersionThread r ⊸ P'V v r a ⊸ P'V v r b ⊸ (VersionThread r, P'V (v + 1) r ())

instance ( KnownNat v, YulO2 b r
         , ABIWordValue b
         ) => SReferenceable v r B32 b where
  sget'l s = encodeP'x YulSGet (ver'l s)
  sput'l vt s x =
    let !(x1, x2) = dup'l x
    in vtseq vt x1 (unsafeCoerceYulPort (encodeP'x YulSPut (merge'l (ver'l s, x2))))

instance ( KnownNat v, YulO2 b r
         , SReferenceable v r B32 b
         ) => SReferenceable v r (REF b) b where
  sget'l s = sget'l (reduceType'l s)
  sput'l vt s = sput'l vt (reduceType'l s)

-------- ----------------------------------------------------------------------------------------------------------------
-- sget,sgetNP, sgetN
------------------------------------------------------------------------------------------------------------------------

sget :: forall a b ie r v vref_.
  ( YulO3 r a b
  , YulVarRef v r (P'x ie r) vref_
  , SReferenceable v r a b
  ) =>
  vref_ a -> YLVM v v r (Ur (Rv v r b))
sget avar = ytkvarv avar LVM.>>= ymkvar . sget'l

-- sgetM :: forall a b ie r v vref_.
--   ( YulO3 r a b
--   , YulVarRef v r (P'x ie r) vref_
--   , SReferenceable v r a b
--   ) =>
--   YLVM v v r (Ur (vref_ a)) -> YLVM v v r (Ur (Rv v r b))
-- sgetM mavar = mavar LVM.>>= \(Ur avar) -> ytkvarv avar LVM.>>= ymkvar . sget'l

sgetM :: forall a b r v.
  ( YulO3 r a b
  -- , YulVarRef v r (P'x ie r) vref_
  , SReferenceable v r a b
  ) =>
  YLVM v v r (Ur (Rv v r a)) -> YLVM v v r (Ur (Rv v r b))
sgetM mavar = mavar LVM.>>= \(Ur avar) -> ytkvarv avar LVM.>>= ymkvar . sget'l

class (KnownNat v, YulO1 r) => SGettableNP v r np b where
  sgetNP :: forall. np -> YLVM v v r b

instance (KnownNat v, YulO1 r) =>
         SGettableNP v r (NP '[]) (Ur (NP '[])) where
  sgetNP Nil = LVM.pure $ Ur Nil

instance ( YulO3 r a b
         , YulVarRef v r (P'x ie r) vref_
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
  ) => tpl_a -> YLVM v v r tpl_b
sgetN tpl_a = let np_a = fromTupleNtoNP tpl_a
                  np_b = sgetNP np_a :: YLVM v v r (TupleNtoNP tpl_b)
              in np_b LVM.>>= LVM.pure . fromNPtoTupleN

------------------------------------------------------------------------------------------------------------------------
-- sput, sputM, sputMM
------------------------------------------------------------------------------------------------------------------------

sput, (<:=) ::
  ( KnownNat (v + 1), v <= v + 1, YulO1 r
  , YulVarRef v r (P'x iea r) vref_a_
  , YulVarRef v r (P'x ieb r) vref_b_
  , SReferenceable v r a b
  ) =>
  vref_a_ a ->
  vref_b_ b ->
  YLVM v (v + 1) r ()
sput aVar bVar = LVM.do
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure ()
(<:=) = sput

infix 0 <:=, <<:=, <<:=<<

sputM, (<<:=) :: forall v a b r vref_a_ vref_b_ iea ieb.
  ( KnownNat (v + 1), v <= v + 1, YulO1 r
  , YulVarRef v r (P'x iea r) vref_a_
  , YulVarRef v r (P'x ieb r) vref_b_
    -- b
  , SReferenceable v r a b
  ) =>
  YLVM v v r (Ur (vref_a_ a)) ->
  vref_b_ b ->
  YLVM v (v + 1) r ()
sputM aVarM bVar = LVM.do
  Ur aVar <- aVarM
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure ()
(<<:=) = sputM

sputMM, (<<:=<<) :: forall v a b r vref_a_ vref_b_ iea ieb.
  ( KnownNat (v + 1), v <= v + 1, YulO1 r
  , YulVarRef v r (P'x iea r) vref_a_
  , YulVarRef v r (P'x ieb r) vref_b_
    -- b
  , SReferenceable v r a b
  ) =>
  YLVM v v r (Ur (vref_a_ a)) ->
  YLVM v v r (Ur (vref_b_ b)) ->
  YLVM v (v + 1) r ()
sputMM aVarM bVarM = LVM.do
  Ur aVar <- aVarM
  Ur bVar <- bVarM
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure ()
(<<:=<<) = sputMM
