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
  , sget, sgetM
  -- , SGettableNP (sgetNP), sgetN
  , sput, (<:=), sputM, (<<:=), sputMM, (<<:=<<)
  ) where
-- base
import GHC.TypeLits                             (type (+), type (<=))
-- linear-base
import Prelude.Linear                           ((.))
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

sgetM :: forall a b r v.
  ( YulO3 r a b
  -- , YulVarRef v r (P'x ie r) vref_
  , SReferenceable v r a b
  ) =>
  YLVM v v r (Ur (Rv v r a)) -> YLVM v v r (Ur (Rv v r b))
sgetM mavar = mavar LVM.>>= \(Ur avar) -> ytkvarv avar LVM.>>= ymkvar . sget'l

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
  YLVM v (v + 1) r (Ur ())
sput aVar bVar = LVM.do
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure (Ur ())
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
  YLVM v (v + 1) r (Ur ())
sputM aVarM bVar = LVM.do
  Ur aVar <- aVarM
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure (Ur ())
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
  YLVM v (v + 1) r (Ur ())
sputMM aVarM bVarM = LVM.do
  Ur aVar <- aVarM
  Ur bVar <- bVarM
  a <- ytkvarv aVar
  b <- ytkvarv bVar
  yrunvt (\vt -> sput'l vt a b)
  LVM.pure (Ur ())
(<<:=<<) = sputMM
