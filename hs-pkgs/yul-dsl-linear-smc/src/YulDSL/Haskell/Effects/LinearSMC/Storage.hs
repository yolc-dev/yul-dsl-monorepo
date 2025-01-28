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
import Data.List.NonEmpty                        (NonEmpty ((:|)))
import GHC.TypeLits                              (type (+))
-- constraints
import Data.Constraint.Unsafe                    (unsafeAxiom)
-- linear-base
import Prelude.Linear                            ((&), (.))
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad            (LVM (MkLVM))
import Control.LinearlyVersionedMonad            qualified as LVM
import Data.LinearContext                        (contextualEmbed)
--
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort


class YulO2 a b => SReferenceable v r a b where
  sget :: forall. YulO1 r => P'V v r a ⊸ YulMonad v v r (P'V v r b)
  sput :: forall. YulO1 r => P'V v r a ⊸ P'V v r b ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())

instance (YulO1 b, ABIWordValue b) => SReferenceable v r B32 b where
  sget a = ypure (encode'x YulSGet a)
  sput to x = encode'x YulSPut (merge'l (to, x))
              & \u -> MkLVM (unsafeAxiom, , unsafeCoerceYulPort u)

instance (YulO1 a, ABIWordValue a) => SReferenceable v r (REF a) a where
  sget a = ypure (encode'x YulSGet (reduceType'l a))
  sput to x = encode'x YulSPut (merge'l (reduceType'l to, x))
              & \u -> MkLVM (unsafeAxiom, , unsafeCoerceYulPort u)

------------------------------------------------------------------------------------------------------------------------
-- sgetNP, sgetN, (<==)
------------------------------------------------------------------------------------------------------------------------

class SGettableNP v r a b where
  sgetNP :: forall. a ⊸ YulMonad v v r b

instance SGettableNP v r (NP '[]) (NP '[]) where
  sgetNP Nil = ypure Nil

instance ( YulO1 r
         , SReferenceable v r a b
         , SGettableNP v r (NP as) (NP bs)
         ) => SGettableNP v r (NP (P'V v r a : as)) (NP (P'V v r b : bs)) where
  sgetNP (a :* as) = LVM.do
    b <- sget a
    bs <- sgetNP as
    ypure (b :* bs)

sgetN :: forall tpl_a tpl_b v r.
  ( ConvertibleTupleN tpl_a, ConvertibleTupleN tpl_b
  , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
  ) => tpl_a ⊸ YulMonad v v r tpl_b
sgetN tpl_a = let np_a = fromTupleNtoNP tpl_a
                  np_b = sgetNP np_a :: YulMonad v v r (TupleNtoNP tpl_b)
              in np_b LVM.>>= ypure . fromNPtoTupleN

(<==) :: forall tpl_a tpl_b v r.
  ( ConvertibleTupleN tpl_a, ConvertibleTupleN tpl_b
  , SGettableNP v r (TupleNtoNP tpl_a) (TupleNtoNP tpl_b)
  ) => tpl_a ⊸ YulMonad v v r tpl_b
(<==) = sgetN

------------------------------------------------------------------------------------------------------------------------
-- sputN
------------------------------------------------------------------------------------------------------------------------

class SPuttableNP v r a where
  sputNP :: forall. a ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())

instance (YulO1 r) => SPuttableNP v r (NP '[]) where
  sputNP Nil = MkLVM \ctx -> let !(ctx', u) = contextualEmbed ctx ()
                             in (unsafeAxiom, ctx', u)

instance ( YulO1 r
         , SReferenceable v r a b
         , SPuttableNP v r (NP xs)
         ) => SPuttableNP v r (NP ((P'V v r a, P'V v r b):xs)) where
  sputNP ((a, b) :* xs) = let x'  = sput a b :: YulMonad v (v + 1) r (P'V (v + 1) r ())
                              x'' = LVM.unsafeCoerceLVM x' :: YulMonad v v r (P'V (v + 1) r ())
                              xs' = sputNP xs :: YulMonad v (v + 1) r (P'V (v + 1) r ())
                          in x'' LVM.>> xs'

sputN :: forall tpl v r.
  ( ConvertibleTupleN tpl
  , SPuttableNP v r (TupleNtoNP tpl)
  ) => tpl ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())
sputN tpl = sputNP (fromTupleNtoNP tpl)

------------------------------------------------------------------------------------------------------------------------
-- sputs
------------------------------------------------------------------------------------------------------------------------

data StorageAssignment v r = forall a b. SReferenceable v r a b => P'V v r a := P'V v r b

sassign :: forall v r. YulO1 r => StorageAssignment v r ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())
sassign (to := x) = sput to x

sputs :: forall v r. YulO1 r => NonEmpty (StorageAssignment v r) ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())
sputs (sa :| []) = sassign sa
sputs (sa :| (sa':sas)) =
  let x  = sassign sa LVM.>>= ypure . unsafeCoerceYulPort:: YulMonad v (v + 1) r (P'V v r ())
      x' = LVM.unsafeCoerceLVM x :: YulMonad v v r (P'V v r ())
      xs = sputs (sa' :| sas)
  in x' LVM.>> xs
