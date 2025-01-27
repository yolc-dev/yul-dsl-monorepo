{-# LANGUAGE FunctionalDependencies #-}
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
import Data.List.NonEmpty                (NonEmpty ((:|)))
import GHC.TypeLits                      (type (+))
-- constraints
import Data.Constraint.Unsafe            (unsafeAxiom)
-- linear-base
import Control.Category.Linear
import Prelude.Linear                    ((&), (.))
import Unsafe.Linear                     qualified as UnsafeLinear
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad    (LVM (MkLVM))
import Control.LinearlyVersionedMonad    qualified as LVM
import Data.LinearContext                (contextualEmbed)
--
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort


class SReferenceable v r a b | a -> v r, b -> v r where
  sget :: forall. a ⊸ YulMonad v v r b
  sput :: forall. a ⊸ b ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())

instance (YulO2 r b, ABIWordValue b) => SReferenceable v r (P'V v r B32) (P'V v r b) where
  sget a = ypure (encode YulSGet a)
  sput to x = encode YulSPut (merge (to, x))
              & \u -> MkLVM (unsafeAxiom, , UnsafeLinear.coerce u)

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
         ) => SGettableNP v r (NP (a : as)) (NP (b : bs)) where
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
         ) => SPuttableNP v r (NP ((a, b):xs)) where
  sputNP ((a, b) :* xs) = let x' = sput a b :: YulMonad v (v + 1) r (P'V (v + 1) r ())
                              x'' = UnsafeLinear.coerce x' :: YulMonad v v r (P'V (v + 1) r ())
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

data StorageAssignment v r = forall a. (YulO1 a, ABIWordValue a) => P'V v r B32 := P'V v r a

sassign :: forall v r. (YulO1 r) => StorageAssignment v r ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())
sassign (to := x) = sput to x

sputs :: forall v r. YulO1 r => NonEmpty (StorageAssignment v r) ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())
sputs (sa :| []) = sassign sa
sputs (sa :| (sa':sas)) = let x  = sassign sa :: YulMonad v (v + 1) r (P'V (v + 1) r ())
                              x' = UnsafeLinear.coerce x :: YulMonad v v r (P'V v r ())
                              xs = sputs (sa' :| sas)
                           in x' LVM.>> xs
