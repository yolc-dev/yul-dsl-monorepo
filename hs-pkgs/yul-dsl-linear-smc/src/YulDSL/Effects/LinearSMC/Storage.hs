{-|

Copyright   : (c) 2024-5 Miao, ZhiCheng
License     : LGPL-3

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module provides yul monads that work with contract storage.

-}
module YulDSL.Effects.LinearSMC.Storage
  ( sget, SLocation (..)
  , sput, SPuttable (sputs)
  ) where
-- base
import GHC.TypeLits                      (type (+))
-- constraints
import Data.Constraint.Unsafe            (unsafeAxiom)
-- linear-base
import Control.Category.Linear
import Prelude.Linear                    ((&))
import Unsafe.Linear                     qualified as UnsafeLinear
-- yul-dsl
import YulDSL.Core
-- linearly-versioned-monad
import Control.LinearlyVersionedMonad    (LVM (MkLVM))
import Control.LinearlyVersionedMonad    qualified as LVM
import Data.LinearContext                (contextualEmbed)
--
import YulDSL.Effects.LinearSMC.YulMonad
import YulDSL.Effects.LinearSMC.YulPort


data SLocation v r = PureLocation (P'P r B32)
                   | VersionedLocation (P'V v r B32)

sget :: forall a r v. (YulO2 r a, ABIWordValue a)
     => SLocation v r ⊸ YulMonad v v r (P'V v r a)
sget (VersionedLocation a) = ypure (encode YulSGet a)
sget (PureLocation a)      = ypure (encode YulSGet (UnsafeLinear.coerce a))

sput :: forall v r a. (YulO2 r a, ABIWordValue a)
      => SLocation v r ⊸ P'V v r a ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())
sput to x = case to of
              (VersionedLocation to') -> go to'
              (PureLocation to')      -> go (UnsafeLinear.coerce to')
  where go to' = encode YulSPut (merge (to', x))
                 & \u -> MkLVM (unsafeAxiom, , UnsafeLinear.coerce u)

class SPuttable v r a where
  sputs :: forall. a ⊸ YulMonad v (v + 1) r (P'V (v + 1) r ())

instance (YulO2 r a, ABIWordValue a) => SPuttable v r (SLocation v r, P'V v r a) where
  sputs (a, x) = sput a x

instance (YulO1 r) => SPuttable v r (NP '[]) where
  sputs Nil = MkLVM \ctx -> let !(ctx', u) = contextualEmbed ctx ()
                            in (unsafeAxiom, ctx', u)

instance ( YulO1 r
         , SPuttable v r x
         , SPuttable v r (NP xs)
         ) => SPuttable v r (NP (x:xs)) where
  sputs (x :* xs) = let x' = sputs x :: YulMonad v (v + 1) r (P'V (v + 1) r ())
                        x'' = UnsafeLinear.coerce x' :: YulMonad v v r (P'V (v + 1) r ())
                        xs' = sputs xs :: YulMonad v (v + 1) r (P'V (v + 1) r ())
                    in x'' LVM.>> xs'
