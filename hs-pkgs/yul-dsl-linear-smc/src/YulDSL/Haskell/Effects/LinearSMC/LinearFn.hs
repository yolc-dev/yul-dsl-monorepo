{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental
-}
module YulDSL.Haskell.Effects.LinearSMC.LinearFn
  ( -- * Build Linear Yul Functions
    lfn'
    -- * Call External Smart Contract Functions
  ) where
-- base
-- template-haskell
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort

import Data.Kind     (Type)
--


type family UncurryNP'Fst f :: [Type] where
  UncurryNP'Fst (x1 %_-> g) = x1 : UncurryNP'Fst (g)
  UncurryNP'Fst         (b) = '[]

-- | Uncurry the result of a function.
type family UncurryNP'Snd (f :: Type) where
  UncurryNP'Snd (_ %_-> g) = UncurryNP'Snd (g)
  UncurryNP'Snd        (b) = b

decode'l :: forall a b. YulO2 a b
  => (forall r. YulO1 r => P'P r a ⊸ P'P r b)
  -> YulCat Pure a b
decode'l f = YulUnsafeCoerceEffect (decodeP'x f)

------------------------------------------------------------------------------------------------------------------------
-- Linear Non-Pure Effects
------------------------------------------------------------------------------------------------------------------------

lfn' :: forall f xs b.
  ( YulO2 (NP xs) b
  , UncurryNP'Fst f ~ xs
  , UncurryNP'Snd f ~ b
  ) =>
  (forall r. YulO1 r => P'P r (NP xs) ⊸ P'P r b) ->
  PureFn f
lfn' f = MkPureFn (decode'l f)
