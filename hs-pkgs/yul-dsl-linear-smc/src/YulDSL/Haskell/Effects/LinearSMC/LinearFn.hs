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
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YulPort

------------------------------------------------------------------------------------------------------------------------
-- Linear Non-Pure Effects
------------------------------------------------------------------------------------------------------------------------

lfn' :: forall f xs b.
  ( YulO2 (NP xs) b
  , EquivalentNPOfFunction f xs b
  ) =>
  String ->
  (forall r. YulO1 r => P'x PurePort r (NP xs) ⊸ P'x PurePort r b) ->
  PureFn f
lfn' cid f = MkPureFn (cid, decode'l f)
