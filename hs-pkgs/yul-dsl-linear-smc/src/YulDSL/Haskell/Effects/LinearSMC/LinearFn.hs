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



lfn' :: forall x xs b.
  ( YulO2 (NP '[x]) b
  , '[x] ~ xs
  ) =>
  (forall r. YulO1 r => P'P r (NP '[x]) ⊸ P'P r b) ->
  PureFn (x -> b)
lfn' f = MkPureFn (decodeP'x f)
