{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module packages all the goodies prelude-worthy for programming "YulDSL" in linear-types.

-}
module Prelude.YulDSL
  ( -- * YulDSL/Haskell's Pure Effects
    module YulDSL.Haskell.YulUtils
    -- * YulDSL/Haskell's LinearSMC Support
  , module YulDSL.Haskell.Effects.LinearSMC
    -- * YulDSL/Haskell's Data Types
  , module YulDSL.Haskell.Data.SHMap
    -- * YulDSL Core
  , module YulDSL.Core
    -- * Module linear-base
  , module Data.MPOrd
  , module Prelude.Linear
    -- * Module linear-smc
  , module Control.Category.Linear
  ) where
-- linear-base, replacing Eq/Ord with MPOrd
import Data.MPOrd
import Data.Num.Linear.YulDSL           ()
import Prelude.Linear                   hiding (Eq (..), Ord (..))
-- linear-smc
import Control.Category.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.YulUtils
--
import YulDSL.Haskell.Effects.LinearSMC
--
import YulDSL.Haskell.Data.SHMap
