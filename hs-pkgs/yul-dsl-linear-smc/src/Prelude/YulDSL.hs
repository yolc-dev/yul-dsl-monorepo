{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module packages all the goodies prelude-worthy for programming "YulDSL" in linear-types.

-}
module Prelude.YulDSL
  ( -- * Module linear-base
    module Data.MPOrd
  , module Prelude.Linear

    -- * YulDSL Core
  , module YulDSL.Core

    -- * YulDSL/Haskell's Pure Effect Utils
  , module YulDSL.Haskell.Lib

    -- * YulDSL/Haskell's LinearSMC Support
  , module YulDSL.Haskell.Effects.LinearSMC
  , module YulDSL.Haskell.YulUtils.LinearSMC
  , module YulDSL.Haskell.Data.SHMap
  ) where
-- linear-base, replacing Eq/Ord with MPOrd
import Data.MPOrd
import Data.Num.Linear.YulDSL            ()
import Prelude.Linear                    hiding (Eq (..), Ord (..))
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.Lib
--
import YulDSL.Haskell.Effects.LinearSMC
--
import YulDSL.Haskell.YulUtils.LinearSMC
--
import YulDSL.Haskell.Data.SHMap
