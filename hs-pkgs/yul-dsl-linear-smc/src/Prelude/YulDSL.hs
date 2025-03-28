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
    module Prelude.Linear
    -- * YulDSL/Haskell/LinearSMC
  , module YulDSL.Haskell.LibLinearSMC
  , module YulDSL.Haskell.Data.SHMap
  ) where
-- linear-base, replacing Eq/Ord with MPOrd
import Prelude.Linear              hiding (Eq (..), Ord (..))
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
--
import YulDSL.Haskell.LibLinearSMC
--
import YulDSL.Haskell.Data.SHMap
