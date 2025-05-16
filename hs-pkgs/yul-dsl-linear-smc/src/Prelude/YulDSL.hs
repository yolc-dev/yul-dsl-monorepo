{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module packages all the goodies prelude-worthy for programming "YulDSL" in linear-types.

-}
module Prelude.YulDSL
  ( -- * YulDSL/Haskell/LinearSMC
    module YulDSL.Haskell.LibLinearSMC
  , module YulDSL.Haskell.Data.SMap
    -- TODO: - Fixed inability to re-export the ``Data.Tuple.MkSolo`` constructor (:ghc-ticket:`25182`)
  , Solo (MkSolo)
  ) where
import Data.Tuple                  (Solo (MkSolo))
--
import YulDSL.Haskell.LibLinearSMC
--
import YulDSL.Haskell.Data.SMap
