{-# LANGUAGE LinearTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module YulDSL.Haskell.LibPure
  -- * YulDSL/Haskell's pure effect support
  ( module YulDSL.Core
  , module YulDSL.Haskell.Effects.Pure
  -- * Data and Control Flow Extensions
  , module Control.IfThenElse
  , module Control.PatternMatchable
  , module Data.MPOrd
  , module Data.Type.Function
  -- * Re-exports
  , Solo (MkSolo)
  ) where
-- base
import Data.Tuple                      (Solo (MkSolo))
-- (data-control-extra)
import Control.IfThenElse
import Control.PatternMatchable
import Data.MPOrd
import Data.Type.Function
-- yul-dsl
import YulDSL.Core
--
import YulDSL.Haskell.YulCatObj.Maybe  ()
import YulDSL.Haskell.YulCatObj.NP     ()
import YulDSL.Haskell.YulCatObj.TUPLEn ()
--
import YulDSL.Haskell.Effects.Pure
