{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module contains template haskell generated code to work with n-ary tuples. It includes type families to convert
between the TupleN types and their isomorphic SimpleNP type, and functions that actually convert between their values.

It supports up to 64-ary tuple.

-}
module Data.TupleN
  ( Solo (MkSolo)
  , TupleNtoNP, FromTupleNtoNP (fromTupleNtoNP), NPtoTupleN, FromNPtoTupleN (fromNPtoTupleN)
  , ConvertibleTupleN
  ) where

-- ghc-experimental
import Data.Tuple.Experimental (Solo (MkSolo))
--
import Data.TupleN.TH


-- | A constraint for TupleN types that are convertible to NP and vice versa.
type ConvertibleTupleN tpl = ( NPtoTupleN (TupleNtoNP tpl) ~ tpl
                             , FromTupleNtoNP tpl
                             , FromNPtoTupleN (TupleNtoNP tpl)
                             )
