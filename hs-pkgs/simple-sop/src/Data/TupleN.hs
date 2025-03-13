{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
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
  ( TupleNtoNP, NPtoTupleN
  , FromTupleNtoNP (fromTupleNtoNP), FromNPtoTupleN (fromNPtoTupleN)
  , ConvertibleTupleNtoNP, ConvertibleNPtoTupleN
  -- re-export solo tuple type
  , Solo (MkSolo)
  ) where

-- ghc-experimental
import Data.Tuple.Experimental (Solo (MkSolo))
--
import Data.TupleN.TH


-- | A constraint alias for TupleN types that are convertible to NP and vice versa.
type ConvertibleTupleNtoNP tpl = ( NPtoTupleN (TupleNtoNP tpl) ~ tpl
                                 , FromTupleNtoNP tpl
                                 , FromNPtoTupleN (TupleNtoNP tpl)
                                 )

-- | A constraint alias for NP types that are convertible to TupleN and vice versa.
type ConvertibleNPtoTupleN np = ( TupleNtoNP (NPtoTupleN np) ~ np
                                , FromTupleNtoNP (NPtoTupleN np)
                                , FromNPtoTupleN np
                                )
