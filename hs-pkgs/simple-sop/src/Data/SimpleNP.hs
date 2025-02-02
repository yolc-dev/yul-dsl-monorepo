{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

A simple n-ary product without any type function that is present in the sop-core package.

-}
module Data.SimpleNP
  ( NP (Nil, (:*))
  ) where
-- base
import Data.Kind (Type)


-- | N-ary product without a type function comparing to its homonym in the "sop" package.
data NP :: [Type] -> Type where
  Nil  :: NP '[]
  (:*) :: x -> NP xs -> NP (x : xs)
infixr 5 :*

deriving instance Eq (NP ('[]))
deriving instance (Eq x, Eq (NP xs)) => Eq (NP (x:xs))

instance Show (NP '[]) where
  show _ = "Nil"
instance (Show x, Show (NP xs)) => Show (NP (x:xs)) where
  show (x :* xs) = "(" ++ show x ++ " :* " ++ show xs ++ ")"
