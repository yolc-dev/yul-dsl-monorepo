{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

-}
module Ethereum.ContractABI.ABITypeCoercible
  ( SameABICoreType, ABITypeCoercible
  ) where
-- (simple-np)
import Data.TupleN                      (Solo)
--
import Ethereum.ContractABI.ABITypeable
import Ethereum.ContractABI.CoreType.NP


type SameABICoreType a a' = ABITypeDerivedOf a ~ ABITypeDerivedOf a'

class ABITypeCoercible a b

-- Solo Tuple
instance forall a. ABITypeCoercible a (Solo a)
instance forall a. ABITypeCoercible (Solo a) a

-- unitor coercion instances
instance forall a. ABITypeCoercible a (a, ())
instance forall a. ABITypeCoercible (a, ()) a

-- associative coercion instances
instance forall a b c. ABITypeCoercible ((a, b), c) (a, (b, c))
instance forall a b c. ABITypeCoercible (a, (b, c)) ((a, b), c)

-- NP coercion instances
instance ABITypeCoercible (NP '[]) ()
instance ABITypeCoercible () (NP '[])
instance forall x xs. ABITypeCoercible (NP (x:xs)) (x, NP xs)
--
instance forall x. ABITypeCoercible x (NP '[x])
instance forall x xs. ABITypeCoercible (x, NP xs) (NP (x:xs))
