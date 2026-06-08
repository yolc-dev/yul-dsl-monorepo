{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures   #-}

{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

'ABITypeable' is the required type class for extended types.

-}
module Ethereum.ContractABI.ABITypeable
 ( ABITypeable (..)
 ) where

-- base
--
import  Ethereum.ContractABI.ABICoreType
