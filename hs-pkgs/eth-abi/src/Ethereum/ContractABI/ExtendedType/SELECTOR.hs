{-# LANGUAGE AllowAmbiguousTypes #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module provides the data types of a selector. A selector encodes the four-bytes identifier of a smart contract
function.

-}
module Ethereum.ContractABI.ExtendedType.SELECTOR
 ( FuncSig (MkFuncSig)
 , SELECTOR (SELECTOR)
 , mkTypedSelector
 , mkRawSelector
 , showSelectorOnly
 ) where

-- base
import Data.List                            (intercalate)
-- eth-abi
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable
import Ethereum.ContractABI.CoreType.BYTESn


--
-- FuncSig
--

-- | External function signature. This optional information does not have run-time representation.
data FuncSig = forall a. ABITypeable a => MkFuncSig String {- function name -}

instance Show FuncSig where
  show (MkFuncSig @a fname) = let args = fmap abiCoreTypeCanonName (abiTypeInfo @a)
                              in  fname ++ "(" ++ intercalate "," args ++ ")"

--
-- SELECTOR
--

-- | Selector value type with the optional function signature tagged.
newtype SELECTOR = SELECTOR (B4, Maybe FuncSig)

-- | Create a selector from a function name @fname@ and its input type signature @a@.
mkTypedSelector :: forall a. ABITypeable a => String -> SELECTOR
mkTypedSelector fname = SELECTOR (bytesnFromWord8s bs4bytes, Just (MkFuncSig @a fname))
  where
    sig = show (MkFuncSig @a fname)
    bs4bytes = take 4 (bytesnToWords (stringKeccak256 sig))

-- | Create a selector from a raw 'U32' value.
mkRawSelector :: B4 -> SELECTOR
mkRawSelector sig = SELECTOR (sig, Nothing)

instance Show SELECTOR where
  show (SELECTOR (sel, Just sig)) = show sel ++ " /* " ++ show sig ++ " */"
  show (SELECTOR (sel, Nothing))  = show sel

-- | A function shows only the selector value itself without the function signature.
showSelectorOnly :: SELECTOR -> String
showSelectorOnly (SELECTOR (sel, _)) = show sel
