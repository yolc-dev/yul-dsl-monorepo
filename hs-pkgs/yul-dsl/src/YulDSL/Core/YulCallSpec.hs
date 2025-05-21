{-# LANGUAGE AllowAmbiguousTypes #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

This module provides the data types of for defining external call specifications.

-}
module YulDSL.Core.YulCallSpec
 ( -- function signature
   FuncSig (MkFuncSig)
   -- selector
 , Selector (MkSelector)
 , mkTypedSelector
 , mkRawSelector
 , showSelectorOnly
   --
 , CallTarget
 , CallGasLimit
 , CallValue
 , CallParams
 ) where

-- base
import Data.List            (intercalate)
-- eth-abi
import Ethereum.ContractABI


--
-- FuncSig
--

-- | External function signature. This optional information does not have run-time representation.
data FuncSig = forall a. ABITypeable a => MkFuncSig String {- function name -}

instance Show FuncSig where
  show (MkFuncSig @a fname) = let args = fmap abiCoreTypeCanonName (abiTypeInfo @a)
                              in  fname ++ "(" ++ intercalate "," args ++ ")"

--
-- Selector
--

-- | Selector value type with the optional function signature tagged.
newtype Selector = MkSelector (B4, Maybe FuncSig)

-- | Create a selector from a function name @fname@ and its input type signature @a@.
mkTypedSelector :: forall a. ABITypeable a => String -> Selector
mkTypedSelector fname = MkSelector (bytesnFromWord8s bs4bytes, Just (MkFuncSig @a fname))
  where
    sig = show (MkFuncSig @a fname)
    bs4bytes = take 4 (bytesnToWords (stringKeccak256 sig))

-- | Create a selector from a raw 'U32' value.
mkRawSelector :: B4 -> Selector
mkRawSelector sig = MkSelector (sig, Nothing)

instance Show Selector where
  show (MkSelector (sel, Just sig)) = show sel ++ " /* " ++ show sig ++ " */"
  show (MkSelector (sel, Nothing))  = show sel

-- | A function shows only the selector value itself without the function signature.
showSelectorOnly :: Selector -> String
showSelectorOnly (MkSelector (sel, _)) = show sel

--
-- External Call Parameters.
--

type CallTarget   = ADDR
type CallGasLimit = U256
type CallValue    = U256

-- TODO: use ADT
type CallParams = (I CallTarget, I CallGasLimit, I CallValue)
