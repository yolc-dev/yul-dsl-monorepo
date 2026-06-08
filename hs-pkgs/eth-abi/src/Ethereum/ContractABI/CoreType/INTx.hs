{-# LANGUAGE AllowAmbiguousTypes #-}
{-|

Copyright   : (c) 2024 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

Ethereum contract ABI assorted integer types.

-}

module Ethereum.ContractABI.CoreType.INTx
  ( INTx, ValidINTx
    -- == Assorted INTx Types
  , U8,U16,U24,U32,U40,U48,U56,U64
  , U72,U80,U88,U96,U104,U112,U120,U128
  , U136,U144,U152,U160,U168,U176,U184,U192
  , U200,U208,U216,U224,U232,U240,U248,U256
  , I8,I16,I24,I32,I40,I48,I56,I64
  , I72,I80,I88,I96,I104,I112,I120,I128
  , I136,I144,I152,I160,I168,I176,I184,I192
  , I200,I208,I216,I224,I232,I240,I248,I256
  ) where

-- base
import Data.Bits                         (shift)
import Data.Coerce                       (coerce)
import Data.Maybe                        (fromJust)
import Data.Proxy                        (Proxy (Proxy))
import GHC.TypeLits                      (type (+), type (<=), type (<=?))
-- cereal
-- eth-abi
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable
import Internal.Data.Type.Bool


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
newtype INTx (s :: Bool) (n :: Nat) = INT Integer
  deriving newtype (Eq, Ord, Enum)

-- | A constraint alias for 'KnownBool' and 'ValidINTn'.
type ValidINTx s n = (KnownBool s, ValidINTn n)



------------------------------------------------------------------------------------------------------------------------
-- Type class instances
------------------------------------------------------------------------------------------------------------------------

--
-- ABITypeable
--

instance forall s n. ValidINTx s n => ABITypeable (INTx s n) where
  type instance ABITypeDerivedOf (INTx s n) = INTx s n
  abiTypeInfo = "i"


-- Note: Code generation command
-- sh$ for i in `seq 1 32`;do echo "type U$((i*8)) = INTx False $i;type I$((i*8)) = INTx True $i";done
type U8 = INTx False 1;type I8 = INTx True 1
type U16 = INTx False 2;type I16 = INTx True 2
type U24 = INTx False 3;type I24 = INTx True 3
type U32 = INTx False 4;type I32 = INTx True 4
type U40 = INTx False 5;type I40 = INTx True 5
type U48 = INTx False 6;type I48 = INTx True 6
type U56 = INTx False 7;type I56 = INTx True 7
type U64 = INTx False 8;type I64 = INTx True 8
type U72 = INTx False 9;type I72 = INTx True 9
type U80 = INTx False 10;type I80 = INTx True 10
type U88 = INTx False 11;type I88 = INTx True 11
type U96 = INTx False 12;type I96 = INTx True 12
type U104 = INTx False 13;type I104 = INTx True 13
type U112 = INTx False 14;type I112 = INTx True 14
type U120 = INTx False 15;type I120 = INTx True 15
type U128 = INTx False 16;type I128 = INTx True 16
type U136 = INTx False 17;type I136 = INTx True 17
type U144 = INTx False 18;type I144 = INTx True 18
type U152 = INTx False 19;type I152 = INTx True 19
type U160 = INTx False 20;type I160 = INTx True 20
type U168 = INTx False 21;type I168 = INTx True 21
type U176 = INTx False 22;type I176 = INTx True 22
type U184 = INTx False 23;type I184 = INTx True 23
type U192 = INTx False 24;type I192 = INTx True 24
type U200 = INTx False 25;type I200 = INTx True 25
type U208 = INTx False 26;type I208 = INTx True 26
type U216 = INTx False 27;type I216 = INTx True 27
type U224 = INTx False 28;type I224 = INTx True 28
type U232 = INTx False 29;type I232 = INTx True 29
type U240 = INTx False 30;type I240 = INTx True 30
type U248 = INTx False 31;type I248 = INTx True 31
type U256 = INTx False 32;type I256 = INTx True 32

-- Alternatively: we can use top-level TH splice to generate these. But it confused LSP, for now.
--
-- forM [ (s, n) | s <- [True, False], n <- [1..32] ] $ \(s, n) -> do
--   name <- TH.newName ((if s then "I" else "U") ++ show (n * 8))
--   TH.tySynD name [] ((TH.conT ''INTx)
--                       `TH.appT` (TH.promotedT (if s then 'True else 'False))
--                       `TH.appT` (TH.litT (TH.numTyLit n)))
