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
  , intxSign, intxNBits
  , intxUpCast, intxSafeCast
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
import Control.Exception                 (assert)
import Control.Monad                     (replicateM)
import Data.Bits                         (shift)
import Data.Coerce                       (coerce)
import Data.Maybe                        (fromJust)
import Data.Proxy                        (Proxy (Proxy))
import Data.Word                         (Word8)
import GHC.TypeError                     (Assert, ErrorMessage (Text), TypeError)
import GHC.TypeLits                      (type (+), type (<=), type (<=?))
-- cereal
import Data.Serialize                    qualified as S
-- eth-abi
import Ethereum.ContractABI.ABICoreType
import Ethereum.ContractABI.ABITypeable
import Ethereum.ContractABI.ABITypeCodec
import Internal.Data.Type.Bool


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
newtype INTx (s :: Bool) (n :: Nat) = INT Integer
  deriving newtype (Eq, Ord, Enum)

-- | A constraint alias for 'KnownBool' and 'ValidINTn'.
type ValidINTx s n = (KnownBool s, ValidINTn n)

-- | Sign of the INTx type. Use type application on @a@.
intxSign :: forall a (s :: Bool) (n :: Nat). (a ~ INTx s n, ValidINTx s n) => Bool
intxSign = fromSBool (boolSing @s)

-- | Number of bits for the INTx type. Use type application on @a@.
intxNBits :: forall a (s :: Bool) (n :: Nat). (a ~ INTx s n, ValidINTn n) => Int
intxNBits = fromEnum (8 * natVal (Proxy @n))

-- | Integer up-casting cases.
intxUpCast :: forall (s1 :: Bool) (n1 :: Nat)  (s2 :: Bool) (n2 :: Nat).
              ( KnownBool s1, KnownBool s2, ValidINTn n1, ValidINTn n2
                -- this must be true in any case
              , n1 <= n2
                -- now check signedness
              , Assert (
                  -- same signedness
                  (s1 && s2) ||
                  (Not s1 && Not s2) ||
                  -- for unsigned input, output can be signed but with larger data size
                  -- Note: (<=?) maybe not work reliably, you may always fallback to intxSafeCast.
                  (Not s1 && s2 && (n1 + 1 <=? n2)))
                (TypeError (Text "Cannot safely up-cast intx")))
           => INTx s1 n1 -> INTx s2 n2
intxUpCast (INT x) = fromInteger x

-- | Safe integer casting.
intxSafeCast :: forall (s1 :: Bool) (n1 :: Nat) (s2 :: Bool) (n2 :: Nat).
                (KnownBool s1, KnownBool s2, ValidINTn n1, ValidINTn n2)
             => INTx s1 n1 -> Maybe (INTx s2 n2)
intxSafeCast (INT x) = fromInteger x

-- | Convert from valid integer to a list of word8.
integerToWord8s :: forall s n. ValidINTx s n => Integer -> [Word8]
integerToWord8s x =
  let x' = if fromBoolKind @s then complement x else x
      (res, ws) = foldl'
        (\(res', ws') _ -> (res' `div` 256, fromInteger (res' `rem` 256) : ws'))
        (x', [])
        [0 .. fromValidINTn @n - 1]
  in assert (res == 0) (if x < 0 then fmap (0xff -) ws else ws)
  where complement y = if y < 0 then -y - 1 else y

word8sToInteger :: forall s n. ValidINTx s n => [Word8] -> Integer
word8sToInteger ws =
  let isneg = if fromBoolKind @s then ws !! 0 >= 80 else False
      ws' = if isneg then fmap (0xff -) ws else ws
      x = assert (toInteger (length ws) == fromSNat (natSing @n))
          (g 0 (reverse ws'))
  in if isneg then -x - 1 else x
  where g :: Int -> [Word8] -> Integer
        g _ []     = 0
        g i (x:xs) = (toInteger x) * (2 ^ i) + g (i + 8) xs

------------------------------------------------------------------------------------------------------------------------
-- Type class instances
------------------------------------------------------------------------------------------------------------------------

--
-- ABITypeable
--

instance forall s n. ValidINTx s n => ABITypeable (INTx s n) where
  type instance ABITypeDerivedOf (INTx s n) = INTx s n
  abiDefault = 0
  abiTypeInfo = [INTx' (boolSing @s) (natSing @n)]

instance forall s n. ValidINTx s n => ABITypeCodec (INTx s n) where
  abiEncoder = foldMap S.put . integerToWord8s @s @32 . toInteger
  abiDecoder = INT . word8sToInteger @s @32 <$> replicateM (fromValidINTn @32) S.get

--
--  Num hierarchy classes for (Maybe INTx s n)
--

instance ValidINTx s n => Bounded (Maybe (INTx s n)) where
  minBound = Just . INT $
    if intxSign @(INTx s n) then negate (1 `shift` (nbits - 1)) else 0
    where nbits = intxNBits @(INTx s n)
  maxBound = Just . INT $
    if intxSign @(INTx s n) then (1 `shift` (nbits - 1)) - 1 else (1 `shift` nbits) - 1
    where nbits = intxNBits @(INTx s n)

instance ValidINTx s n => Num (Maybe (INTx s n)) where
  (Just (INT a)) + (Just (INT b)) = fromInteger (a + b)
  _ + _                           = Nothing

  (Just (INT a)) - (Just (INT b)) = fromInteger (a - b)
  _ - _                           = Nothing

  (Just (INT a)) * (Just (INT b)) = fromInteger (a * b)
  _ * _                           = Nothing

  abs (Just (INT a)) = fromInteger (abs a)
  abs _              = Nothing

  signum (Just (INT a)) = Just (INT (signum a))
  signum _              = Nothing

  fromInteger a = let a' = INT (fromInteger a)
                  in if a' >= minBound @(INTx s n) && a' <= maxBound @(INTx s n)
                     then Just a' else Nothing

instance ValidINTx s n => Real (Maybe (INTx s n)) where
  toRational (Just (INT a)) = toRational a
  toRational Nothing        = error "INTx.toRational Nothing"

instance Enum (Maybe (INTx s n)) where
  fromEnum (Just (INT a)) = fromEnum a
  fromEnum Nothing        = error "INTx.fromEnum Nothing"
  toEnum = Just . INT . toEnum

instance ValidINTx s n => Integral (Maybe (INTx s n)) where
  toInteger (Just (INT a)) = a
  toInteger Nothing        = error "INTx.fromInteger Nothing"

  quotRem _              (Just (INT 0)) = (Nothing, Nothing)
  quotRem (Just (INT a)) (Just (INT b)) = let (c, d) = quotRem a b in (Just (INT c), Just (INT d))
  quotRem _              _              = (Nothing, Nothing)

--
-- Num hierarchy classes for (INTx s n)
--

instance ValidINTx s n => Bounded (INTx s n) where
  minBound = fromJust minBound
  maxBound = fromJust maxBound

instance ValidINTx s n => Num (INTx s n) where
  a + b = fromJust (Just a + Just b)
  a - b = fromJust (Just a - Just b)
  a * b = fromJust (Just a * Just b)
  abs = fromJust . abs . Just
  signum = fromJust . signum . Just
  fromInteger = fromJust . fromInteger

instance ValidINTx s n => Real (INTx s n) where
  toRational = toRational . Just

instance ValidINTx s n => Integral (INTx s n) where
  toInteger = toInteger . Just
  quotRem a b = let (a', b') = quotRem (Just a) (Just b) in (fromJust a', fromJust b')

--
-- ABIWordValue instances
--

instance ValidINTx s n => ABIWordValue (INTx s n) where
  type instance ABIWordNBytes (INTx s n) = n
  fromWord w = let maxVal = coerce (maxBound @(INTx s n))
                   -- min = coerce (minBound @(INTx s n))
                   a  = wordToInteger w
               in if intxSign @(INTx s n)
                  then if a <= maxVal
                       then Just (INT a)
                       else let a' = a - (1 `shift` intxNBits @(INTx s n))
                            in if a' < 0 then Just (INT a') else Nothing
                  else if a <= maxVal
                       then Just (INT a)
                       else Nothing

  toWord (INT a) = if intxSign @(INTx s n)
                   then if a >= 0
                        then integerToWord a
                        else integerToWord (a + 1 `shift` intxNBits @(INTx s n))
                   else integerToWord a

--
-- Show instances
--

instance ValidINTx s n => Show (INTx s n) where
  show (INT a) = show a

------------------------------------------------------------------------------------------------------------------------
-- Assorted Fixed-Precision Integer Aliases
------------------------------------------------------------------------------------------------------------------------

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
