{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

= Description

All derived types and dependent types are mapped to the underlying core types, such that you only need to work with
contract ABI types to support the entire contract ABI specification.

-}
module Ethereum.ContractABI.ABICoreType
  ( ABICoreType (..)
  -- for working with INTx, BYTEn
  , SNat, Nat, natSing, natVal, fromSNat
  , ValidINTn, fromValidINTn, withSomeValidINTx
  -- ABI type names
  , abiCoreTypeCanonName
  , abiCoreTypeCompactName, decodeAbiCoreTypeCompactName
  -- EVM word representations
  , WORD, integerToWord, wordToInteger, defWord, maxWord
  , ABIWordValue (ABIWordNBytes, toWord, fromWord)
  ) where

-- base
import Control.Exception            (assert)
import Data.Char                    (isDigit)
import Data.Coerce                  (coerce)
import GHC.TypeLits
    ( KnownNat (natSing)
    , Nat
    , SNat
    , fromSNat
    , natVal
    , type (<=)
    , withKnownNat
    , withSomeSNat
    )
import Numeric                      (showHex)
import Text.ParserCombinators.ReadP qualified as RP
-- template-haskell
import Language.Haskell.TH          qualified as TH
-- constraints
import Data.Constraint              (Dict, (\\))
import Data.Constraint.Unsafe       (unsafeAxiom)
--
import Internal.Data.Type.Bool


{- * ABICoreType and their utilities -}

-- | Contract ABI core types.
data ABICoreType where
  -- ^ Boolean
  BOOL'   :: ABICoreType
  -- ^ Fixed-precision integers
  INTx'   :: forall s n. (KnownBool s, ValidINTn n) => SBool s -> SNat n -> ABICoreType
  -- ^ Ethereum addresses
  ADDR'   :: ABICoreType
  -- ^ Fixed-size byte arrays
  BYTESn' :: forall n. (ValidINTn n) => SNat n -> ABICoreType
  -- ^ Arrays of values of the same ABI core type
  ARRAY'  :: ABICoreType -> ABICoreType

instance Eq ABICoreType where
  BOOL'       == BOOL'         = True
  (INTx' s n) == (INTx' s' n') = fromSBool s == fromSBool s' && fromSNat n == fromSNat n'
  ADDR'       == ADDR'         = True
  (BYTESn' n) == (BYTESn' n')  = fromSNat n == fromSNat n'
  (ARRAY' a)  == (ARRAY' b)    = a == b
  -- not using _ == _ in order to let GHC do exhaustive checks on cases above
  BOOL'       == _             = False
  (INTx' _ _) == _             = False
  ADDR'       == _             = False
  (BYTESn' _) == _             = False
  (ARRAY' _)  == _             = False

-- | A constraint that restricts what Nat values are valid for 'INTx' and 'BYTESn'.
--   Note: It is valid from 1 to 32.
type ValidINTn n = (KnownNat n, ValidINTn_ n)

-- | From ValidINTn to Int value.
fromValidINTn :: forall n. ValidINTn n => Int
fromValidINTn = fromInteger . fromSNat $ natSing @n

-- | A helper constraint to avoid KnownNat to be super class which may cause issues when unsafeAxiom.
class ValidINTn_ n

-- | A top-level splice that declares all the valid INTx n values.
flip foldMap [1 .. 32] $ \i -> [d| instance ValidINTn_ $(TH.litT (TH.numTyLit i)) |]

-- | Work with the INTx signedness and data byte-size during runtime.
withSomeValidINTx :: forall r. ()
                  => Bool -> Integer
                  -> (forall s n. (KnownBool s, ValidINTn n, 1 <= n, n <= 32) => SBool s -> SNat n -> r)
                  -> Maybe r
withSomeValidINTx sval nval f =
  toKnownSBool sval $ \s ->
  withSomeSNat nval $ \maybeSn -> maybeSn >>=
  \sn -> withSomeValidINTn sn >>=
  \validINTn -> withKnownNat sn (Just (f s sn) \\ validINTn)
  where withSomeValidINTn :: forall n. SNat n -> Maybe (Dict (ValidINTn_ n, 1 <= n, n <= 32))
        withSomeValidINTn sn = let n = fromSNat sn
                               in if n >= 1 && n <= 32 then Just unsafeAxiom else Nothing

-- | Canonical names for the core types used for computing the function selectors.
abiCoreTypeCanonName :: ABICoreType -> String
abiCoreTypeCanonName BOOL'       = "bool"
abiCoreTypeCanonName (INTx' s n) = (if fromSBool s then "int" else "uint") <> show (natVal n * 8)
abiCoreTypeCanonName ADDR'       = "address"
abiCoreTypeCanonName (BYTESn' n) = "bytes" ++ show (natVal n)
abiCoreTypeCanonName (ARRAY' a)  = abiCoreTypeCanonName a ++ "[]"

-- | Compact but unambiguous names for the core types..
abiCoreTypeCompactName :: ABICoreType -> String
abiCoreTypeCompactName BOOL'       = "b"
abiCoreTypeCompactName (INTx' s n) = (if fromSBool s then "i" else "u") <> show (natVal n)
abiCoreTypeCompactName ADDR'       = "a"
abiCoreTypeCompactName (BYTESn' n) = "B" ++ show (natVal n)
abiCoreTypeCompactName (ARRAY' a)  = "[" ++ abiCoreTypeCompactName a ++ "]"

-- | Decode result from 'abiCoreTypeCompactName'.
decodeAbiCoreTypeCompactName :: String -> [ABICoreType]
decodeAbiCoreTypeCompactName part = case results of
  [(rs, "")] -> rs
  []         -> error ("Invalid abiCoreTypeCompactName, no match: " ++ part)
  xs         -> error ("Invalid abiCoreTypeCompactName, non-unique match: " ++ show xs)
  where parseOne = do
          a <- RP.get
          case a of
            'b' -> pure BOOL'
            'i' -> parseINTx True
            'u' -> parseINTx False
            'a' -> pure ADDR'
            '[' -> do
              a' <- parseOne
              _ <- RP.char ']'
              pure (ARRAY' a')
            _ -> RP.pfail
        parseINTx s = do
          digits <- RP.many1 $ RP.satisfy isDigit
          maybe RP.pfail pure (withSomeValidINTx s (read digits) INTx')
        results = RP.readP_to_S (RP.manyTill parseOne RP.eof) part

instance Show ABICoreType where show = abiCoreTypeCanonName

{- * EVM word representations  -}

-- | Raw storage value for ABI value types.
newtype WORD = WORD Integer deriving newtype (Eq)

instance Show WORD where
  show (WORD a) = "0x" ++ showHex a ""

-- | Convert from an integer to a word.
integerToWord :: Integer -> WORD
integerToWord a = assert (a >= 0 && a <= coerce maxWord) WORD a

-- | Convert to an integer from a word.
wordToInteger :: WORD -> Integer
wordToInteger = coerce

-- | Default and minimum word value: 0.
defWord :: WORD
defWord = WORD 0

-- | Maximum word value: 2^256 - 1.
maxWord :: WORD
maxWord = WORD (2 ^ (256 :: Int) - 1)

-- | ABI values that can be stored in one word.
class Bounded a => ABIWordValue a where
  -- | Number of bytes the ABI word requires.
  type family ABIWordNBytes a :: Nat
  -- | Convert from a storage value to an ABI typed value.
  fromWord :: WORD -> Maybe a
  -- | Convert from a ABI typed value to a storage value.
  toWord :: a -> WORD
