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
  , ValidINTn
  -- ABI type names
  , abiCoreTypeCompactName
  -- EVM word representations
  ) where

-- base
import Control.Exception            (assert)
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

instance Eq ABICoreType where
  BOOL'       == BOOL'         = True
  (INTx' s n) == (INTx' s' n') = fromSBool s == fromSBool s' && fromSNat n == fromSNat n'
  ADDR'       == ADDR'         = True
  (BYTESn' n) == (BYTESn' n')  = fromSNat n == fromSNat n'
  -- not using _ == _ in order to let GHC do exhaustive checks on cases above
  BOOL'       == _             = False
  (INTx' _ _) == _             = False
  ADDR'       == _             = False
  (BYTESn' _) == _             = False

-- | A constraint that restricts what Nat values are valid for 'INTx' and 'BYTESn'.
--   Note: It is valid from 1 to 32.
type ValidINTn n = (KnownNat n, ValidINTn_ n)

-- | From ValidINTn to Int value.
-- | A helper constraint to avoid KnownNat to be super class which may cause issues when unsafeAxiom.
class ValidINTn_ n

-- | A top-level splice that declares all the valid INTx n values.
flip foldMap [1 .. 32] $ \i -> [d| instance ValidINTn_ $(TH.litT (TH.numTyLit i)) |]

-- | Compact but unambiguous names for the core types..
abiCoreTypeCompactName :: ABICoreType -> String
abiCoreTypeCompactName BOOL'       = "b"
abiCoreTypeCompactName (INTx' s n) = (if fromSBool s then "i" else "u") <> show (natVal n)
abiCoreTypeCompactName ADDR'       = "a"
abiCoreTypeCompactName (BYTESn' n) = "B" ++ show (natVal n)
