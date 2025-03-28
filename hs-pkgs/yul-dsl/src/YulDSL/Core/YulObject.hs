{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

Yul object builder. Yul object specification can be found from [solidity
documentation](https://docs.soliditylang.org/en/latest/yul.html#specification-of-yul-object).

-}
module YulDSL.Core.YulObject
  (-- $AnyExportedYulCat
    AnyExportedYulCat (MkAnyExportedYulCat), withAnyExportedYulCat
  , pureFn, staticFn, omniFn
    -- $YulObject
  , YulObject (..), mkYulObject
  ) where
-- base
import Data.List                                  (intercalate)
-- simple-sop
import Data.Type.Function
-- eth-abi
import Ethereum.ContractABI.ABITypeable           (abiTypeCanonName)
import Ethereum.ContractABI.CoreType.NP
import Ethereum.ContractABI.ExtendedType.SELECTOR
--
import YulDSL.Core.YulCat
import YulDSL.Core.YulCatObj


------------------------------------------------------------------------------------------------------------------------
-- $AnyExportedYulCat

-- | Existential type wrapper for yul function that is exported.
data AnyExportedYulCat where
  MkAnyExportedYulCat :: forall k { eff :: k } xs b. YulO2 (NP xs) b
                      => SELECTOR -> YulCatEffectClass -> NamedYulCat eff (NP xs) b -> AnyExportedYulCat

-- | The function to process the content of 'AnyExportedYulCat'.
withAnyExportedYulCat :: AnyExportedYulCat
  -> (forall k { eff :: k } xs b. (YulO2 (NP xs) b ) => NamedYulCat eff (NP xs) b -> a)
  -> a
withAnyExportedYulCat (MkAnyExportedYulCat _ _ f) g = g f

pureFn :: forall fn f xs b efc.
  ( ClassifiedFn fn efc
  , efc ~ PureEffect
  , EquivalentNPOfFunction f xs b
  , YulO2 (NP xs) b
  ) => String -> fn f -> AnyExportedYulCat
pureFn fname = withClassifiedFn (MkAnyExportedYulCat (mkTypedSelector @(NP xs) fname) PureEffect . unFn)

staticFn :: forall fn f xs b efc.
  ( ClassifiedFn fn efc
  , efc ~ StaticEffect
  , EquivalentNPOfFunction f xs b
  , YulO2 (NP xs) b
  ) => String -> fn f -> AnyExportedYulCat
staticFn fname = withClassifiedFn (MkAnyExportedYulCat (mkTypedSelector @(NP xs) fname) StaticEffect . unFn)

omniFn :: forall fn f xs b efc.
  ( ClassifiedFn fn efc
  , efc ~ OmniEffect
  , EquivalentNPOfFunction f xs b
  , YulO2 (NP xs) b
  ) => String -> fn f -> AnyExportedYulCat
omniFn fname = withClassifiedFn (MkAnyExportedYulCat (mkTypedSelector @(NP xs) fname) OmniEffect . unFn)

instance Show AnyExportedYulCat where
  show (MkAnyExportedYulCat s PureEffect   cat) = "pure "   <> show_fn_spec s cat
  show (MkAnyExportedYulCat s StaticEffect cat) = "static " <> show_fn_spec s cat
  show (MkAnyExportedYulCat s OmniEffect   cat) = "omni "   <> show_fn_spec s cat

show_fn_spec :: forall xs b eff. YulO2 (NP xs) b
             => SELECTOR -> NamedYulCat eff (NP xs) b -> String
show_fn_spec (SELECTOR (sel, fsig)) cat@(cid, _) =
  let fspec = case fsig of
                Just (MkFuncSig fname) -> fname ++ "," ++ show sel ++ "," ++ cid
                Nothing                -> show sel ++ "," ++ cid
  in "fn " <> fspec <> "(" <> abiTypeCanonName @(NP xs) <> ") -> " <> abiTypeCanonName @b <> "\n" <>
     show cat

------------------------------------------------------------------------------------------------------------------------
-- $YulObject

-- | A Yul Object per spec.
--
-- Note:
--   * Do not confuse this with 'YulCatObj' which is for "objects" in the category of 'YulCat'.
--   * Specification: https://docs.soliditylang.org/en/latest/yul.html#specification-of-yul-object
data YulObject = MkYulObject { yulObjectName    :: String              -- ^ object name
                             , yulObjectCtor    :: AnyYulCat           -- ^ constructor
                             , yulObjectExports :: [AnyExportedYulCat] -- ^ list of exported yul functions
                             , yulSubObjects    :: [YulObject]         -- ^ dependent objects
                             -- , TODO support object data
                             }

instance Show YulObject where
  show o = "-- Functions:\n\n"
           <> intercalate "\n\n" (fmap show (yulObjectExports  o))
           <> "\n\n-- Init code:\n\n"
           <> (show . yulObjectCtor) o

mkYulObject :: String
            -> AnyYulCat
            -> [AnyExportedYulCat]
            -> YulObject
mkYulObject name ctor afns = MkYulObject { yulObjectName    = name
                                         , yulObjectCtor    = ctor
                                         , yulObjectExports = afns
                                         , yulSubObjects    = []
                                         }
