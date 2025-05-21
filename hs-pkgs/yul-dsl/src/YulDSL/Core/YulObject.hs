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
import Data.List                        (intercalate)
-- eth-abi
import Ethereum.ContractABI.ABITypeable (abiTypeCanonName)
import Ethereum.ContractABI.CoreType.NP
--
import YulDSL.Core.YulCallSpec
import YulDSL.Core.YulCat
import YulDSL.Core.YulCatObj
import YulDSL.Core.YulEffect


------------------------------------------------------------------------------------------------------------------------
-- $AnyExportedYulCat

-- | Existential type wrapper for yul function that is exported.
data AnyExportedYulCat where
  MkAnyExportedYulCat :: forall k { eff :: k } xs b. YulO2 (NP I xs) b
                      => Selector -> YulCatEffectClass -> NamedYulCat eff (NP I xs) b -> AnyExportedYulCat

-- | The function to process the content of 'AnyExportedYulCat'.
withAnyExportedYulCat :: AnyExportedYulCat
  -> (forall k { eff :: k } xs b. (YulO2 (NP I xs) b ) => NamedYulCat eff (NP I xs) b -> a)
  -> a
withAnyExportedYulCat (MkAnyExportedYulCat _ _ f) g = g f

pureFn :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP I xs) b
  , efc ~ PureEffect
  , YulO2 (NP I xs) b
  ) => String -> fn -> AnyExportedYulCat
pureFn fname fn = withKnownNamedYulCat fn (MkAnyExportedYulCat (mkTypedSelector @(NP I xs) fname) PureEffect)

staticFn :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP I xs) b
  , efc ~ StaticEffect
  , YulO2 (NP I xs) b
  ) => String -> fn -> AnyExportedYulCat
staticFn fname fn = withKnownNamedYulCat fn (MkAnyExportedYulCat (mkTypedSelector @(NP I xs) fname) StaticEffect)

omniFn :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP I xs) b
  , efc ~ OmniEffect
  , YulO2 (NP I xs) b
  ) => String -> fn -> AnyExportedYulCat
omniFn fname fn = withKnownNamedYulCat fn (MkAnyExportedYulCat (mkTypedSelector @(NP I xs) fname) OmniEffect)

instance Show AnyExportedYulCat where
  show (MkAnyExportedYulCat s PureEffect   cat) = "pure "   <> show_fn_spec s cat
  show (MkAnyExportedYulCat s StaticEffect cat) = "static " <> show_fn_spec s cat
  show (MkAnyExportedYulCat s OmniEffect   cat) = "omni "   <> show_fn_spec s cat

show_fn_spec :: forall xs b eff. YulO2 (NP I xs) b
             => Selector -> NamedYulCat eff (NP I xs) b -> String
show_fn_spec (MkSelector (sel, fsig)) cat@(cid, _) =
  let fspec = case fsig of
                Just (MkFuncSig fname) -> fname ++ "," ++ show sel ++ "," ++ cid
                Nothing                -> show sel ++ "," ++ cid
  in "fn " <> fspec <> "(" <> abiTypeCanonName @(NP I xs) <> ") -> " <> abiTypeCanonName @b <> "\n" <>
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
