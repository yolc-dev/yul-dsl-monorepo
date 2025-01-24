{-# LANGUAGE OverloadedStrings #-}
{-|

Copyright   : (c) 2023-2024 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

Project manifest builder.

-}
module YolSuite.YOLC.Builder
  ( getCodeGenConfig
  , buildManifest
  ) where

-- base
import Data.Either                               (partitionEithers)
import Data.Functor                              ((<&>))
import Data.Maybe                                (fromJust, fromMaybe, mapMaybe)
import Data.String                               (fromString)
import System.Environment                        (lookupEnv)
-- text
import Data.Text.Lazy                            qualified as T
import Data.Text.Lazy.Encoding                   (decodeUtf8, encodeUtf8)
-- lens
import Control.Lens                              ((^..), (^?))
-- aseson
import Data.Aeson                                (KeyValue ((.=)))
import Data.Aeson                                qualified as Aeson
import Data.Aeson.Types                          qualified as AesonTypes
-- aeson-lens
import Data.Aeson.Lens                           (key, values)
-- system-process
import System.IO                                 (hClose, hGetContents', hPutStr)
import System.Process                            (CreateProcess (..), StdStream (CreatePipe), createProcess, proc)
-- yul-dsl
import YulDSL.CodeGens.YulGen
import YulDSL.Core
--
import YolSuite.YOLC.Manifest
import YolSuite.YOLC.Templates.Preamble
import YolSuite.YOLC.Templates.SingletonContract

type BuildResult = Either T.Text T.Text

getCodeGenConfig :: IO CodeGenConfig
getCodeGenConfig = (\config -> lookupEnv "YOLC_DEBUG_LEVEL" >>=
                     \case Nothing -> pure config
                           Just dbglvl -> pure (config { cg_config_debug_level = read dbglvl }))
                   defaultCodeGenConfig

-- | Compile a YulObject to bytecode.
compile_main_object :: YulObject -> IO BuildResult
compile_main_object mo = do
  let oname = yulObjectName mo
  solc <- get_solc
  cg_config <- getCodeGenConfig
  (Just hin, Just hout, _, _) <- createProcess (proc solc ["--standard-json"])
                                 { std_in = CreatePipe, std_out = CreatePipe }
  hPutStr hin (T.unpack . decodeUtf8 . Aeson.encode $ Aeson.object
               [ "language" .= ("Yul" :: String)
               , "sources"  .= Aeson.object [
                   "main.yul" .= Aeson.object [ "content" .= compileYulObject cg_config mo ]
                   ]
               , "settings" .= Aeson.object [
                   "evmVersion" .= ("paris" :: String),
                   "outputSelection" .= Aeson.object [
                       "*" .= Aeson.object [ "*" .= (["evm.bytecode.object"] :: [String])]
                       ]
                   ]
                 -- "optimizer": { "enabled": true, "details": { "yul": true } }
               ])
  hClose hin
  maybeOut :: Maybe Aeson.Value <- Aeson.decode . encodeUtf8 . T.pack <$> hGetContents' hout
  pure $ run_maybe "Failed to decode json output from solc." maybeOut
    $ \out -> run_maybe "Missing 'errors' field." (out ^? key "errors" >>= Just . (^.. values))
              $ \errors ->
                  if null errors
                  then run_maybe
                       "Missing 'contracts...evm.bytecode.object' field."
                       (out
                         ^? key "contracts"
                         >>= (^? key "main.yul")
                         >>= (^? key (fromString oname))
                         >>= (^? key "evm")
                         >>= (^? key "bytecode")
                         >>= (^? key "object"))
                       stringify
                  else Left $
                       foldr
                       (((<>)
                          . fromJust . AesonTypes.parseMaybe AesonTypes.parseJSON
                          . fromMaybe (fromString "(empty error message)")
                        )
                        . (^? key "formattedMessage")
                       )
                       (fromString "")
                       errors

ifunc_name :: AnyExportedYulCat -> Maybe T.Text
ifunc_name (MkAnyExportedYulCat (SELECTOR (_, Just (MkFuncSig fname))) fnEff (_ :: NamedYulCat eff a b))
  = Just
    $ "  function " <> T.pack fname
    <> "(" <> T.intercalate ", " argTypes <>") external" <> effect fnEff
    <> (if null retTypes then ";" else " returns (" <> T.intercalate ", " retTypes <> ");")
    where argTypes = map (T.pack . abiCoreTypeCanonName) (abiTypeInfo @a)
          retTypes = map (T.pack . abiCoreTypeCanonName) (abiTypeInfo @b)
          effect PureEffect   = " pure"
          effect StaticEffect = " view"
          effect OmniEffect   = ""
ifunc_name _ = Nothing

-- Compile interface of the build unit.
build_interface :: BuildUnit -> IO BuildResult
build_interface (MkBuildUnit { mainObject = MkYulObject
                               { yulObjectName    = oname
                               , yulObjectExports = sfns
                               } }) =
  let iname = "I" ++ oname ++ "Program"
  in pure $ Right
     (T.unlines $
      [ "interface " <> T.pack iname <> " {"
      ] ++
      mapMaybe ifunc_name sfns ++
      [
      "}"
      ])

-- Compile program of the build unit.
build_program :: BuildUnit -> IO BuildResult
build_program (MkBuildUnit { mainObject = mo }) = do
  result <- compile_main_object mo
  pure $ result <&> \bytecode ->
    let oname = yulObjectName mo
        iname = "I" ++ oname ++ "Program"
        pname = oname ++ "Program"
        bytecode' = foldr ((<>) . ("\\x" <>)) "" (T.chunksOf 2 bytecode)
    in genSingletonContract (pname, iname, bytecode')

-- Build manifest in the single-file output mode.
buildManifest :: Manifest -> IO BuildResult
buildManifest (MkManifest { buildUnits }) = do
  sections <- sequence (concatMap (\bu -> [build_interface bu, build_program bu]) buildUnits)
  let (errors, codes) = partitionEithers (Right genPreamble : sections)
  pure $ if null errors then Right (T.intercalate "\n" codes)
         else Left (T.intercalate "\n" errors)

--
-- Internal founctions
--

get_solc :: IO String
get_solc = pure "solc" -- FIXME read SOLC environment variable

run_maybe :: T.Text -> Maybe a -> (a -> BuildResult) -> BuildResult
run_maybe err  Nothing _ = Left err
run_maybe _ (Just val) f = f val

stringify :: Aeson.Value -> BuildResult
stringify val = case Aeson.fromJSON val of
  Aeson.Success str -> Right str
  Aeson.Error   err -> Left (T.pack err)
