module ABITypeCodec_golden where
-- base
import Control.Exception    (assert)
import Data.Maybe           (fromJust, isJust)
import Data.Word            (Word8)
import Debug.Trace          (trace)
import Numeric              (readHex)
import Text.Printf          (printf)
-- bytestring
import Data.ByteString      qualified as BS
-- hspec, QuickCheck
import Test.Hspec
--
import Ethereum.ContractABI


test_value_types :: Bool
test_value_types = and
  [ -- cast abi-encode "f(int256)" 42
    test_f "u256" (42 :: U256) (align_ethword '0' "2a")
  , test_f "i8 pos" (127 :: I8) (align_ethword '0' "7f")
  , test_f "i8 neg" (fromInteger (-128) :: I8) (align_ethword 'f' "80")
  ]

tests = describe "ABITypeCodec golden" $
  it "Value types" test_value_types

------------------------------------------------------------------------------------------------------------------------

align_ethword :: Char -> String -> String
align_ethword c hex = let n = length hex in assert (n < 64) (replicate (64 - n) c) <> hex

bs2hex :: BS.ByteString -> [Char]
bs2hex = concatMap (printf "%02x") . BS.unpack

hex2word8 :: (Char, Char) -> Word8
hex2word8 (c1, c2) = case readHex [c1, c2] of [(w, [])] -> w; _ -> error "hex2word: bad hex string"

hex2word8s :: [Char] -> [Word8]
hex2word8s (c1:c2:cs) = hex2word8 (c1, c2) : hex2word8s cs
hex2word8s (_:_)      = error "hex2words: bad hex string"
hex2word8s []         = []

hex2bs :: [Char] -> BS.ByteString
hex2bs = BS.pack . hex2word8s

trace_bool :: Bool -> String -> Bool
trace_bool b msg = b || trace msg False

test_f :: forall a. ABITypeCodec a => String -> a -> String -> Bool
test_f label a expected =
  trace_bool ((bs2hex a') == expected) (label ++ " #1: " ++ bs2hex a' ++ " /= " ++ expected) &&
  trace_bool (isJust a'') (label ++ " #2: abiDecode fails") &&
  trace_bool (a''' == a') (label ++ " #3: " ++ bs2hex a''')
  where a' = abiEncode a
        a'' = abiDecode a'
        a''' = abiEncode @a (fromJust a'')
