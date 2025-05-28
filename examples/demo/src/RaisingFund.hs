module RaisingFund where
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude.YulDSL


-- MANDATORY MISSING FEATURES
-- - ABI Binding
-- - SupportedNetworks data type
-- - Stunt contract creation
-- - Custom constructors

-- OPTIONAL FEATURES:
-- - Log emission
-- - Revert with messages
-- - Type-level Storage ACL: read-only, owner-write permission
--

object = mkYulObject "RaisingFund" yulNoop
  [ staticFn "myContribution" myContribution
    --, omniFn "contribute"
  ]

data Network
  = BaseMainnet
  | ArbOne

usdcAddress :: Network -> PureFn (ADDR)
usdcAddress network = $lfn $ ylvm'pp $
  yembed
  case network of
    -- https://developers.circle.com/stablecoins/usdc-on-main-networks
    BaseMainnet ->  constAddr 0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913
    ArbOne ->  constAddr 0xaf88d065e77c8cC2239327C5EDb3A432268e5831

aaveL2PoolAddress :: Network -> PureFn (ADDR)
aaveL2PoolAddress network = $lfn $ ylvm'pp $
  yembed
  case network of
    -- References: https://aave.com/docs/resources/addresses
    BaseMainnet ->  constAddr 0xA238Dd80C259a72e81d7e4664a9801593F98d1c5
    ArbOne ->  constAddr 0x794a61358D6845594F94dc1DB02A252b5b4814aD

contributions :: SMap (ADDR -> U256)
contributions = makeSMap "Yolc.Demo.RaisingFund.Contributions"

contribute :: OmniFn (U256 -> ())
contribute = $lfn $ ylvm'pv
  \amount -> LVM.do
    Ur usdc <- ycall (usdcAddress BaseMainnet)
    Ur this <- yaddress
    Ur msgSender <- ycaller

    ycall (usdc @-> abi_ERC20_transferFrom) (ver msgSender) (ver this) (ver amount)

myContribution :: StaticFn U256
myContribution = $lfn $ ylvm'pv LVM.do
  Ur _ <- ycaller
  yembed 0

----------------------------------------------------------------------------------------------------
-- TODO: Auto-generated ABI Bindings
----------------------------------------------------------------------------------------------------

abi_ERC20_transferFrom = externalOmniFn
  @(ADDR {- sender -} -> ADDR {- recipient -} -> U256 {- amount -} -> ())
  "transferFrom"

abi_AAVE_L2Pool_supply = externalOmniFn
  @(ADDR {- asset -} -> U256 {- amount -} -> ADDR {- onBehalfOf -} -> U16 {- referralCode -} -> ())
  "supply"
