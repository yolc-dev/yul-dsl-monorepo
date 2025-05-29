module RaisingFund where
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude.YulDSL

-- MANDATORY MISSING FEATURES
-- - [BUG] No pure $lfn
-- - SupportedNetworks data type
-- - Time object
-- - Stunt contract creation
-- - Custom constructors

-- OPTIONAL FEATURES:
-- - ABI Binding
-- - Log emission
-- - Revert with messages
-- - Type-level Storage ACL: read-only, owner-write permission
--

object = mkYulObject "RaisingFund" yulNoop
  [ pureFn "usdcAddress" usdcAddress
  , pureFn "aaveL2PoolAddress" aaveL2PoolAddress
  , staticFn "myContribution" myContribution
  , omniFn "contribute" contribute
  ]

data SupportedNetwork'
  = BaseMainnet
  | ArbOne
  deriving Show

type SupportedNetwork = LabeledU256 SupportedNetwork'

instance IsLabledINTx SupportedNetwork' 32 where
  fromLabelToINTx = \case
    BaseMainnet -> 8453
    ArbOne -> 42161
  allINTxLabels = [BaseMainnet, ArbOne]

usdcAddress :: PureFn ADDR
usdcAddress = $lfn $ ylvm'pp $ LVM.do
  Ur chainid <- ychainid @SupportedNetwork
  MkSolo chainid `ypurelamN_1` flip match \case
    -- Reference: httpsdevelopers.circle.com/stablecoins/usdc-on-main-networks
    BaseMainnet ->  yulEmb (constAddr 0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913)
    ArbOne ->  yulEmb (constAddr 0xaf88d065e77c8cC2239327C5EDb3A432268e5831)

aaveL2PoolAddress :: PureFn ADDR
aaveL2PoolAddress = $lfn $ ylvm'pp $ LVM.do
  Ur chainid <- ychainid @SupportedNetwork
  MkSolo chainid `ypurelamN_1` flip match \case
    -- Reference: https://aave.com/docs/resources/addresses
    BaseMainnet ->  yulEmb (constAddr 0xA238Dd80C259a72e81d7e4664a9801593F98d1c5)
    ArbOne ->  yulEmb (constAddr 0x794a61358D6845594F94dc1DB02A252b5b4814aD)

contributions :: SMap (ADDR -> U256)
contributions = makeSMap "Yolc.Demo.RaisingFund.Contributions"

contribute :: OmniFn (U256 -> ())
contribute = $lfn $ ylvm'pv
  \amount -> LVM.do
    Ur usdc <- ycalluv usdcAddress
    Ur aaveL2Pool <- ycalluv aaveL2PoolAddress
    Ur this <- yaddress
    Ur me <- ycaller

    -- Tranfer fund from the user
    ycall (usdc @-> abi_ERC20_transferFrom) (ver me) (ver this) (ver amount)
    -- Approve aave pool for supply logic
    ycall (usdc @-> abi_ERC20_approve) (ver aaveL2Pool) (ver amount)
    -- Supply USDC to aave pool
    Ur referralCode <- yembed 0 -- TODO: make this inline-able
    ycall (aaveL2Pool @-> abi_AAVE_L2Pool_supply) (ver usdc) (ver amount) (ver this) referralCode

    Ur currentContribution <- sgetM $ contributions #-> me
    contributions #-> me <<:=<< (ver amount, currentContribution) `yrpurelamN_1` (\x y -> x + y)

    yembed ()

myContribution :: StaticFn U256
myContribution = $lfn $ ylvm'pv LVM.do
  Ur me <- ycaller
  sgetM $ contributions #-> me







----------------------------------------------------------------------------------------------------
-- TODO: Auto-generated ABI Bindings
----------------------------------------------------------------------------------------------------

abi_ERC20_approve = externalOmniFn
  @(ADDR {- spender -} -> U256 {- amount -} -> ())
  "approve"

abi_ERC20_transferFrom = externalOmniFn
  @(ADDR {- sender -} -> ADDR {- recipient -} -> U256 {- amount -} -> ())
  "transferFrom"

abi_AAVE_L2Pool_supply = externalOmniFn
  @(ADDR {- asset -} -> U256 {- amount -} -> ADDR {- onBehalfOf -} -> U16 {- referralCode -} -> ())
  "supply"

-- abi_AAVe_getReserveAToken = staticOmniFn
