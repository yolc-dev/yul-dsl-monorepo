module ERC20 where
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude.YulDSL

-- | Ethereum contract is a Yul Object in Yolc.
object = mkYulObject "ERC20" yulNoop
  [ staticFn "balanceOf" balanceOf
  , staticFn "allowance" allowance
  , omniFn   "transfer"  transfer
  , omniFn   "mint"      mint
  ]

-- | Storage map of account balances
balances :: SMap (ADDR -> U256)
balances = makeSMap "Yolc.Demo.ERC20.Storage.AccountBalances"

-- | ERC20 balance of the account.
balanceOf :: StaticFn (ADDR -> U256)
balanceOf = $lfn $ ylvm'pv \owner -> sgetM $ balances #-> owner

-- | Storage map of allowances
allowances :: SMap (ADDR {- Owner -} -> ADDR {- spender -} -> U256)
allowances = makeSMap "Yolc.Demo.ERC20.Storage.Allowances"

-- | ERC20 allowance function.
allowance :: StaticFn (ADDR -> ADDR -> U256)
allowance = $lfn $ ylvm'pv
  \owner spender -> sgetM $ allowances #-> (owner, spender)

-- | ERC20 transfer function.
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ ylvm'pv
  \to amount -> LVM.do
    Ur from <- ycaller

    -- ✅ CORRECT CODE:

    Ur senderBalance <- ycall balanceOf (ver from)
    Ur newSenderBalance <- yrpurelamN_1 (ver amount, senderBalance)
      \amount' senderBalance' ->
        if senderBalance' >= amount' then senderBalance' - amount'
        else yulRevert
    balances #-> from <<:= newSenderBalance

    Ur receiverBalance <- ycall balanceOf (ver to)
    Ur newReceiverBalance <- yrpurelamN_1 (ver amount, receiverBalance) \x y -> x + y
    balances #-> to <<:= newReceiverBalance

    -- ⛔ INCORRECT CODE, CANNOT PASS COMPILATION:

    -- Ur senderBalance <- ycall balanceOf (ver from)
    -- Ur receiverBalance <- ycall balanceOf (ver to)

    -- -- calculate new balances
    -- Ur (newSenderBalance, newReceiverBalance) <- yrpurelamN
    --   (ver amount, senderBalance, receiverBalance)
    --   \amount' senderBalance' receiverBalance' ->
    --     be (senderBalance' - amount', receiverBalance' + amount')

    -- -- WARNING: THIS IS WRONG
    -- -- Have you found the issue?
    -- balances #-> from <<:= newSenderBalance
    -- balances #-> to   <<:= newReceiverBalance

    -- always return true as a silly urban-legendary ERC20 convention
    yembed true

-- | Mint new tokens
mint :: OmniFn (ADDR -> U256 -> ())
mint = $lfn $ ylvm'pv
  -- [solidity] function mint(address to, uint256 amount) returns ()
  \to amount -> LVM.do
    -- [solidity] uint256 balanceBefore = balanceOf(to)
    Ur balanceBefore <- ycall balanceOf (ver to)

    -- calculate new balance
    -- [solidity] uint256 newAmount = balanceBefore + amount
    Ur newAmount <- yrpurelamN_1 (balanceBefore, ver amount) \x y -> x + y

    --
    -- ⚠️ NOTE: swap the following code blocks will not compile, because there can be reentrance!

    -- update balance
    -- [solidity] balances[to] = newAmount
    balances #-> to <<:= newAmount

    -- call **untrusted** external contract onTokenMinted
    -- [solidity] TokenMintHook(to).onTokenMinted(to, amount)
    ycall (to @-> onTokenMinted) (ver to) (ver amount)

    -- return () always, for demo purpose
    yembed ()

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = externalOmniFn @(ADDR -> U256 -> ()) "onTokenMinted"
