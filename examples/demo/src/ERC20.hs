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
allowance = $lfn $ ylvm'pv \owner spender -> sgetM $ allowances #-> (owner, spender)

-- | ERC20 transfer function.
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ ylvm'pv
  \to amount -> LVM.do
    Ur from <- ycaller

    -- CORRECT CODE:

    Ur senderBalance <- ycall balanceOf (ver from)
    Ur newSenderBalance <- ywithrv_1 @(U256 -> U256 -> U256) (ver amount, senderBalance)
      \amount' senderBalance' -> senderBalance' - amount'
    balances #-> from <<:= newSenderBalance

    Ur receiverBalance <- ycall balanceOf (ver to)
    Ur newReceiverBalance <- ywithrv_1 @(U256 -> U256 -> U256) (ver amount, receiverBalance)
      \amount' receiverBalance' -> receiverBalance' + amount'
    balances #-> to <<:= newReceiverBalance

    -- ⛔ INCORRECT CODE, CANNOT PASS COMPILATION:

    -- Ur senderBalance <- ycall balanceOf (ver from)
    -- Ur receiverBalance <- ycall balanceOf (ver to)

    -- -- calculate new balances
    -- Ur (newSenderBalance, newReceiverBalance) <- ywithrv
    --   @(U256 -> U256 -> U256 -> (U256, U256))
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
  \to amount -> LVM.do
    Ur balanceBefore <- ycall balanceOf (ver to)

    -- calculate new balance
    Ur newAmount <- ywithrv_1 @(U256 -> U256 -> U256)
      (balanceBefore, ver amount)
      (\x y -> x + y)

    -- ⚠️ NOTE: swap the following code blocks will not compile, because there can be reentrance!

    -- update balance
    balances #-> to <<:= newAmount

    -- call **untrusted** external contract onTokenMinted
    ycall (to @-> onTokenMinted) (ver to) (ver amount)

    -- return () always, for demo purpose
    yembed ()

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = externalOmniFn @(ADDR -> U256 -> ()) "onTokenMinted"
