module ERC20 where
import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude.YulDSL

-- | Ethereum contract is a Yul Object in Yolc.
object = mkYulObject "ERC20" yulNoop
  [ staticFn "balanceOf" balanceOf
  , omniFn   "transfer"  transfer
  , omniFn   "mint"      mint
  ]

-- | Storage map of account balances
balanceMap :: SHMap ADDR U256
balanceMap = shmap "Yolc.Demo.ERC20.Storage.AccountBalance"

-- | ERC20 balance of the account.
balanceOf :: StaticFn (ADDR -> U256)
balanceOf = $lfn $ ylvm'pv \owner -> shmapGet balanceMap owner

-- | ERC20 transfer function.
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ ylvm'pv
  \to amount -> LVM.do
    Ur from <- ycaller

    -- get current balances
    Ur senderBalance <- ycall balanceOf (ver from)
    Ur receiverBalance <- ycall balanceOf (ver to)

    -- calculate new balances
    Ur (newSenderBalance, newReceiverBalance) <- ywithrv
      @(U256 -> U256 -> U256 -> (U256, U256))
      (ver amount, senderBalance, receiverBalance)
      \amount' senderBalance' receiverBalance' ->
        be (senderBalance' - amount', receiverBalance' + amount')

    -- WARNING: THIS IS WRONG, we shouldn't batch like this, and it violats data freshness.
    -- Have you found the issue?
    --
    -- It will be fixed; by removing sputs.
    sputs $
      balanceMap .-> from := newSenderBalance   :|
      balanceMap .-> to   := newReceiverBalance :[]

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
    -- update balance
    sputs $ balanceMap .-> to := newAmount :|[]
    -- call **untrusted** external contract onTokenMinted
    ycall (to @-> onTokenMinted) (ver to) (ver amount)

    -- return () always, for demo purpose
    yembed ()

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = externalOmniFn @(ADDR -> U256 -> ()) "onTokenMinted"
