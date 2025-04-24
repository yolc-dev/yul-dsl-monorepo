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
balanceOf = $lfn $ ylvm'pv \(Uv owner) -> balanceMap `shmapGet` owner

-- | ERC20 transfer function.
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ ylvm'pv
  \(Uv to) (Uv amount) -> LVM.do
    Uv from <- ymkref LVM.=<< ycaller
    -- get sender balance storage reference
    Uv senderBalanceRef <- shmapRef balanceMap from
    -- get receiver balance storage reference
    Uv receiverBalanceRef <- shmapRef balanceMap to
    -- get current balances
    Rv senderBalance <- ycall balanceOf (ver from)
    Rv receiverBalance <- ycall balanceOf (ver to)

    -- calculate new balances
    (Rv newSenderBalance, Rv newReceiverBalance) <- ywithrv_N @(U256 -> U256 -> U256 -> (U256, U256))
      (ver amount, Rv senderBalance, Rv receiverBalance)
      \amount' senderBalance' receiverBalance' ->
        be (senderBalance' - amount', receiverBalance' + amount')

    -- update storages
    sputs $
      senderBalanceRef   := newSenderBalance   :|
      receiverBalanceRef := newReceiverBalance :[]

    -- always return true as a silly urban-legendary ERC20 convention
    yembed true

-- | Mint new tokens
mint :: OmniFn (ADDR -> U256 -> ())
mint = $lfn $ ylvm'pv
  \(Uv to) (Uv amount) -> LVM.do
    Rv balanceBefore <- ycall balanceOf (ver to)

    -- update balance
    LVM.do
      (MkSolo (Rv newAmount)) <- ywithrv_N @(U256 -> U256 -> Solo U256)
                                 (Rv balanceBefore, ver amount)
                                 (\x y -> be (x + y))
      shmapPut balanceMap to newAmount

    -- call unsafe external contract onTokenMinted
    LVM.do
      to_p1 <- ytake1 to
      to_p2 <- ytake1 to
      amount_v <- ytakev1 amount
      externalCall onTokenMinted to_p1 (ver'l to_p2) amount_v

    yembed ()

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = declareExternalFn @(ADDR -> U256 -> ()) "onTokenMinted"
