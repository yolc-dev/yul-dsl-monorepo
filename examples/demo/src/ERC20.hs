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
-- (TODO: refactor using LVMVar ongoing)
balanceOf :: StaticFn (ADDR -> U256)
balanceOf = $lfn $ yullvm'pv
  \(Uv owner'uv) -> LVM.do
    owner_p <- ytake1 owner'uv
    balance <- balanceMap `shmapGet` owner_p
    Ur balanceRef <- ymkref balance
    LVM.pure balanceRef

-- | ERC20 transfer function.
-- (TODO: refactor using LVMVar ongoing; it will be just few lines!)
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ yullvm'pv
  \(Uv to'uv) (Uv amount'uv) -> LVM.do
    Ur (Uv from'uv) <- LVM.do
      from_p <- ycaller
      ymkref from_p

    -- get sender balance storage reference
    senderBalanceRef_p <- LVM.do
      from_p <- ytake1 from'uv
      shmapRef balanceMap from_p

    -- get receiver balance storage reference
    receiverBalanceRef_p <- LVM.do
      to_p <- ytake1 to'uv
      shmapRef balanceMap to_p

    -- calculate new balances
    LVM.do
      amount <- ytakev1 amount'uv
      from <- ytakev1 from'uv
      to <- ytakev1 to'uv
      let !(newSenderBalance, newReceiverBalance) = with'l @(U256 -> U256 -> U256 -> (U256, U256))
            ( amount
            , call balanceOf from
            , call balanceOf to
            ) \amount senderBalance receiverBalance ->
                be (senderBalance - amount, receiverBalance + amount)

      sputs $
        senderBalanceRef_p   := newSenderBalance   :|
        receiverBalanceRef_p := newReceiverBalance :[]

    -- always return true as a silly urban-legendary ERC20 convention
    yembed true

-- | Mint new tokens
-- (TODO: refactor using LVMVar ongoing; it will be just few lines!)
mint :: OmniFn (ADDR -> U256 -> ())
mint = $lfn $ yullvm'pv
  \(Uv to'uv) (Uv amount'uv) -> LVM.do
    -- fetch balance of the account
    balanceBefore <- LVM.do
      to <- ytakev1 to'uv
      ycall balanceOf to

    -- update balance
    LVM.do
      to_p <- ytake1 to'uv
      amount <- ytakev1 amount'uv
      let !(MkSolo newAmount) = with'l @(U256 -> U256 -> Solo U256) (balanceBefore, amount) (\x y -> be (x + y))
      shmapPut balanceMap to_p newAmount

    -- call unsafe external contract onTokenMinted
    LVM.do
      to_p1 <- ytake1 to'uv
      to_p2 <- ytake1 to'uv
      amount <- ytakev1 amount'uv
      externalCall onTokenMinted to_p1 (ver'l to_p2) amount

    yembed ()

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = declareExternalFn @(ADDR -> U256 -> ()) "onTokenMinted"
