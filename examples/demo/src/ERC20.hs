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
balanceOf = $lfn $ yullvm'pv \(Uv owner) -> balanceMap `shmapGet` owner

-- | ERC20 transfer function.
-- (TODO: refactor using LVMVar ongoing; it will be just few lines!)
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ yullvm'pv
  \(Uv to) (Uv amount) -> LVM.do
    Uv from <- ymkref LVM.=<< ycaller

    -- get sender balance storage reference
    Uv senderBalanceRef <- shmapRef balanceMap from

    -- get receiver balance storage reference
    Uv receiverBalanceRef <- shmapRef balanceMap to

    -- calculate new balances
    (newSenderBalance'rv, newReceiverBalance'rv) <- LVM.do
      amount_v <- ytakev1 amount
      from_v <- ytakev1 from
      to_v <- ytakev1 to

      let !(newSenderBalance, newReceiverBalance) = with'l @(U256 -> U256 -> U256 -> (U256, U256))
            ( amount_v
            , call balanceOf from_v
            , call balanceOf to_v
            ) \amount' senderBalance' receiverBalance' ->
                be (senderBalance' - amount', receiverBalance' + amount')

      Rv newSenderBalance'rv <- ymkref newSenderBalance
      Rv newReceiverBalance'rv <- ymkref newReceiverBalance

      LVM.pure (newSenderBalance'rv, newReceiverBalance'rv)

    -- update storages
    sputs $
      senderBalanceRef   := newSenderBalance'rv   :|
      receiverBalanceRef := newReceiverBalance'rv :[]

    -- always return true as a silly urban-legendary ERC20 convention
    yembed true

-- | Mint new tokens
-- (TODO: refactor using LVMVar ongoing; it will be just few lines!)
mint :: OmniFn (ADDR -> U256 -> ())
mint = $lfn $ yullvm'pv
  \(Uv to) (Uv amount) -> LVM.do
    -- fetch balance of the account
    Rv balanceBefore <- LVM.do
      to_v <- ytakev1 to
      ymkref LVM.=<< ycall balanceOf to_v

    -- update balance
    LVM.do
      (MkSolo (Rv newAmount)) <- ywithAny @(U256 -> U256 -> Solo U256)
                                    (AnyRv balanceBefore, AnyUv amount)
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
