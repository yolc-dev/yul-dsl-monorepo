module ERC20 where
import Control.LinearlyVersionedMonad qualified as LVM
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
balanceOf = $lfn $ yulmonad'p
  -- NOTE on naming convention,  "*_p" means port that are still pure;
  -- use ver'l to tag version to them.
  \owner_p -> balanceMap `shmapGet` owner_p

-- | ERC20 transfer function.
transfer :: OmniFn (ADDR -> ADDR -> U256 -> BOOL)
transfer = $lfn $ yulmonad'p \from_p to_p amount_p -> LVM.do
  -- get sender balance
  (from_p, senderBalanceRef_p) <- pass from_p (shmapRef balanceMap)
  -- get receiver balance
  (to_p, receiverBalanceRef_p) <- pass to_p (shmapRef balanceMap)
  -- calculate new balances
  (amount, newSenderBalance) <- pass (ver'l amount_p)
    \amount -> ypure $ call balanceOf (ver'l from_p) - amount
  let newReceiverBalance = call balanceOf (ver'l to_p) + amount
  -- update storages
  sputs $
    senderBalanceRef_p   := newSenderBalance   :|
    receiverBalanceRef_p := newReceiverBalance :[]
  -- always return true as a silly urban-legendary ERC20 convention
  embed true

-- | Mint new tokens
mint :: OmniFn (ADDR -> U256 -> ())
mint = $lfn $ yulmonad'p \to_p amount_p -> LVM.do
  -- fetch balance of the account
  (to_p, balanceBefore) <- pass to_p \to_p ->
    ypure $ balanceOf `call` ver'l to_p

  -- use linear port values safely
  (to_p, amount_p) <- passN_ (to_p, amount_p) \(to_p, amount_p) ->
    -- update balance
    shmapPut balanceMap to_p (balanceBefore + ver'l amount_p)

  -- call unsafe external contract onTokenMinted
  externalCall onTokenMinted (ver'l to_p) (ver'l amount_p)

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = declareExternalFn @(U256 -> ()) "onTokenMinted"
