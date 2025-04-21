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
balanceOf = $lfn $ yullvm'p
  -- NOTE on naming convention,  "*_p" means port that are still pure;
  -- use ver'l to tag version to them.
  \owner_p -> balanceMap `shmapGet` owner_p

-- | ERC20 transfer function.
transfer :: OmniFn (ADDR -> U256 -> BOOL)
transfer = $lfn $ yullvm'p \to_p amount_p -> LVM.do
  from_p <- ycaller

  -- get sender balance
  (from_p, senderBalanceRef_p) <- pass1 from_p (shmapRef balanceMap)
  -- get receiver balance
  (to_p, receiverBalanceRef_p) <- pass1 to_p (shmapRef balanceMap)

  -- calculate new balances
  let !(newSenderBalance, newReceiverBalance) = with'l @(U256 -> U256 -> U256 -> (U256, U256))
        ( ver'l amount_p
        , call balanceOf (ver'l from_p)
        , call balanceOf (ver'l to_p)
        ) \amount senderBalance receiverBalance ->
            be (senderBalance - amount, receiverBalance + amount)

  sputs $
    senderBalanceRef_p   := newSenderBalance   :|
    receiverBalanceRef_p := newReceiverBalance :[]

  -- always return true as a silly urban-legendary ERC20 convention
  embed true

-- | Mint new tokens
mint :: OmniFn (ADDR -> U256 -> ())
mint = $lfn $ yullvm'p \to_p amount_p -> LVM.do
  -- fetch balance of the account
  (to_p, balanceBefore) <- pass1 to_p \to_p -> ycall balanceOf (ver'l to_p)

  -- use linear port values safely
  (to_p, amount_p) <- passN_ (to_p, amount_p) \(to_p, amount_p) ->
    -- update balance
    shmapPut balanceMap to_p (balanceBefore + ver'l amount_p)

  -- call unsafe external contract onTokenMinted
  let !(to_p1, to_p2) = dup'l (ver'l to_p)
  externalCall onTokenMinted to_p1 to_p2 (ver'l amount_p)

--
-- TODO: this should/could be generated from a solidity interface definition file:
-- | A hook to the token minted event for the mint receiver.
onTokenMinted = declareExternalFn @(ADDR -> U256 -> ()) "onTokenMinted"
