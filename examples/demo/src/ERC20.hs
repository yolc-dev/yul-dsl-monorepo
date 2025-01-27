module ERC20 where
import Control.LinearlyVersionedMonad qualified as LVM
import Prelude.YulDSL

-- | Ethereum contract is a Yul Object in Yolc.
object = mkYulObject "ERC20" emptyCtor
  [ staticFn "balanceOf" balanceOf
  , omniFn   "transfer"  transfer
  , omniFn   "mint"      mint
  ]

-- | ERC20 balance of the account.
balanceOf = lfn $locId $ yulmonad'p @(ADDR -> U256)
  \account'p -> LVM.do
  s <- shmapGet balanceMap account'p
  sget (ver'l s)

balanceMap = shmap @(ADDR -> U256) "Yolc.Demo.ERC20.Storage.AccountBalance"

-- | ERC20 transfer function.
transfer = lfn $locId $ yulmonad'p @(ADDR -> ADDR -> U256 -> BOOL)
  \from'p to'p amount'p -> LVM.do
  -- get sender balance
  (from'p, senderBalanceRef) <- pass from'p (shmapGet balanceMap)
  -- get receiver balance
  (to'p, receiverBalanceRef) <- pass to'p (shmapGet balanceMap)
  -- calculate new balances
  (amount, newSenderBalance) <- pass (ver'l amount'p)
    \amount -> ypure $ callFn'l balanceOf (ver'l from'p) - amount
  newReceiverBalance <- with amount
    \amount -> ypure $ callFn'l balanceOf (ver'l to'p) + amount
  -- update storages
  sputs $
    ver'l senderBalanceRef   := newSenderBalance   :|
    ver'l receiverBalanceRef := newReceiverBalance :[]
  -- always return true as a silly urban-legendary ERC20 convention
  embed true

-- | Mint new tokens
mint = lfn $locId $ yulmonad'p @(ADDR -> U256 -> ())
  \account'p mintAmount'p -> LVM.do
  -- fetch balance of the account
  (account'p, balanceBefore) <- pass account'p (ypure . callFn'l balanceOf . ver'l)
  -- use linear port (naming convention, "*'p") values safely
  (account'p, mintAmount'p) <- passN_ (account'p, mintAmount'p) \(account'p, mintAmount'p) -> LVM.do
    -- update balance
    s <- shmapGet balanceMap account'p
    sput (ver'l s) (balanceBefore + ver'l mintAmount'p)
  -- call unsafe external contract onTokenMinted
  externalCall onTokenMinted (ver'l account'p) (ver'l mintAmount'p)

onTokenMinted = declareExternalFn @(U256 -> ()) "onTokenMinted"
