module ERC20 where
import Control.LinearlyVersionedMonad qualified as LVM
import Prelude.YulDSL


-- | ERC20 balance storage location for the account.
--
-- TODO: this code can be made more palatable in the future versions of Yolc.
erc20_balance_storage_of = fn @(ADDR -> B32) $locId $
  \acc -> yulKeccak256 $
          -- shell$ cast keccak "Yolc.Demo.ERC20.Storage.AccountBalance"
          (YulEmb (0xc455e3e95e9cd89a306d7619bc5f6406a85b850d31788d0c0fb15e6364be6592 :: U256))
          `YulFork` acc

balance_sloc account'p = ver'l $ callFn'lpp erc20_balance_storage_of account'p

balance_of account'p = sget $ balance_sloc account'p

-- | ERC20 balance of the account.
erc20_balance_of = lfn $locId $ yulmonad'p @(ADDR -> U256)
  \account'p -> balance_of account'p

erc20_mint = lfn $locId $ yulmonad'p @(ADDR -> U256 -> ())
  \account'p mintAmount'p -> LVM.do
  -- fetch balance of the account
  (account'p, balanceBefore) <- pass account'p balance_of
  -- use linear port (naming convention, "*'p") values safely
  (account'p, mintAmount'p) <- passN_ (account'p, mintAmount'p) \(account'p, mintAmount'p) ->
    -- update balance
    sput (balance_sloc account'p) (balanceBefore + ver'l mintAmount'p)
  -- call unsafe external contract onTokenMinted
  externalCall onTokenMinted (ver'l account'p) (ver'l mintAmount'p)

  -- -- fetch balance of the account
  -- (account'p, balanceBefore) <- pass account'p balance_of
  -- -- use linear port (naming convention, "*'p") values safely
  -- (account'p, mintAmount'p) <- passN_ (account'p, mintAmount'p) \(account'p, mintAmount'p) ->
  --   -- call unsafe external contract onTokenMinted
  --   externalCall onTokenMinted (ver'l account'p) (ver'l mintAmount'p)
  -- -- update balance, but using out dated "balanceBefore value" will fail to compile
  -- sput (balance_sloc account'p) (balanceBefore + ver'l mintAmount'p)

erc20_transfer = lfn $locId $ yulmonad'p @(ADDR -> ADDR -> U256 -> BOOL)
  \from'p to'p amount'p -> LVM.do
  -- get sender balance
  (from'p, senderBalanceRef) <- pass from'p (ypure . balance_sloc)
  -- get receiver balance
  (to'p, receiverBalanceRef) <- pass to'p (ypure . balance_sloc)
  -- calculate new balances
  (amount, newSenderBalance) <- pass (ver'l amount'p)
    \amount -> ypure $ callFn'l erc20_balance_of (ver'l from'p) - amount
  newReceiverBalance <- with amount
    \amount -> ypure $ callFn'l erc20_balance_of (ver'l to'p) + amount
  -- update storages
  sputs $
    senderBalanceRef   := newSenderBalance   :|
    receiverBalanceRef := newReceiverBalance : []
  -- always return true as a silly urban-legendary ERC20 convention
  embed true

object = mkYulObject "ERC20" emptyCtor
  [ staticFn "balanceOf" erc20_balance_of
  , omniFn   "mint" erc20_mint
  , omniFn   "transfer" erc20_transfer
  ]

-- TODO: to be abstracted in an interface definition
--
onTokenMinted = declareExternalFn @(U256 -> ()) "onTokenMinted"
