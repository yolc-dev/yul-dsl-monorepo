{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.StdBuiltIns.Runtime where
-- eth-abi
import Ethereum.ContractABI
-- CodeGenUtils
import CodeGenUtils.Variable
--
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCatObj


instance YulCatObj a => YulBuiltInPrefix "__const_revert0_c_" () a where
  yulB_fname p@(MkYulBuiltIn @_ @_ @b) = yulB_prefix p <> abiTypeCompactName @b
  yulB_body (MkYulBuiltIn @_ @_ @b) =
    ( [], gen_vars (length (abiTypeInfo @b))
    , ["revert(0, 0)"], []
    )
  yulB_eval b = error (yulB_fname b)

-- A wrapper to caller() for specifying the non-pure effect constraint.
instance YulBuiltInPrefix "__caller" () ADDR where
  type instance IsYulBuiltInNonPure "__caller" = True
  yulB_fname = yulB_prefix
  yulB_body _ = ([], [MkVar "r"], ["r := caller()"] , [])
  yulB_eval b = error ("NoImpl: yulB_eval " ++ yulB_prefix b)
