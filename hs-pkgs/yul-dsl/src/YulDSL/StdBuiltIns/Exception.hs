{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.StdBuiltIns.Exception where
-- eth-abi
import Ethereum.ContractABI
-- CodeGenUtils
import CodeGenUtils.Variable
--
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCatObj


instance YulCatObj a => YulBuiltInPrefix "__const_revert0_c_" () a where
  yulB_fname p@(MkYulBuiltIn @_ @_ @b) = yulB_prefix p <> abiTypeCompactName @b
  yulB_body (MkYulBuiltIn @_ @_ @b) = ( [], gen_vars (length (abiTypeInfo @b))
                                      , ["revert(0, 0)"]
                                      , [])
  yulB_eval p = error (yulB_fname p)
