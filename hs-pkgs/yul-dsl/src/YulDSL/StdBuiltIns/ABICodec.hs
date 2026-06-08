{-# OPTIONS_GHC -Wno-orphans -Wno-missing-signatures #-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.StdBuiltIns.ABICodec where
-- eth-abi
import Ethereum.ContractABI
-- text
-- CodeGenUtils
--
import YulDSL.Core.YulBuiltIn
--


------------------------------------------------------------------------------------------------------------------------


instance ( ABITypeable b, YulBuiltInPrefix "__cleanup_t_" U256 b
         ) => YulBuiltInPrefix "__abidec_from_calldata_t_" (U256, U256) b where
  yulB_fname b = yulB_prefix b

------------------------------------------------------------------------------------------------------------------------



------------------------------------------------------------------------------------------------------------------------

instance ABITypeable a => YulBuiltInPrefix "__abienc_from_stack_c_" (U256, a) U256 where
  yulB_fname b = yulB_prefix b <> abiTypeCompactName @a

instance ( ABITypeable a, YulBuiltInPrefix "__cleanup_t_" U256 a
         ) => YulBuiltInPrefix "__abienc_from_stack_t_" (U256, a) () where
  yulB_fname b = yulB_prefix b

instance ABITypeable a => YulBuiltInPrefix "__keccak_c_" a B32 where
  yulB_fname b = yulB_prefix b <> abiTypeCompactName @a

------------------------------------------------------------------------------------------------------------------------

--
-- internal functions
--

-- decoder


