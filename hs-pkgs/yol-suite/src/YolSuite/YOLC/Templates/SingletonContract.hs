{-# LANGUAGE QuasiQuotes #-}
module YolSuite.YOLC.Templates.SingletonContract (genSingletonContract) where
import Data.Text.Lazy              qualified as T
import YolSuite.YOLC.TemplateUtils (fmt)

genSingletonContract :: (String, String, T.Text) -> T.Text
genSingletonContract (pname, iname, bytecode) = T.pack [fmt|
contract %pname% is Proxy {
    /**
     * @dev Storage slot with the address of the current implementation.
     * This is the keccak-256 hash of "eip1967.proxy.implementation" subtracted by 1, and is
     * validated in the constructor.
     */
    bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;

    address immutable public LOGIC_ADDRESS;

    constructor () {
        bytes memory bytecode = "%bytecode%";
        address logicAddress;

        // create both logic and stunt
        address stunt = address(new %pname%Stunt());
        assembly {
            sstore(_IMPLEMENTATION_SLOT, stunt)
            logicAddress := create(0, add(bytecode, 0x20), mload(bytecode))
        }
        assert(logicAddress != address(0));
        LOGIC_ADDRESS = logicAddress;

    }

    function _implementation() internal view override returns (address) {
        return LOGIC_ADDRESS;
    }
}

function create%pname%() returns (%iname%){
  return %iname%(address(new %pname%()));
}
|]
