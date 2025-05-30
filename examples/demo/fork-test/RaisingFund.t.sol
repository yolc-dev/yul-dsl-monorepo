pragma solidity ^0.8.20;

import { Test, console } from "forge-std/Test.sol";
import { IERC20 } from "forge-std/interfaces/IERC20.sol";

import { IRaisingFundProgram, createRaisingFundProgram } from "yol-build/Contracts.sol";


interface IUSDC is IERC20 {
  function masterMinter() external view returns (address);
  function configureMinter(address minter, uint256 minterAllowedAmount) external;
  function mint(address to, uint256 amount) external;
}

contract ForkTestRaisingFundProgram is Test {
  IRaisingFundProgram p;
  address constant ALICE = address(42);

  function setUp() external {
    uint256 baseFork = vm.createFork(vm.envString("BASE_MAINNET_FOUNDRY_ETH_RPC_URL"));
    vm.selectFork(baseFork);
    p = createRaisingFundProgram();
  }

  function testExternalContractAddresses() view external {
    assertEq(p.usdcAddress(), address(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913), "USDC");
    assertEq(p.aaveL2PoolAddress(), address(0xA238Dd80C259a72e81d7e4664a9801593F98d1c5), "USDC");
  }

  function testContribute() external {
    // USDC is in 6 decimals
    uint256 a = 100e6;
    uint256 b = 50e6;

    IUSDC usdc = IUSDC(p.usdcAddress());

    console.log("usdc.masterMinter() = ", usdc.masterMinter());
    vm.startPrank(usdc.masterMinter());
    usdc.configureMinter(ALICE, type(uint256).max);
    vm.stopPrank();

    vm.startPrank(ALICE);
    {
      assertEq(p.myContribution(), 0, "myContribution 0");
      usdc.mint(ALICE, a + b);
      assertEq(usdc.balanceOf(ALICE), a + b, "mint");

      usdc.approve(address(p), a);
      p.contribute(a);
      assertEq(p.myContribution(), a, "myContribution 1");

      usdc.approve(address(p), b);
      p.contribute(b);
      assertEq(p.myContribution(), a + b, "myContribution 2");
    }
    vm.stopPrank();
  }
}
