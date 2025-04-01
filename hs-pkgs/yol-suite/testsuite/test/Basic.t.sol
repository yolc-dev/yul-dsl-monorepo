pragma solidity ^0.8.20;

import { Test, console2 } from "forge-std/Test.sol";

import { IBasicTestsProgram, createBasicTestsProgram } from "yol-build/Contracts.sol";


interface TestFoos {
  function foo0() external pure returns (uint256);
  function foo1(uint256) external pure returns (uint256);
  function foo2(uint256, uint256) external pure returns (uint256);
}

contract BasicProgramTest is Test, TestFoos {
  IBasicTestsProgram private _p;

  constructor () {
    _p = createBasicTestsProgram();
  }

  function testEmbeddings() external view {
    _p.embUnit$p(42);
    assertTrue(_p.embTrue$p(), "embTrue$p");
    assertTrue(_p.embTrue$l(), "embTrue$l");
  }

  function testRevetIfTrue() external {
    vm.expectRevert();
    _p.revertIfTrue(true, 42);
    assertEq(_p.revertIfTrue(false, 42), 42);
  }

  function testRangeSum() external view {
    assertEq(_p.rangeSum$p(0, 1, 10), 55, "result1");
    assertEq(_p.rangeSum$l(0, 1, 11), 66, "result1");
  }

  function testExternalFoos() external {
    // assertEq(_p.callExternalFoo0(address(this)), 42);
    assertEq(_p.callExternalFoo1(address(this), 42), 42);
    assertEq(_p.callExternalFoo2(address(this), 42, 69), 111);
  }

  function foo0() override external pure returns (uint256) {
    return 42;
  }

  function foo1(uint256 v1) override external pure returns (uint256) {
    return v1;
  }

  function foo2(uint256 v1, uint256 v2) override external pure returns (uint256) {
    return v1 + v2;
  }
}
