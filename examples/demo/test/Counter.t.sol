pragma solidity ^0.8.20;

import { Test, console } from "forge-std/Test.sol";

import { ICounterProgram, createCounterProgram } from "yol-build/Contracts.sol";


contract CounterProgramTest is Test {
  ICounterProgram private counter;
  address constant ALICE = address(41);
  address constant BOB = address(42);

  constructor () {
    counter = createCounterProgram();
  }

  function testGlobalCounter(uint32 a, uint32 b) external {
    assertEq(counter.getGlobalCounter(), 0);
    assertEq(counter.getGlobalCounter(), 0);
    counter.incGlobalCounter(a);
    assertEq(counter.getGlobalCounter(), a, "1");
    counter.incGlobalCounter(b);
    assertEq(counter.getGlobalCounter(), uint256(a) + b, "2");
  }

  function testUserCounter(uint32 a, uint32 b) external {
    assertEq(counter.getCounter(ALICE), 0);
    assertEq(counter.getCounter(BOB), 0);
    vm.startPrank(ALICE);
    counter.incCounter(a);
    vm.stopPrank();
    vm.startPrank(BOB);
    counter.incCounter(b);
    vm.stopPrank();
    assertEq(counter.getCounter(ALICE), a);
    assertEq(counter.getCounter(BOB), b);
  }
}
