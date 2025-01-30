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

  function testDefaultCounterValue() external {
    assertEq(counter.getCounter(), 0);
  }

  function testIncCounter(uint32 a, uint32 b) external {
    counter.incCounter(a);
    assertEq(counter.getCounter(), a, "1");
    counter.incCounter(b);
    assertEq(counter.getCounter(), uint256(a) + b, "2");
  }
}
