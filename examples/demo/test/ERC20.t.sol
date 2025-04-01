pragma solidity ^0.8.20;

import { Test, console } from "forge-std/Test.sol";

import { IERC20Program, createERC20Program } from "yol-build/Contracts.sol";


address constant ALICE = address(41);
address constant BOB = address(42);

contract MintReentranceHacker {
  function onTokenMinted(address mintee, uint256 amount) external {
    IERC20Program token = IERC20Program(msg.sender);
    uint256 balance = token.balanceOf(address(this));
    console.log("Hacker sees minted %d to %s", amount, mintee);
    console.log("Hacker sees his current balance %d", balance);
    token.transfer(ALICE, balance);
  }
}

contract ERC20ProgramTest is Test {
  IERC20Program private token;
  MintReentranceHacker HACKER = new MintReentranceHacker();

  constructor () {
    token = createERC20Program();
  }

  function testBalanceOfIsViewFunction() external view {
    assertEq(token.balanceOf(ALICE), 0);
  }

  function testMintAndTransfer(uint128 x1, uint128 x2) external {
    uint256 mintAmount = uint256(x1) + uint256(x2);
    assertEq(token.balanceOf(ALICE), 0, "alice init balance is wrong");
    assertEq(token.balanceOf(BOB), 0, "bob init balance is wrong");

    token.mint(ALICE, mintAmount);
    assertEq(token.balanceOf(ALICE), mintAmount, "alice balance is wrong 1");

    vm.startPrank(ALICE);
    token.transfer(BOB, x1);
    vm.stopPrank();

    assertEq(token.balanceOf(ALICE), x2, "alice balance is wrong 2");
    assertEq(token.balanceOf(BOB), x1, "bob balance is wrong 2");

    vm.startPrank(ALICE);
    vm.expectRevert();
    token.transfer(BOB, uint256(x2) + 1);
    vm.stopPrank();
  }

  function testMintHack(uint128 x) external {
    token.mint(address(HACKER), x);
    assertEq(token.balanceOf(address(HACKER)), 0, "Hacker's balance is wrong");
    assertEq(token.balanceOf(ALICE), x, "Alice's balance is wrong");
  }
}
