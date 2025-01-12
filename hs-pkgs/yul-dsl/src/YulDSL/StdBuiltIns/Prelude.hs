{-# LANGUAGE OverloadedStrings #-}
module YulDSL.StdBuiltIns.Prelude where
-- text
import Data.Text.Lazy              qualified as T
-- CodeGenUtils
import CodeGenUtils.CodeFormatters

yulObjectPrelude :: [Code]
yulObjectPrelude =
  [ "/// full set of comparitors"
  , "function neq(a, b) -> r { r := iszero( eq(a, b)) }"
  , "function  le(a, b) -> r { r := iszero( gt(a, b)) }"
  , "function  ge(a, b) -> r { r := iszero( lt(a, b)) }"
  , "function sle(a, b) -> r { r := iszero(sgt(a, b)) }"
  , "function sge(a, b) -> r { r := iszero(slt(a, b)) }"
  , ""
  ] ++

  [ "/// exception handling"
  , "function revert_forward_1() {"
  , " let pos := allocate_unbounded()"
  , " returndatacopy(pos, 0, returndatasize())"
  , " revert(pos, returndatasize())"
  , "}"
  , ""
  , "function panic_error(code) {"
  , "  // `cast sig 'Panic(uint256)'` == 0x4e487b71"
  , "  mstore(0, 0x4e487b71" <> T.pack (replicate 56 '0') <> ")"
  , "  mstore(4, code)"
  , "  revert(0, 0x24)"
  , "}"
  , ""
  ] ++

  [ "/// memory conventions"
  , "function allocate_unbounded() -> memPtr { memPtr := mload(64) }"
  , ""
  , "function finalize_allocation(memPtr, size) {"
  , " size := and(add(size, 31), not(31)) // round_up_to_mul_of_32"
  , " let newFreePtr := add(memPtr, size)"
  , " // protect against overflow"
  , " if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error(0x41) }"
  , " mstore(64, newFreePtr)"
  , "}"
  , ""
  ] ++

  [ "/// for object dispatcher"
  , "function selector() -> s {"
  , " s := div(calldataload(0), 0x100000000000000000000000000000000000000000000000000000000)"
  , "}"
  , ""
  ]
