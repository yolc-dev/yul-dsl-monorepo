module Num_Tests where

import Prelude.YulDSL

--
-- comparitors
--

type CmpResult = (BOOL, BOOL, BOOL, BOOL, BOOL)

cmp_uint256 = fn' @(U256 -> U256 -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)
cmp_uint192 = fn' @(U192 -> U192 -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)
cmp_uint128 = fn' @(U128 -> U128 -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)
cmp_uint32  = fn' @(U32  -> U32  -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)

cmp_int256 = fn' @(I256 -> I256 -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)
cmp_int192 = fn' @(I192 -> I192 -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)
cmp_int128 = fn' @(I128 -> I128 -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)
cmp_int32  = fn' @(I32  -> I32  -> CmpResult) $locId \x y -> be (x < y, x <= y, x == y, x >= y, x > y)

--
-- add
--

add_uint256 = fn' @(U256 -> U256 -> U256) $locId \x y -> x + y
add_uint192 = fn' @(U192 -> U192 -> U192) $locId \x y -> x + y
add_uint128 = fn' @(U128 -> U128 -> U128) $locId \x y -> x + y
add_uint32  = fn' @(U32  -> U32  -> U32)  $locId \x y -> x + y

add_int256  = fn' @(I256 -> I256 -> I256) $locId \x y -> x + y
add_int192  = fn' @(I192 -> I192 -> I192) $locId \x y -> x + y
add_int128  = fn' @(I128 -> I128 -> I128) $locId \x y -> x + y
add_int32   = fn' @(I32  -> I32  -> I32)  $locId \x y -> x + y

--
-- sub
--

sub_uint256 = fn' @(U256 -> U256 -> U256) $locId \x y -> x - y
sub_uint192 = fn' @(U192 -> U192 -> U192) $locId \x y -> x - y
sub_uint128 = fn' @(U128 -> U128 -> U128) $locId \x y -> x - y
sub_uint32  = fn' @(U32  -> U32  -> U32)  $locId \x y -> x - y

sub_int256  = fn' @(I256 -> I256 -> I256) $locId \x y -> x - y
sub_int192  = fn' @(I192 -> I192 -> I192) $locId \x y -> x - y
sub_int128  = fn' @(I128 -> I128 -> I128) $locId \x y -> x - y
sub_int32   = fn' @(I32  -> I32  -> I32)  $locId \x y -> x - y

--
-- mul
--

mul_uint256 = fn' @(U256 -> U256 -> U256) $locId \x y -> x * y
mul_uint192 = fn' @(U192 -> U192 -> U192) $locId \x y -> x * y
mul_uint128 = fn' @(U128 -> U128 -> U128) $locId \x y -> x * y
mul_uint32  = fn' @(U32  -> U32  -> U32)  $locId \x y -> x * y

mul_int256 = fn' @(I256 -> I256 -> I256) $locId \x y -> x * y
mul_int192 = fn' @(I192 -> I192 -> I192) $locId \x y -> x * y
mul_int128 = fn' @(I128 -> I128 -> I128) $locId \x y -> x * y
mul_int32  = fn' @(I32  -> I32  -> I32)  $locId \x y -> x * y

--
-- div
--

-- div_uint256 = fn' @(U256 -> U256 -> U256) $locId \x y -> x / y
-- div_uint192 = fn' @(U192 -> U192 -> U192) $locId \x y -> x / y
-- div_uint128 = fn' @(U128 -> U128 -> U128) $locId \x y -> x / y
-- div_uint32  = fn' @(U32  -> U32  -> U32)  $locId \x y -> x / y

-- div_int256 = fn' @(I256 -> I256 -> I256) $locId \x y -> x / y
-- div_int192 = fn' @(I192 -> I192 -> I192) $locId \x y -> x / y
-- div_int128 = fn' @(I128 -> I128 -> I128) $locId \x y -> x / y
-- div_int32  = fn' @(I32  -> I32  -> I32)  $locId \x y -> x / y

--
-- maybe values
--

add_maybe_int96 = fn' @(Maybe I96 -> Maybe I96 -> Maybe I96) $locId
  \x y -> x + y

add_int96_with_default = fn' @(I96 -> I96 -> I96 -> I96) $locId
  \x y def -> match (be (Just x) + be (Just y)) \case
    Nothing -> def
    Just z  -> z

add_maybe_int96_with_default = fn' @(Maybe I96 -> Maybe I96 -> I96 -> I96) $locId
  \x y def -> match (x + y) \case
    Nothing -> def
    Just z  -> z

object :: YulObject
object = mkYulObject "NumTests" yulNoop
  [ pureFn "cmp_uint256" cmp_uint256
  , pureFn "cmp_uint192" cmp_uint192
  , pureFn "cmp_uint128" cmp_uint128
  , pureFn "cmp_uint32"  cmp_uint32

  , pureFn "cmp_int256" cmp_int256
  , pureFn "cmp_int192" cmp_int192
  , pureFn "cmp_int128" cmp_int128
  , pureFn "cmp_int32"  cmp_int32

  , pureFn "add_uint256" add_uint256
  , pureFn "add_uint192" add_uint192
  , pureFn "add_uint128" add_uint128
  , pureFn "add_uint32"  add_uint32
  --
  , pureFn "add_int256" add_int256
  , pureFn "add_int192" add_int192
  , pureFn "add_int128" add_int128
  , pureFn "add_int32"  add_int32
  --
  , pureFn "sub_uint256" sub_uint256
  , pureFn "sub_uint192" sub_uint192
  , pureFn "sub_uint128" sub_uint128
  , pureFn "sub_uint32"  sub_uint32
  --
  , pureFn "sub_int256" sub_int256
  , pureFn "sub_int192" sub_int192
  , pureFn "sub_int128" sub_int128
  , pureFn "sub_int32" sub_int32
  --
  , pureFn "mul_uint256" mul_uint256
  , pureFn "mul_uint192" mul_uint192
  , pureFn "mul_uint128" mul_uint128
  , pureFn "mul_uint32"  mul_uint32
  --
  , pureFn "mul_int256" mul_int256
  , pureFn "mul_int192" mul_int192
  , pureFn "mul_int128" mul_int128
  , pureFn "mul_int32"  mul_int32
  --
  , pureFn "add_maybe_int96" add_maybe_int96
  , pureFn "add_int96_with_default" add_int96_with_default
  , pureFn "add_maybe_int96_with_default" add_maybe_int96_with_default
  ]
