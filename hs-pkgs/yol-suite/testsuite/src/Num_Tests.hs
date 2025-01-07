module Num_Tests where

import Prelude.YulDSL

--
-- comparitors
--

-- TODO: hmm, need to use returning TupleN for testing full cmp booleans:
le_uint256 = fn @(U256 -> U256 -> BOOL) $locId \x y -> x < y
le_uint192 = fn @(U192 -> U192 -> BOOL) $locId \x y -> x < y
le_uint128 = fn @(U128 -> U128 -> BOOL) $locId \x y -> x < y
le_uint32  = fn @(U32  -> U32  -> BOOL) $locId \x y -> x < y

le_int256 = fn @(I256 -> I256 -> BOOL) $locId \x y -> x < y
le_int192 = fn @(I192 -> I192 -> BOOL) $locId \x y -> x < y
le_int128 = fn @(I128 -> I128 -> BOOL) $locId \x y -> x < y
le_int32  = fn @(I32  -> I32  -> BOOL) $locId \x y -> x < y

--
-- add
--

add_uint256 = fn @(U256 -> U256 -> U256) $locId \x y -> x + y
add_uint192 = fn @(U192 -> U192 -> U192) $locId \x y -> x + y
add_uint128 = fn @(U128 -> U128 -> U128) $locId \x y -> x + y
add_uint32  = fn @(U32  -> U32  -> U32)  $locId \x y -> x + y

add_int256  = fn @(I256 -> I256 -> I256) $locId \x y -> x + y
add_int192  = fn @(I192 -> I192 -> I192) $locId \x y -> x + y
add_int128  = fn @(I128 -> I128 -> I128) $locId \x y -> x + y
add_int32   = fn @(I32  -> I32  -> I32)  $locId \x y -> x + y

--
-- sub
--

sub_uint256 = fn @(U256 -> U256 -> U256) $locId \x y -> x - y
sub_uint192 = fn @(U192 -> U192 -> U192) $locId \x y -> x - y
sub_uint128 = fn @(U128 -> U128 -> U128) $locId \x y -> x - y
sub_uint32  = fn @(U32  -> U32  -> U32)  $locId \x y -> x - y

sub_int256  = fn @(I256 -> I256 -> I256) $locId \x y -> x - y
sub_int192  = fn @(I192 -> I192 -> I192) $locId \x y -> x - y
sub_int128  = fn @(I128 -> I128 -> I128) $locId \x y -> x - y
sub_int32   = fn @(I32  -> I32  -> I32)  $locId \x y -> x - y

--
-- mul
--

--
-- div
--

--
-- maybe values
--

add_maybe_int96 = fn @(Maybe I96 -> Maybe I96 -> Maybe I96) $locId
  \x y -> x + y

add_int96_with_default = fn @(I96 -> I96 -> I96 -> I96) $locId
  \x y def -> match (inCase (Just x) + inCase (Just y)) \case
    Nothing -> def
    Just z  -> z

add_maybe_int96_with_default = fn @(Maybe I96 -> Maybe I96 -> I96 -> I96) $locId
  \x y def -> match (x + y) \case
    Nothing -> def
    Just z  -> z

object :: YulObject
object = mkYulObject "NumTests" emptyCtor
  [ pureFn "le_uint256" le_uint256
  , pureFn "le_uint192" le_uint192
  , pureFn "le_uint128" le_uint128
  , pureFn "le_uint32"  le_uint32

  , pureFn "le_int256" le_int256
  , pureFn "le_int192" le_int192
  , pureFn "le_int128" le_int128
  , pureFn "le_int32"  le_int32

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
  , pureFn "add_maybe_int96" add_maybe_int96
  , pureFn "add_int96_with_default" add_int96_with_default
  , pureFn "add_maybe_int96_with_default" add_maybe_int96_with_default
  ]
