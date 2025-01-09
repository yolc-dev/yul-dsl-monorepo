{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.CodeGens.Yul.Internal.BuiltIns.Arithmetic (exports) where
-- base
import Data.List                                    (stripPrefix)
import Data.Maybe                                   (fromJust)
-- eth-abi
import Ethereum.ContractABI
-- text
import Data.Text.Lazy                               qualified as T
--
import YulDSL.CodeGens.Yul.Internal.BuiltInRegistra


cmp_builtins = mk_builtin "__cmp_" $ \part full ->
  let (op, typ) = break (== '_') part -- e.g.: __cmp_lt_t_uint256
      clean_f = "__cleanup" <> typ
  in ( [ "function " <> T.pack full <> "(x, y) -> b {"
       , " b := " <> T.pack op <> "(" <> T.pack clean_f <> "(x), " <> T.pack clean_f <> "(y))"
       , "}"
       ]
     , [ clean_f
       , op])

append_checked_maybe_variants op@(safeOpPrefix, _) =
  let opname = fromJust (stripPrefix "__safe_" safeOpPrefix)
  in [ op
     -- checked operator that reverts
     , mk_builtin ("__checked_" <> opname) $ \part full ->
         ( [ "function " <> T.pack full <> "(x, y) -> result {"
           , " let failed := false"
           , " result, failed := " <> T.pack (safeOpPrefix <> part) <> "(x, y)"
           , " if eq(failed, true) { panic_error_0x11() }"
           , "}"
           ]
         , [ safeOpPrefix <> part
           , "panic_error_0x11"
           ])
     -- maybe type wrapped operator
     , mk_builtin ("__maybe_" <> opname) $ \part full ->
         ( [ "function " <> T.pack full <> "(tx, x, ty, y) -> t, result {"
           , " t := iszero(or(iszero(tx), iszero(ty)))"
           , " if eq(t, true) {" -- both Just values
           , "   result, t := " <> T.pack (safeOpPrefix <> part) <> "(x, y)"
           , "   if eq(t, true) {" -- t: failed
           , "     result := 0"
           , "   }"
           , "   t := iszero(t)" -- flip t: not failed / Just value
           , " }"
           , "}"
           ]
         , [ safeOpPrefix <> part
           ])
     ]

safe_add_uintn = mk_builtin "__safe_add_t_uint" $ \part full ->
  let part' = T.pack part
      nbits = read part :: Int
  in ( [ "function " <> T.pack full <> "(x, y) -> sum, failed {"
       , " x := __cleanup_t_uint" <> part' <> "(x)"
       , " y := __cleanup_t_uint" <> part' <> "(y)"
       , " sum := add(x, y)"
       , " if "
         <> (if nbits < 256 then "gt(sum, " <> max_uint_val nbits <> ")" else "gt(x, sum)")
         <> " { failed := true }"
       , "}"
       ]
     , [ "__cleanup_t_uint" <> part
       ])

safe_add_intn = mk_builtin "__safe_add_t_int" $ \part full ->
  let part' = T.pack part
      nbits = read part :: Int
  in ( [ "function " <> T.pack full <> "(x, y) -> sum, failed {"
       , " x := __cleanup_t_int" <> part' <> "(x)"
       , " y := __cleanup_t_int" <> part' <> "(y)"
       , " sum := add(x, y)"
       , " if or("
       ] ++ ( if nbits < 256
              then [ "  sgt(sum, " <> max_int_val nbits <> "),"
                   , "  slt(sum, " <> min_int_val nbits <> ")" ]
              else [ "  and(sge(x, 0), slt(sum, y)),"
                   , "  and(slt(x, 0), sge(sum, y))" ]) ++
       [ " ) { failed := true }"
       , "}"
       ]
     , [ "__cleanup_t_int" <> part
       ])

safe_sub_uintn = mk_builtin "__safe_sub_t_uint" $ \part full ->
  let part' = T.pack part
      nbits = read part :: Int
  in ( [ "function " <> T.pack full <> "(x, y) -> diff, failed {"
       , "  x := __cleanup_t_uint" <> part' <> "(x)"
       , "  y := __cleanup_t_uint" <> part' <> "(y)"
       , "  diff := sub(x, y)"
       , "  if "
         <> (if nbits < 256 then "gt(diff, " <> max_uint_val nbits <> ")" else "gt(diff, x)")
         <> " { failed := true}"
       , "}"
       ]
     , [ "__cleanup_t_uint" <> part
       ])

safe_sub_intn = mk_builtin "__safe_sub_t_int" $ \part full ->
  let part' = T.pack part
      nbits = read part :: Int
  in ( [ "function " <> T.pack full <> "(x, y) -> diff, failed {"
       , "  x := __cleanup_t_int" <> part' <> "(x)"
       , "  y := __cleanup_t_int" <> part' <> "(y)"
       , "  diff := sub(x, y)"
       , "  if or("
       ] ++ (if nbits < 256
             then [ "    slt(diff, " <> min_int_val nbits <> "),"
                  , "    sgt(diff, " <> max_int_val nbits <> ")" ]
             else [ "    and(sge(y, 0), sgt(diff, x)),"
                  , "    and(slt(y, 0), slt(diff, x))" ] ) ++
       [ "  ) { failed := true }"
       , "}"
       ]
     , [ "__cleanup_t_int" <> part ] )

safe_mul_uintn = mk_builtin "__safe_mul_t_uint" $ \part full ->
  let part' = T.pack part
      nbits = read part :: Int
  in ( [ "function " <> T.pack full <> "(x, y) -> product, failed {"
       , " x := __cleanup_t_uint" <> part' <> "(x)"
       , " y := __cleanup_t_uint" <> part' <> "(y)"
       , " let product_raw := mul(x, y)"
       , " product := __cleanup_t_uint" <> part' <> "(product_raw)"
       ] ++ (if nbits == 256
             then [ " // overflow, if x != 0 and y != product/x"
                  , " if iszero(or(iszero(x), eq(y, div(product, x)))) { failed := true }"]
             else [ " if neq(product, product_raw) { failed := true }"]) ++
       [ "}" ]
     , [ "__cleanup_t_uint" <> part
       ])

safe_mul_intn = mk_builtin "__safe_mul_t_int" $ \part full ->
  let part' = T.pack part
      nbits = read part :: Int
  in ( [ "function " <> T.pack full <> "(x, y) -> product, failed {"
       , " x := __cleanup_t_int" <> part' <> "(x)"
       , " y := __cleanup_t_int" <> part' <> "(y)"
       , " let product_raw := mul(x, y)"
       , " product := __cleanup_t_int" <> part' <> "(product_raw)"
       ] ++ (if nbits == 256
              then [ " if and(slt(x, 0), eq(y, " <> min_int_val nbits <> ")) { failed := true }"
                   , " if iszero(failed) {"
                   , "   if iszero(or(iszero(x), eq(y, sdiv(product, x)))) { failed := true }"
                   , " }"
                   ]
             else if nbits > 128
              then [ " if iszero(or(iszero(x), eq(y, sdiv(product, x)))) { failed := true }" ]
              else [ " if neq(product, product_raw) { failed := true }"] ) ++
       [ "}" ]
     , [ "__cleanup_t_int" <> part
       ])


exports :: [BuiltInEntry]
exports =
  [ cmp_builtins ] ++
  append_checked_maybe_variants safe_add_uintn ++
  append_checked_maybe_variants safe_add_intn ++
  append_checked_maybe_variants safe_sub_uintn ++
  append_checked_maybe_variants safe_sub_intn ++
  append_checked_maybe_variants safe_mul_uintn ++
  append_checked_maybe_variants safe_mul_intn

--
-- Internal functions
--

max_uint_val nbits = T.pack . show . fromJust $
  withSomeValidINTx False (toInteger (nbits `div` 8)) $
  \_ (_ :: SNat n) -> toWord (maxBound @(INTx False n))

max_int_val nbits = T.pack . show . fromJust $
  withSomeValidINTx True (toInteger (nbits `div` 8)) $
  \_ (_ :: SNat n) -> toWord (maxBound @(INTx True n))

min_int_val nbits = T.pack . show . fromJust $
  withSomeValidINTx True (toInteger (nbits `div` 8)) $
  \_ (_ :: SNat n) -> toWord (intxUpCast (minBound @(INTx True n)) :: I256)
