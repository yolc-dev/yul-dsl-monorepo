module YLVM_Fn_t where
--base
-- import Prelude qualified as BasePrelude
-- hspec
import Test.Hspec
-- (lvm)
import Control.LinearlyVersionedMonad.LVM qualified as LVM
-- yul-dsl
import Prelude.YulDSL
--
import YulPorts_Fn_t qualified


--------------------------------------------------------------------------------
-- declaring ylvm functions
--------------------------------------------------------------------------------

bar0 :: StaticFn (U256)
bar0 = $lfn $ ylvm'pv LVM.do
  Ur u <- yembed ()
  ycall YulPorts_Fn_t.static_fn0u u

bar1 :: StaticFn (U256 -> U256)
bar1 = $lfn $ ylvm'pv
  \x1 -> ycall YulPorts_Fn_t.static_fn1 (ver x1)

test_ytakev :: StaticFn (U256 -> U256 -> U256 -> U256)
test_ytakev = $lfn $ ylvm'pv
  \x1_uv x2_uv x3_uv -> LVM.do
    x1 <- ytakev x1_uv
    x2 <- ytakev x2_uv
    x3 <- ytakev x3_uv
    ymakev (ver'l (x1 + x2 + x3))

test_yrtakev :: StaticFn (U256 -> U256 -> U256 -> U256)
test_yrtakev = $lfn $ ylvm'pv
  \x1_uv x2_uv x3_uv -> LVM.do
    x1 <- yrtakev x1_uv
    x2 <- yrtakev x2_uv
    x3 <- yrtakev x3_uv
    ymakev (x1 + x2 + x3)

test_ytakev_np :: StaticFn (U256 -> U256 -> U256 -> U256)
test_ytakev_np = $lfn $ ylvm'pv
  \x1_uv x2_uv x3_uv -> LVM.do
    -- (x1 :* x2 :* x3 :* Nil) <- ytakevNP (x1_uv :* x2_uv :* x3_uv :* Nil)
    -- ymakev (ver'l (x1 + x2 + x3))
    ytakevNP (x1_uv :* x2_uv :* x3_uv :* Nil) LVM.>>= \case
      (x1 :* x2 :* x3 :* Nil) -> ymakev (ver'l (x1 + x2 + x3))

test_yrtakev_np :: StaticFn (U256 -> U256 -> U256 -> U256)
test_yrtakev_np = $lfn $ ylvm'pv
  \x1_uv x2_uv x3_uv -> LVM.do
    -- (x1 :* x2 :* x3 :* Nil) <- yrtakevNP (x1_uv :* x2_uv :* x3_uv :* Nil)
    -- ymakev (x1 + x2 + x3)
    yrtakevNP (x1_uv :* x2_uv :* x3_uv :* Nil) LVM.>>= \case
      (x1 :* x2 :* x3 :* Nil) -> ymakev (x1 + x2 + x3)

test_ytakev_n :: StaticFn (U256 -> U256 -> U256 -> U256)
test_ytakev_n = $lfn $ ylvm'pv
  \x1_uv x2_uv x3_uv -> LVM.do
    (x1, x2, x3) <- ytakevN (x1_uv, x2_uv, x3_uv)
    ymakev (ver'l (x1 + x2 + x3))

test_yrtakev_n :: StaticFn (U256 -> U256 -> U256 -> U256)
test_yrtakev_n = $lfn $ ylvm'pv
  \x1_uv x2_uv x3_uv -> LVM.do
    (x1, x2, x3) <- yrtakevN (x1_uv, x2_uv, x3_uv)
    ymakev (x1 + x2 + x3)

--------------------------------------------------------------------------------
-- storage effect
--------------------------------------------------------------------------------

test_sput :: OmniFn (B32 -> U256 -> ())
test_sput = $lfn $ ylvm'pv
  \slot val -> LVM.do
    slot <:= val
    yembed ()

call_sput :: OmniFn (B32 -> U256 -> ())
call_sput = $lfn $ ylvm'pv
  \addr val -> ycall test_sput (ver addr) (ver val)

tests = describe "YLVM Linear Function" $
  it "compiles" True
