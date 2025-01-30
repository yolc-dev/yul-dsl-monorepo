module LinearFn_prop where

-- hspec
import Test.Hspec
--
import Prelude        ()
import Prelude.YulDSL


foo0 :: StaticFn (() -> U256)
foo0 = lfn $locId $
  uncurry'lvv (emb'l 42)

foo1 :: StaticFn (U256 -> U256)
foo1 = lfn $locId $
  uncurry'lvv id

foo2 :: StaticFn (U256 -> U256 -> U256)
foo2 = lfn $locId $
  uncurry'lvv
    \x1 x2 -> x1 + x2

foo3 :: StaticFn (U256 -> U256 -> U256 -> U256)
foo3 = lfn $locId $
  uncurry'lvv
    \x1 x2 x3 -> x1 + x2 + x3

foo4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
foo4 = lfn $locId $
  uncurry'lvv
  \x1 x2 x3 x4 -> x1 + x2 + x3 + x4

maybe_fn :: StaticFn (Maybe U256 -> U256)
maybe_fn = lfn $locId $ uncurry'lvv
  \x1 -> match'l x1 \case
    Just c  -> c
    Nothing -> 0

bar3 :: StaticFn (U256 -> U256 -> U256 -> U256)
bar3 = lfn $locId $ yulmonad'p
  \x1 x2 x3 -> ypure (ver'l x1 + ver'l x2 + ver'l x3)

fooSPut :: OmniFn (B32 -> U256 -> ())
fooSPut = lfn $locId $ yulmonad'p
  \sloc'p val'p -> sput (ver'l sloc'p) (ver'l val'p)

call0 :: StaticFn (() -> U256)
call0 = lfn $locId $ uncurry'lvv
  \u -> callFn'l foo0 u

call1 :: StaticFn (U256 -> U256)
call1 = lfn $locId $ uncurry'lvv
  \x -> callFn'l foo1 x

call2 :: StaticFn (U256 -> U256 -> U256)
call2 = lfn $locId $ uncurry'lvv
  \x1 x2 -> callFn'l foo2 x1 x2

call3 :: StaticFn (U256 -> U256 -> U256 -> U256)
call3 = lfn $locId $ uncurry'lvv
  \x1 x2 x3 -> callFn'l foo3 x1 x2 x3

call4 :: StaticFn (U256 -> U256 -> U256 -> U256 -> U256)
call4 = lfn $locId $ uncurry'lvv
  \x1 x2 x3 x4 -> callFn'l foo4 x1 x2 x3 x4

callSPut :: OmniFn (B32 -> U256 -> ())
callSPut = lfn $locId $ uncurry'lvv
  \addr var -> callFn'l fooSPut addr var

tests = describe "Ethereum.ContractsABI.YulDSL.Linear" $ do
  describe "lfn: linear function builder" $ do
    it "simple fn definitions" True
