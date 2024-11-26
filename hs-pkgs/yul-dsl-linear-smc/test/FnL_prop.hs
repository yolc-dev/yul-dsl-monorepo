module FnL_prop where

-- hspec
import           Test.Hspec
--
import           Prelude        ()
import           Prelude.YulDSL

foo0 = fn'l "foo0" $
  uncurry'l @(() -> U256) (emb'l 42)

foo1 = fn'l "foo1" $
  uncurry'l @(U256 -> U256) id

foo2 = fn'l "foo2" $
  uncurry'l @(U256 -> U256 -> U256)
    \x1 x2 -> x1 + x2

foo3 = fn'l "foo3" $
  uncurry'l @(U256 -> U256 -> U256 -> U256)
    \x1 x2 x3 -> x1 + x2 + x3

foo4 = fn'l "foo4" $
  uncurry'l @(U256 -> U256 -> U256 -> U256 -> U256)
  \x1 x2 x3 x4 -> x1 + x2 + x3 + x4

-- bar3 = fn'l "bar3" $
--   uncurry'p'l @(U256 -> U256 -> U256 -> U256)
--   \x1 x2 x3 -> MkYulCat'L do
--     \xs ->
--       let x1' = lift'l x1 xs
--           x2' = lift'l x2 xs
--           x3' = lift'l x3 xs
--       in x1' + x1' + x2' + x3'

fooSPut = fn'l "fooSPut" $
  uncurry'l @(ADDR -> U256 -> ())
   \addr val -> dis'l (sput addr val)

call0 = fn'l "call0" $
  uncurry'l @(() -> U256)
    \u -> call'l foo0 u

call1 = fn'l "call1" $
  uncurry'l @(U256 -> U256)
    \x -> call'l foo1 x

call2 = fn'l "call2" $
  uncurry'l @(U256 -> U256 -> U256)
    \x1 x2 -> call'l foo2 x1 x2

call3 = fn'l "call3" $
  uncurry'l @(U256 -> U256 -> U256 -> U256)
    \x1 x2 x3 -> call'l foo3 x1 x2 x3

call4 = fn'l "call4" $
  uncurry'l @(U256 -> U256 -> U256 -> U256 -> U256)
    \x1 x2 x3 x4 -> call'l foo4 x1 x2 x3 x4

callSPut = fn'l "callSPut" $
  uncurry'l @(ADDR -> U256 -> ())
    \addr var -> call'l fooSPut addr var

tests = describe "Ethereum.ContractsABI.YulDSL.Linear" $ do
  describe "fn'l: linear function builder" $ do
    it "simple fn definitions" True