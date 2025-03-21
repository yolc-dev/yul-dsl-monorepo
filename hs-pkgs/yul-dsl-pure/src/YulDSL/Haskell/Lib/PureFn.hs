{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
module YulDSL.Haskell.Lib.PureFn
  -- * Build And Call PureFn
  -- $PureFn
  ( PureFn (MkPureFn), fn', fn
  -- * Technical Notes
  -- $yulCatVal
  ) where
-- template-haskell
import Language.Haskell.TH         qualified as TH
-- eth-abi
import Ethereum.ContractABI
-- yul-dsl
import YulDSL.Core.YulCat
--
import YulDSL.Haskell.Effects.Pure
import YulDSL.Haskell.Lib.TH

-- | Function without side effects, hence pure.
data PureFn f where
  MkPureFn :: Fn Pure f -> PureFn f

instance ClassifiedFn PureFn PureEffect where
  withClassifiedFn g (MkPureFn f) = g f

-- -- | Function without side effects and bottom, hence total.
-- newtype TotalFn f = MkPureFn (Fn Total f)

-- | Create a 'PureFn' by uncyrrying a currying function @f@ of pure yul categorical values.
--
-- __Note: How to use__
--
-- @
--   -- Use type application to resolve the type @f@:
--   bar = fn "bar" $ uncurry'p @(U256 -> U256)
--     \a -> a + a
-- @
--
-- __Note: How to Read This Type Signature__
--
-- When given:
--
--   * @NP xs = (x1, x2 ... xn)@
--   * @x1' = Pure (NP xs ⤳ x1), x2' = Pure (NP xs ↝ x2), ... xn' = Pure (NP xs ⤳ xn)@
--   * @f = λ x1' -> λ x2' -> ... λ xn' -> Pure (NP xs ↝ b)@
--
-- It returns: @Pure (NP xs ↝ b)@
fn' :: forall f xs b m.
  ( YulO2 (NP xs) b
  , YulCat'P (NP xs) ~ m
  , UncurriableNP f xs b m m m m Many
  ) =>
  String ->
  LiftFunction f m m Many -> -- ^ uncurrying function type
  PureFn (CurryNP (NP xs) b) -- ^ result type, or its short form @m b@
fn' cid f = let cat = uncurryingNP @f @xs @b @m @m @m @m f YulId in MkPureFn (MkFn (cid, cat))

-- | Create a 'PureFn' with automatic id based on function definition source location.
fn :: TH.Q TH.Exp
fn = [e| fn' $locId |]

instance ( YulO4 x (NP xs) b r
         , YulCat'P r ~ m
         , CurriableNP xs b (YulCat'P r) (YulCat'P r) (YulCat'P r) Many
         ) =>
         CallableFunctionNP PureFn x xs b (YulCat'P r) (YulCat'P r) Many where
  callNP (MkPureFn (MkFn (cid, cat))) x = curryingNP @xs @b @m @m @m (\xs -> consNP x xs >.> YulJmpU (cid, cat))

instance YulO2 b r =>
         CallableFunctionN PureFn '[] b (YulCat'P r) (YulCat'P r) Many where
  callN (MkPureFn (MkFn (cid, cat))) () = yulNil >.> YulJmpU (cid, cat)

instance ( YulO4 x (NP xs) b r
         , DistributiveNP (YulCat'P r) (x:xs)
         ) =>
         CallableFunctionN PureFn (x:xs) b (YulCat'P r) (YulCat'P r) Many where
  callN (MkPureFn (MkFn (cid, cat))) tpl = distributeNP (fromTupleNtoNP tpl) >.> YulJmpU (cid, cat)

-- $yulCatVal
--
-- = Yul Categorical Value
--
-- A yul categorical value of @r ⤳ a@ is another way of saying all morphisms that leads to @a@ in the category of
-- 'YulCat'.
--
-- One may also wrap it around an effect kind, e.g. @Pure (r ⤳ a)@ means a pure yul categorical value of @r ⤳ a@.
--
-- From category theory perspective, it is a hom-set @YulCat(-, a)@ that is contravariant of @a@.
