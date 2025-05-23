{-# LANGUAGE UndecidableInstances #-}
{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides the operations for working with the 'Pure' kind of effect for the yul category morphisms.

-}
module YulDSL.Haskell.Effects.Pure
  (
    -- * Pure Effect Kind
    -- $PureEffectKind
    PureEffectKind (Pure, Total)
  , YulCat'P, YulFn, PureYulFn
    -- $PureFn
    -- * Pure Functions
  , PureFn (MkPureFn), fn', fn, call, callN
    -- * Template Haskell Support
  , fnLocId
    -- * Technical Notes
    -- $yulCatVal
  ) where
-- template-haskell
import Language.Haskell.TH qualified as TH
-- TO BE MOVED
import Data.Type.Function
-- yul-dsl
import YulDSL.Core


------------------------------------------------------------------------------------------------------------------------
-- $PureEffectKind
------------------------------------------------------------------------------------------------------------------------

-- | Data kind for pure morphisms in the yul category.
data PureEffectKind = Pure  -- ^ Pure morphism, may not be total
                    | Total -- ^ TODO, to further distinguish totality from other pure morphism.

type instance IsEffectNonPure (eff :: PureEffectKind) = False
instance KnownYulCatEffect Pure

type instance MayAffectWorld (eff :: PureEffectKind) = False
instance KnownYulCatEffect Total

-- | Pure yul category morphisms.
type YulCat'P = YulCat Pure

-- | To work with a morphis in yul object-wise.
type YulFn eff f = forall a. YulO1 a => LiftFunction f (YulCat eff a) (YulCat eff a) Many

-- | YulFn of Pure effect.
type PureYulFn f = YulFn Pure f

--
-- UncurriableNP instances
--

-- ^ Base case: @uncurryingNP (x) => NP '[] -> x@
instance YulO2 b r =>
         UncurriableNP '[] b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) (YulCat'P r) Many where
  uncurryNP b _ = b

-- ^ Inductive case: @uncurryingNP (x -> ...xs -> b) => (x, uncurryingNP (... xs -> b)) => NP (x:xs) -> b@
instance forall x xs b r.
         ( YulO4 x (NP I xs) b r
         , UncurriableNP xs b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) (YulCat'P r) Many
         ) =>
         UncurriableNP (x:xs) b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) (YulCat'P r) Many where
  uncurryNP f xxs = let (x, xs) = unconsNP xxs in uncurryNP @xs @b @(YulCat'P r) @(YulCat'P r) (f x) xs

--
-- CurriableNP instances
--

-- ^ Base case: @curryingNP (NP '[] -> b) => b@
instance YulO2 b r =>
         CurriableNP '[] b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) Many where
  curryNP fNP = fNP (YulReduceType <.< YulDis)

-- ^ Inductive case: @curryingNP (NP (x:xs) -> b) => x -> curryingNP (NP I xs -> b)@
instance forall x xs b r.
         ( YulO5 x (NP I xs) b (NP I (x:xs)) r
         , CurriableNP xs b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) Many
         ) =>
         CurriableNP (x:xs) b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) Many where
  curryNP fNP x = curryNP @xs @b @(YulCat'P r) @(YulCat'P r) @_ @(YulCat'P r) @_ (fNP . consNP x)

------------------------------------------------------------------------------------------------------------------------
-- $PureFn
------------------------------------------------------------------------------------------------------------------------

-- | Function without side effects, hence pure.
data PureFn f where
  MkPureFn :: forall f xs b.
    ( EquivalentNPOfFunction f xs b
    , YulO2 (NP I xs) b
    ) =>
    NamedYulCat Pure (NP I xs) b -> PureFn f

instance Show (PureFn f) where
  show (MkPureFn (name, cat)) = "PureFn " <> name <> " {\n  " <> show (cleanYulCat cat) <> "\n}"

instance EquivalentNPOfFunction f xs b => KnownNamedYulCat (PureFn f) PureEffect (NP I xs) b where
  withKnownNamedYulCat (MkPureFn f) g = g f

-- -- | Function without side effects and bottom, hence total.
-- newtype TotalFn f = MkPureFn (Fn Total f)

-- | Create a 'PureFn' by uncyrrying a currying function @f@ of pure yul categorical values.
--
-- __Note: How to use__
--
-- @
--   -- Use type signature to constrain data type:
--   bar :: PureFn (U256 -> U256)
--   bar = $fn
--     \a -> a + a
-- @
--
-- __Note: How to read this type signature__
--
-- When given:
--
--   * @NP I xs = (x1, x2 ... xn)@
--   * @x1' = Pure (NP I xs ⤳ x1), ... xn' = Pure (NP I xs ⤳ xn)@
--   * @f = λ x1' -> ... λ xn' -> Pure (NP I xs ↝ b)@
--
-- It returns: @Pure (NP I xs ↝ b)@
fn' :: forall f xs b m.
  ( YulO2 (NP I xs) b
  , YulCat'P (NP I xs) ~ m
  , EquivalentNPOfFunction f xs b
  , UncurriableNP xs b m m Many m m Many
  ) =>
  String ->
  CurryNP (NP m xs) (m b) Many -> -- ^ uncurrying function type
  PureFn (CurryNP_I (NP I xs) b)  -- ^ result type, or its short form @m b@
fn' cid f = let cat = uncurryNP @xs @b @m @m @_ @m @m @_ f YulId in MkPureFn (cid, cat)

-- | Create a 'PureFn' with automatic id based on function definition source location.
fn :: TH.Q TH.Exp
fn = [e| fn' ("$pfn_" ++ $fnLocId) |]

instance forall f xs b r.
         ( YulO3 (NP I xs) b r
         , EquivalentNPOfFunction f xs b
         , CurriableNP xs b (YulCat'P r) (YulCat'P r) Many (YulCat'P r) Many
         ) =>
         CallableFunctionNP PureFn f xs b (YulCat'P r) (YulCat'P r) Many where
  call (MkPureFn (cid, cat)) =
    curryNP @xs @b @(YulCat'P r) @(YulCat'P r) @_ @(YulCat'P r) @_
    (>.> YulJmpU (cid, cat))

instance forall f xs b r.
         ( YulO3 (NP I xs) b r
         , EquivalentNPOfFunction f xs b
         , ConvertibleNPtoTupleN (YulCat'P r) (NP (YulCat'P r) xs)
         , DistributiveNP (YulCat'P r) xs
         ) =>
         CallableFunctionN PureFn f xs b (YulCat'P r) (YulCat'P r) Many where
  callN (MkPureFn (cid, cat)) tpl = distributeNP (fromTupleNtoNP tpl) >.> YulJmpU (cid, cat)

-- | Automatically generate a source location based id using template haskell.
fnLocId :: TH.Q TH.Exp
fnLocId = do
  loc <- TH.location
  let modname = TH.loc_module loc
      -- normalize module name: replace "."
      modname' = fmap (\x -> if x `elem` "." then '_' else x) modname
      (s1, s2) = TH.loc_start loc
  TH.litE (TH.StringL (modname' ++ "_" ++ show s1 ++ "_" ++ show s2))

-- $yulCatVal
--
-- == Yul Categorical Values
--
-- A yul categorical value of @r ⤳ a@ a morphism from some @r@ to @a@ in the category of yul.
--
-- Notation-wise, one may also wrap it around an effect kind, e.g. @Pure (r ⤳ a)@ means a pure yul categorical value of
-- @r ⤳ a@.
--
-- From category theory perspective, all category values of @a@ forms a hom-set @YulCat(-, a)@ that is contravariant in
-- @a@; or the hom-set of the opposite of the yul category: YulCatOp(a, -).
