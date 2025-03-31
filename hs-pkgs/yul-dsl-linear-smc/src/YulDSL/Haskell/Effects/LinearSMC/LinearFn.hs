{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental
-}
module YulDSL.Haskell.Effects.LinearSMC.LinearFn
  ( -- * Build Linear Yul Functions
    StaticFn, OmniFn, lfn', lfn
  , ycall, ycall0', ycall0, ycallN
    -- * Call External Smart Contract Functions
  , externalCall
  ) where
-- base
import GHC.TypeLits                                  (KnownNat, type (+))
-- template-haskell
import Language.Haskell.TH                           qualified as TH
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (linearly-versioned-monoad)
import Control.LinearlyVersionedMonad                qualified as LVM
--
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort

------------------------------------------------------------------------------------------------------------------------
-- Linear Non-Pure Effects
------------------------------------------------------------------------------------------------------------------------

data StaticFn f where
  MkStaticFn :: forall (eff :: LinearEffectKind) f xs b.
                ( ClassifiedYulCatEffect eff, AssertStaticEffect eff
                , EquivalentNPOfFunction f xs b
                ) => NamedYulCat eff (NP xs) b ⊸ StaticFn f

instance EquivalentNPOfFunction f xs b => ClassifiedYulCat (StaticFn f) StaticEffect (NP xs) b where
  withClassifiedYulCat (MkStaticFn f) g = g f

data OmniFn f where
  MkOmniFn :: forall (eff :: LinearEffectKind) f xs b.
              ( ClassifiedYulCatEffect eff, AssertOmniEffect eff
              , EquivalentNPOfFunction f xs b
              ) => NamedYulCat eff (NP xs) b ⊸ OmniFn f

instance EquivalentNPOfFunction f xs b => ClassifiedYulCat (OmniFn f) OmniEffect (NP xs) b where
  withClassifiedYulCat (MkOmniFn f) g = g f

------------------------------------------------------------------------------------------------------------------------
-- Constructible Linear Functions
------------------------------------------------------------------------------------------------------------------------

-- | Create classified linear kind of yul functions.
class ConstructibleLinearFn fn (ie :: PortEffect) (oe :: PortEffect) where
  -- | Define a `YulCat` morphism from a yul port diagram.
  lfn' :: forall f xs b.
    ( YulO2 (NP xs) b
    , EquivalentNPOfFunction f xs b
    ) =>
    String ->
    (forall r. YulO1 r => P'x ie r (NP xs) ⊸ P'x oe r b) ->
    fn f

instance ConstructibleLinearFn StaticFn (VersionedPort 0) (VersionedPort 0) where
  lfn' cid f = MkStaticFn (cid, decode'l f)

instance ConstructibleLinearFn StaticFn PurePort (VersionedPort 0) where
  lfn' cid f = MkStaticFn (cid, decode'l f)

instance (KnownNat vd, AssertOmniEffect (VersionedInputOutput vd)) =>
         ConstructibleLinearFn OmniFn (VersionedPort 0) (VersionedPort vd) where
  lfn' cid f = MkOmniFn (cid, decode'l f)

instance (KnownNat vd, AssertOmniEffect (PureInputVersionedOutput vd)) =>
         ConstructibleLinearFn OmniFn PurePort (VersionedPort vd) where
  lfn' cid f = MkOmniFn (cid, decode'l f)

-- | Create a curruying linear function with pure input ports.
lfn :: TH.Q TH.Exp
lfn = [e| lfn' $locId |]

------------------------------------------------------------------------------------------------------------------------
-- Callable Linear Functions
------------------------------------------------------------------------------------------------------------------------

instance forall f x xs b g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'P r) (P'P r) (YulCat'LPP r ()) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'P r) (P'P r) One where
  call (MkPureFn f') x =
    let !(x', u) = mkUnit'l x
    in curryNP @g @xs @b @(P'P r) @(P'P r) @(YulCat'LPP r ()) @One
       \(MkYulCat'LPP fxs) -> encodeWith'l id (YulJmpU f') (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'V va r) (P'V va r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'V va r) (P'V va r) One where
  call (MkPureFn f) x =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP (x:xs)) b
        !(x', u) = mkUnit'l x
    in curryNP @g @xs @b @(P'V va r) @(P'V va r) @(YulCat'LVV va va r ()) @One
       \(MkYulCat'LVV fxs) -> encodeWith'l id (YulJmpU f') (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'V va r) (P'V va r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP StaticFn f x xs b (P'V va r) (P'V va r) One where
  call (MkStaticFn f) = call (MkPureFn (unsafeCoerceNamedYulCat f))

--
-- ycall
--

class YulMonadCallableFunctionNP fn vd | fn -> vd where
  ycall :: forall xs x b va vb g r fncls.
    ( YulO4 x (NP xs) b r
    , va + vd ~ vb
    , ClassifiedYulCat fn fncls (NP (x:xs)) b
    , CurriableNP g xs (P'V vb r b) (P'V va r) (YulMonad va vb r) (YulCat'LVV va va r ()) One
    ) =>
    fn ->
    P'V va r x ⊸
    LiftFunction (CurryNP (NP xs) (P'V vb r b)) (P'V va r) (YulMonad va vb r) One
  ycall f x =
    let f' = withClassifiedYulCat f unsafeCoerceNamedYulCat :: NamedYulCat (VersionedInputOutput vd) (NP (x:xs)) b
        !(x', u) = mkUnit'l x
    in curryNP @g @xs @(P'V vb r b) @(P'V va r) @(YulMonad va vb r) @(YulCat'LVV va va r ()) @One
       \(MkYulCat'LVV fxs) -> encodeWith'l
                              (LVM.unsafeCoerceLVM . ypure)
                              (YulJmpU f')
                              $ consNP x' (fxs u)

instance YulMonadCallableFunctionNP (PureFn f) 0
instance YulMonadCallableFunctionNP (StaticFn f) 0
instance YulMonadCallableFunctionNP (OmniFn f) 1

--
-- ycall0
--

class YulMonadCallableFunctionNil fn vd | fn -> vd where
  ycall0' :: forall va r b fncls.
    ( YulO2 b r
    , EquivalentNPOfFunction b '[] b
    , ClassifiedYulCat fn fncls (NP '[]) b
    ) =>
    fn -> (P'V va r () ⊸ YulMonad va (va + vd) r (P'V (va + vd) r b))
  ycall0' f u =
    let f' = withClassifiedYulCat f unsafeCoerceNamedYulCat :: NamedYulCat (VersionedInputOutput vd) (NP '[]) b
    in encodeWith'l (LVM.unsafeCoerceLVM . ypure) (YulJmpU f') (coerceType'l u)

instance YulMonadCallableFunctionNil (PureFn f) 0
instance YulMonadCallableFunctionNil (StaticFn f) 0
instance YulMonadCallableFunctionNil (OmniFn f) 1

ycall0 :: TH.Q TH.Exp
ycall0 = [| \f -> yembed () LVM.>>= \u -> ycall0' f u |]

--
-- ycallN
--

class YulMonadCallableFunctionN fn f xs b r va vd | fn -> vd where
  ycallN :: forall fncls.
    ( YulO3 (NP xs) b r
    , EquivalentNPOfFunction f xs b
    , ConvertibleNPtoTupleN (NP (MapList (P'V va r) xs))
    , ClassifiedYulCat fn fncls (NP xs) b
    ) =>
    fn ->
    NPtoTupleN (NP (MapList (P'V va r) xs)) ⊸
    YulMonad va (va + vd) r (P'V (va + vd) r b)

instance YulMonadCallableFunctionN (PureFn b) b '[] b r va 0 where
  ycallN (MkPureFn f) () =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP '[]) b
    in yembed () LVM.>>=
       \u -> encodeWith'l ypure (YulJmpU f') (coerceType'l u)

instance forall f x xs b r va.
         ( YulO2 x (NP xs)
         , DistributiveNP (P'V va r) (x:xs)
         ) =>
         YulMonadCallableFunctionN (PureFn f) f (x:xs) b r va 0 where
  ycallN (MkPureFn f) tpl =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP (x:xs)) b
        xxs = distributeNP (fromTupleNtoNP tpl) :: P'V va r (NP (x:xs))
    in ypure (encodeWith'l id (YulJmpU f') xxs)

instance YulMonadCallableFunctionN (PureFn f) f xs b r va 0 =>
         YulMonadCallableFunctionN (StaticFn f) f xs b r va 0 where
  ycallN (MkStaticFn f) = ycallN (MkPureFn (unsafeCoerceNamedYulCat f))

instance YulMonadCallableFunctionN (OmniFn b) b '[] b r va 1 where
  ycallN (MkOmniFn f) () =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 1) (NP '[]) b
    in yembed () LVM.>>=
       \u -> encodeWith'l (LVM.unsafeCoerceLVM . ypure) (YulJmpU f') (coerceType'l u)

instance forall f x xs b r va.
         ( YulO4 x (NP xs) b r
         , DistributiveNP (P'V va r) (x:xs)
         , ConvertibleNPtoTupleN (NP (MapList (P'V va r) (x:xs)))
         ) =>
         YulMonadCallableFunctionN (OmniFn f) f (x:xs) b r va 1 where
  ycallN (MkOmniFn f) tpl =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 1) (NP (x:xs)) b
        xxs = distributeNP (fromTupleNtoNP tpl) :: P'V va r (NP (x:xs))
    in (LVM.unsafeCoerceLVM . ypure) (encodeWith'l id (YulJmpU f') xxs)

------------------------------------------------------------------------------------------------------------------------
-- calling external functions (Yul Monadic)
------------------------------------------------------------------------------------------------------------------------

externalCall :: forall f x xs b g b' r v1 addrEff.
  ( YulO4 x (NP xs) b r
  , P'V (v1 + 1) r b ~ b'
  , EquivalentNPOfFunction f (x:xs) b
  , EquivalentNPOfFunction g xs b'
  , CurriableNP g xs b' (P'V v1 r) (YulMonad v1 (v1 + 1) r) (YulCat'LVV v1 v1 r ()) One
  ) =>
  ExternalFn f ->
  P'x addrEff r ADDR ⊸
  (P'V v1 r x ⊸ LiftFunction (CurryNP (NP xs) b') (P'V v1 r) (YulMonad v1 (v1 + 1) r) One)
externalCall (MkExternalFn sel) addr x =
  mkUnit'l x
  & \(x', u) ->
      curryNP @g @xs @b' @(P'V v1 r) @(YulMonad v1 (v1 + 1) r) @(YulCat'LVV v1 v1 r ()) @One
      $ \(MkYulCat'LVV fxs) -> encodeWith'l
                               @(VersionedInputOutput 1) @(VersionedPort v1) @(VersionedPort (v1 + 1))
                               @_ @_ @_ {- r a b -}
                               @(YulMonad v1 (v1 + 1) r b')
                               (\(b' :: P'V (v1 + 1) r b) -> LVM.unsafeCoerceLVM (LVM.pure b'))
                               YulId
                               $ go (consNP x' (fxs u))
  where go :: forall. P'x (VersionedPort v1) r (NP (x : xs)) ⊸ P'V v1 r b
        go args = let !(args', u) = mkUnit'l args
                  in encodeWith'l @(VersionedInputOutput 0) @(VersionedPort v1) @(VersionedPort v1)
                     id
                     (YulCall sel)
                     (merge'l (merge'l (unsafeCoerceYulPort addr, emb'l 0 u), args'))
