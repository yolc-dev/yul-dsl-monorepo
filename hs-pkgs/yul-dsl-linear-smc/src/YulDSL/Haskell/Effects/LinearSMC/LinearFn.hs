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
import YulDSL.Haskell.Lib
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
  MkStaticFn :: forall (eff :: LinearEffectKind) f.
                ( KnownYulCatEffect eff, AssertStaticEffect eff
                ) => Fn eff f ⊸ StaticFn f

instance ClassifiedFn StaticFn StaticEffect where
  withClassifiedFn g (MkStaticFn f) = g f

data OmniFn f where
  MkOmniFn :: forall (eff :: LinearEffectKind) f.
              ( KnownYulCatEffect eff, AssertOmniEffect eff
              ) => Fn eff f ⊸ OmniFn f

instance ClassifiedFn OmniFn OmniEffect where
  withClassifiedFn g (MkOmniFn f) = g f

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
  lfn' cid f = MkStaticFn (MkFn (cid, decode'l f))

instance ConstructibleLinearFn StaticFn PurePort (VersionedPort 0) where
  lfn' cid f = MkStaticFn (MkFn (cid, decode'l f))

instance (KnownNat vd, AssertOmniEffect (VersionedInputOutput vd)) =>
         ConstructibleLinearFn OmniFn (VersionedPort 0) (VersionedPort vd) where
  lfn' cid f = MkOmniFn (MkFn (cid, decode'l f))

instance (KnownNat vd, AssertOmniEffect (PureInputVersionedOutput vd)) =>
         ConstructibleLinearFn OmniFn PurePort (VersionedPort vd) where
  lfn' cid f = MkOmniFn (MkFn (cid, decode'l f))

-- | Create a curruying linear function with pure input ports.
lfn :: TH.Q TH.Exp
lfn = [e| lfn' $locId |]

------------------------------------------------------------------------------------------------------------------------
-- callFn'l
------------------------------------------------------------------------------------------------------------------------

instance forall f x xs b g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'P r) (P'P r) (YulCat'LPP r ()) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'P r) (P'P r) b One where
  callNP (MkPureFn f) x =
    unsafeCoerceFn f
    & \(MkFn f') -> mkUnit'l x
    & \(x', u) -> curryNP @g @xs @b @(P'P r) @(P'P r) @(YulCat'LPP r ()) @One
                  \(MkYulCat'LPP fxs) -> encodeWith'l id (YulJmpU f') (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'V va r) (P'V va r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'V va r) (P'V va r) b One where
  callNP (MkPureFn f) x =
    (unsafeCoerceFn f :: Fn (VersionedInputOutput 0) f)
    & \(MkFn f') -> mkUnit'l x
    & \(x', u) -> curryNP @g @xs @b @(P'V va r) @(P'V va r) @(YulCat'LVV va va r ()) @One
                  \(MkYulCat'LVV fxs) -> encodeWith'l id (YulJmpU f') (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'V va r) (P'V va r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP StaticFn f x xs b (P'V va r) (P'V va r) b One where
  callNP (MkStaticFn f) = callNP (MkPureFn (unsafeCoerceFn f))

instance forall f x xs b va vb g r.
         ( YulO4 x (NP xs) b r
         , va + 1 ~ vb
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs (P'V vb r b) (P'V va r) (YulMonad va vb r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP OmniFn f x xs b (P'V va r) (YulMonad va vb r) (P'V vb r b) One where
  callNP (MkOmniFn f) x =
    (unsafeCoerceFn f :: Fn (VersionedInputOutput 1) f)
    & \(MkFn f') -> mkUnit'l x
    & \(x', u) -> curryNP @g @xs @(P'V vb r b) @(P'V va r) @(YulMonad va vb r) @(YulCat'LVV va va r ()) @One
                  \(MkYulCat'LVV fxs) -> encodeWith'l
                                         (LVM.unsafeCoerceLVM . ypure)
                                         (YulJmpU f')
                                         $ consNP x' (fxs u)

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
