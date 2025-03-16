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
    StaticFn, OmniFn, lfn', lfn_
    -- * Call Yul Functions Linearly
  , callFn'lvv, callFn'lpp, callFn'l
    -- * Call External Smart Contract Functions
  , externalCall
    -- * Template Haskell Support
  , lfn
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
import YulDSL.Haskell.YulUtils.Pure
-- (linearly-versioned-monoad)
import Control.LinearlyVersionedMonad                qualified as LVM
--
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort

------------------------------------------------------------------------------------------------------------------------
-- lfn
------------------------------------------------------------------------------------------------------------------------

data StaticFn f where
  MkStaticFn :: forall (eff :: LinearEffectKind) f.
                ( KnownYulCatEffect eff, AssertStaticEffect eff
                ) => Fn eff f -> StaticFn f

data OmniFn f where
  MkOmniFn :: forall (eff :: LinearEffectKind) f.
              ( KnownYulCatEffect eff, AssertOmniEffect eff
              ) => Fn eff f -> OmniFn f

instance ClassifiedFn StaticFn StaticEffect where
  withClassifiedFn g (MkStaticFn f) = g f

instance ClassifiedFn OmniFn OmniEffect where
  withClassifiedFn g (MkOmniFn f) = g f

-- | Create classified linear kind of yul functions.
class ConstructibleLinearFn fn (ie :: PortEffect) (oe :: PortEffect) where
  -- | Define a `YulCat` morphism from a yul port diagram.
  lfn' :: forall f xs b.
    ( -- constraint f, using b xs
      EquivalentNPOfFunction f xs b
    , YulO2 (NP xs) b
    ) => String
      -> (forall r. YulO1 r => P'x ie r (NP xs) ⊸ P'x oe r b)
      -> fn f

instance ConstructibleLinearFn StaticFn (VersionedPort 0) (VersionedPort 0) where
  lfn' cid f = MkStaticFn (MkFn (cid, decode'l f))

instance ConstructibleLinearFn StaticFn PurePort (VersionedPort 0) where
  lfn' cid f = MkStaticFn (MkFn (cid, decode'l f))

instance ( KnownNat vd, AssertOmniEffect (VersionedInputOutput vd)
         ) =>
         ConstructibleLinearFn OmniFn (VersionedPort 0) (VersionedPort vd) where
  lfn' cid f = MkOmniFn (MkFn (cid, decode'l f))

instance ( KnownNat vd, AssertOmniEffect (PureInputVersionedOutput vd)
         ) =>
         ConstructibleLinearFn OmniFn PurePort (VersionedPort vd) where
  lfn' cid f = MkOmniFn (MkFn (cid, decode'l f))

-- | Create linear kind of yul functions.
class ConstructibleLinearFn_ (eff :: LinearEffectKind) (ie :: PortEffect) (oe :: PortEffect) | ie oe -> eff where
  -- | Define a `YulCat` morphism from a yul port diagram.
  lfn_ :: forall f xs b.
    ( -- constraint f, using b xs
      EquivalentNPOfFunction f xs b
    , YulO2 (NP xs) b
    ) => String
      -> (forall r. YulO1 r => P'x ie r (NP xs) ⊸ P'x oe r b)
      -> Fn eff f

instance ConstructibleLinearFn_ (VersionedInputOutput vd) (VersionedPort 0) (VersionedPort vd) where
  lfn_ cid f = MkFn (cid, decode'l f)

instance ConstructibleLinearFn_ (PureInputVersionedOutput vd) PurePort (VersionedPort vd) where
  lfn_ cid f = MkFn (cid, decode'l f)

------------------------------------------------------------------------------------------------------------------------
-- callFn'l
------------------------------------------------------------------------------------------------------------------------

type CallFn'L f x xs b r ie oe ye =
  ( -- constraint f
    EquivalentNPOfFunction f (x:xs) b
  , YulO4 x (NP xs) b r
    -- constraint b
  , LiftFunction b (ye r ()) (P'x oe r) One ~ P'x oe r b
    -- CurryingNP instance on "NP xs -> b"
  , CurryingNP xs b (P'x ie r) (P'x oe r) (ye r ()) One
  )

-- | Call functions with versioned yul port and get versioned yul port.
callFn'lvv :: forall f v1 vd vn x xs b r.
  ( v1 + vd ~ vn
  , CallFn'L f x xs b r (VersionedPort v1) (VersionedPort vn) (YulCat'LVV v1 v1)
  ) =>
  Fn (VersionedInputOutput vd) f ->
  (P'V v1 r x ⊸ LiftFunction (CurryNP (NP xs) b) (P'V v1 r) (P'V vn r) One)
-- ^ All other function kinds is coerced into calling as if it is a versioned input output.
callFn'lvv (MkFn f) x =
    mkUnit'l x
    & \(x', u) -> curryingNP @xs @b @(P'V v1 r) @(P'V vn r) @(YulCat'LVV v1 v1 r ()) @One
    $ \(MkYulCat'LVV fxs) -> encodeWith'l id (YulJmpU f)
    $ consNP'l x' (fxs u)

-- | Call pure function with pure yul port and get pure yul port.
callFn'lpp :: forall f x xs b r.
  ( CallFn'L f x xs b r PurePort PurePort YulCat'LPP
  ) =>
  Fn Pure f ->
  (P'P r x ⊸ LiftFunction (CurryNP (NP xs) b) (P'P r) (P'P r) One)
callFn'lpp (MkFn f) x =
  mkUnit'l x
  & \(x', u) -> curryingNP @_ @_ @(P'P r) @(P'P r) @(YulCat'LPP r ()) @One
  $ \(MkYulCat'LPP fxs) -> encodeWith'l id (YulJmpU f)
  $ consNP'l x' (fxs u)

type family CallableFn_LVV_OE fn (ie :: PortEffect) where
  CallableFn_LVV_OE (Fn (PureInputVersionedOutput vd)) (VersionedPort v1) = VersionedPort (v1 + vd)
  CallableFn_LVV_OE (Fn (VersionedInputOutput vd)) (VersionedPort v1) = VersionedPort (v1 + vd)
  CallableFn_LVV_OE (Fn Pure) PurePort = PurePort
  CallableFn_LVV_OE StaticFn (VersionedPort v1) = VersionedPort v1
  CallableFn_LVV_OE OmniFn (VersionedPort v1) = VersionedPort (v1 + 1)
  CallableFn_LVV_OE PureFn (VersionedPort v1) = VersionedPort v1
  CallableFn_LVV_OE PureFn PurePort = PurePort

type family CallableFn_LVV_YE fn (ie :: PortEffect) where
  CallableFn_LVV_YE (Fn (PureInputVersionedOutput _)) (VersionedPort v1) = YulCat'LVV v1 v1
  CallableFn_LVV_YE (Fn (VersionedInputOutput _)) (VersionedPort v1) = YulCat'LVV v1 v1
  CallableFn_LVV_YE (Fn Pure) PurePort = YulCat'LPP
  CallableFn_LVV_YE StaticFn (VersionedPort v1) = YulCat'LVV v1 v1
  CallableFn_LVV_YE OmniFn (VersionedPort v1) = YulCat'LVV v1 v1
  CallableFn_LVV_YE PureFn (VersionedPort v1) = YulCat'LVV v1 v1
  CallableFn_LVV_YE PureFn PurePort = YulCat'LPP

-- | Calling @fnEff@ kind of yul function will increase data version by @vd@.
class CallableFn'LVV fn (ie :: PortEffect) f where
  -- | Call functions with versioned yul port and get versioned yul port.
  callFn'l :: forall x xs b r oe.
    ( CallableFn_LVV_OE fn ie ~ oe
    , CallFn'L f x xs b r ie oe (CallableFn_LVV_YE fn ie)
    ) =>
    fn f ->
    (P'x ie r x ⊸ LiftFunction (CurryNP (NP xs) b) (P'x ie r) (P'x oe r) One)
instance CallableFn'LVV (Fn (PureInputVersionedOutput vd)) (VersionedPort v1) f where
  callFn'l f = callFn'lvv @f @v1 @vd @(v1 + vd) (unsafeCoerceFn f)
instance CallableFn'LVV (Fn (VersionedInputOutput vd)) (VersionedPort v1) f where
  callFn'l f = callFn'lvv @f @v1 @vd @(v1 + vd) (unsafeCoerceFn f)
instance CallableFn'LVV (Fn Pure) PurePort f where
  callFn'l = callFn'lpp @f
instance CallableFn'LVV StaticFn (VersionedPort v1) f where
  callFn'l (MkStaticFn f) = callFn'lvv @f @v1 @0 @v1 (unsafeCoerceFn f)
instance CallableFn'LVV OmniFn (VersionedPort v1) f where
  callFn'l (MkOmniFn f) = callFn'lvv @f @v1 @1 @(v1 + 1) (unsafeCoerceFn f)
instance CallableFn'LVV PureFn (VersionedPort v1) f where
  callFn'l (MkPureFn f) = callFn'lvv @f @v1 @0 @v1 (unsafeCoerceFn f)
instance CallableFn'LVV PureFn PurePort f where
  callFn'l (MkPureFn f) = callFn'lpp @f f

------------------------------------------------------------------------------------------------------------------------
-- calling external functions (Yul Monadic)
------------------------------------------------------------------------------------------------------------------------

externalCall :: forall f x xs b b' r v1 addrEff.
  ( YulO4 x (NP xs) b r
  , P'V (v1 + 1) r b ~ b'
    -- constraint f
  , EquivalentNPOfFunction f (x:xs) b
    -- CurryingNP instance on "NP xs -> b"
  , CurryingNP xs b' (P'V v1 r) (YulMonad v1 (v1 + 1) r) (YulCat'LVV v1 v1 r ()) One
  )
  => ExternalFn f
  -> P'x addrEff r ADDR
  ⊸ (P'V v1 r x ⊸ LiftFunction (CurryNP (NP xs) b') (P'V v1 r) (YulMonad v1 (v1 + 1) r) One)
externalCall (MkExternalFn sel) addr x =
  mkUnit'l x
  & \(x', u) ->
      curryingNP @_ @_ @(P'V v1 r) @(YulMonad v1 (v1 + 1) r) @(YulCat'LVV v1 v1 r ()) @One
      $ \(MkYulCat'LVV fxs) -> encodeWith'l @(VersionedInputOutput 1) @(VersionedPort v1) @(VersionedPort (v1 + 1))
                                            @_ @_ @_ {- r a b -}
                                            @(YulMonad v1 (v1 + 1) r b')
                               (\(b' :: P'V (v1 + 1) r b) -> LVM.unsafeCoerceLVM (LVM.pure b'))
                               YulId
      $ go (consNP'l x' (fxs u))
  where go :: forall. P'x (VersionedPort v1) r (NP (x : xs)) ⊸ P'V v1 r b
        go args = let !(args', u) = mkUnit'l args
                  in encodeWith'l @(VersionedInputOutput 0) @(VersionedPort v1) @(VersionedPort v1)
                     id
                     (YulCall sel)
                     (merge'l (merge'l (unsafeCoerceYulPort addr, emb'l 0 u), args'))

----------------------------------------------------------------------------------------------------
-- Template Haskell Support
----------------------------------------------------------------------------------------------------

-- | Create a curruying linear function with pure input ports.
lfn :: TH.Q TH.Exp
lfn = [e| lfn' $locId |]
