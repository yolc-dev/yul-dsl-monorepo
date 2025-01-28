{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental
-}
module YulDSL.Haskell.Effects.LinearSMC.LinearFn
  ( -- * Build Linear Yul Functions
    CreateLinearFn (lfn)
    -- * Call Yul Functions Linearly
  , LinearlyCallableFn, CallFnLinearly (callFn'l)
  , callFn'lpp
    -- * Call External Smart Contract Functions
  , externalCall
  ) where
-- base
import GHC.TypeLits                                  (type (+))
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

-- | Create linear kind of yul functions.
class CreateLinearFn (iEff :: PortEffect) (oEff :: PortEffect) (fnEff :: LinearEffectKind)
      | iEff oEff -> fnEff where
  -- | Define a `YulCat` morphism from a yul port diagram.
  lfn :: forall f xs b.
    ( YulO2 (NP xs) b
    -- constraint f, using b xs
    , EquivalentNPOfFunction f xs b
    )
    => String
    -> (forall r. YulO1 r => P'x iEff r (NP xs) ⊸ P'x oEff r b)
    -> Fn fnEff (CurryNP (NP xs) b)

instance CreateLinearFn (VersionedPort 0) (VersionedPort vd) (VersionedInputOutput vd) where
  lfn cid f = MkFn (cid, decode'l f)

instance CreateLinearFn PurePort (VersionedPort vd) (PureInputVersionedOutput vd) where
  lfn cid f = MkFn (cid, decode'l f)

------------------------------------------------------------------------------------------------------------------------
-- callFn'l
------------------------------------------------------------------------------------------------------------------------

-- This makes the signature of CallFnLinearly easier to repeat.
type LinearlyCallableFn f x xs b r v1 vd vn =
    ( YulO4 x (NP xs) b r
    , v1 + vd ~ vn
    -- constraint f
    , EquivalentNPOfFunction f (x:xs) b
    -- constraint b
    , LiftFunction b (YulCat'LVV v1 v1 r ()) (P'V vn r) One ~ P'V vn r b
    -- CurryingNP instance on "NP xs -> b"
    , CurryingNP xs b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r ()) One
    )

-- | Calling @fnEff@ kind of yul function will increase data version by @vd@.
class CallFnLinearly fnEff vd | fnEff -> vd where
  -- | Call functions with versioned yul port and get versioned yul port.
  callFn'l :: forall f x xs b r v1 vn.
    LinearlyCallableFn f x xs b r v1 vd vn
    => Fn fnEff f
    -> (P'V v1 r x ⊸ LiftFunction (CurryNP (NP xs) b) (P'V v1 r) (P'V vn r) One)
  -- ^ All other function kinds is coerced into calling as if it is a versioned input output.
  callFn'l f = callFn'l @(VersionedInputOutput vd) @vd @f
               (unsafeCoerceFn f)

instance CallFnLinearly (VersionedInputOutput vd) vd where
  callFn'l :: forall f x xs b r v1 vn.
    LinearlyCallableFn f x xs b r v1 vd vn
    => Fn (VersionedInputOutput vd) f
    -> (P'V v1 r x ⊸ LiftFunction (CurryNP (NP xs) b) (P'V v1 r) (P'V vn r) One)
  callFn'l (MkFn t) x =
    mkUnit'l x
    & \(x', u) -> curryingNP @xs @b @(P'V v1 r) @(P'V vn r) @(YulCat'LVV v1 v1 r ()) @One
    $ \(MkYulCat'LVV fxs) -> encode'l (YulJmpU t) id
    $ cons'l x' (fxs u)

instance CallFnLinearly (PureInputVersionedOutput vd) vd
instance CallFnLinearly Pure 0
instance CallFnLinearly Total 0

-- | Call pure function with pure yul port and get pure yul port.
callFn'lpp :: forall f x xs b r eff.
  ( YulO4 x (NP xs) b r
  -- constraint f
  , EquivalentNPOfFunction f (x:xs) b
  -- constraint b
  , LiftFunction b (YulCat'LPP r ()) (P'P r) One ~ P'P r b
  -- CurryingNP instance on "NP xs -> b"
  , CurryingNP xs b (P'P r) (P'P r) (YulCat'LPP r ()) One
  )
  => Fn (eff :: PureEffectKind) f
  -> (P'P r x ⊸ LiftFunction (CurryNP (NP xs) b) (P'P r) (P'P r) One)
callFn'lpp (MkFn t) x =
  mkUnit'l x
  & \(x', u) -> curryingNP @_ @_ @(P'P r) @(P'P r) @(YulCat'LPP r ()) @One
  $ \(MkYulCat'LPP fxs) -> encode'l (YulJmpU t) id
  $ cons'l x' (fxs u)

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
  & \(x', u) -> curryingNP @_ @_ @(P'V v1 r) @(YulMonad v1 (v1 + 1) r) @(YulCat'LVV v1 v1 r ()) @One
  $ \(MkYulCat'LVV fxs) -> encode'l @(VersionedInputOutput 1) @(VersionedPort v1) @(VersionedPort (v1 + 1))
                                    @_ @_ @_ {- r a b -}
                                    @(YulMonad v1 (v1 + 1) r b')
                           YulId
                           (\(b' :: P'V (v1 + 1) r b) -> LVM.unsafeCoerceLVM (LVM.pure b'))
  $ go (cons'l x' (fxs u))
  where go :: forall. P'x (VersionedPort v1) r (NP (x : xs)) ⊸ P'V v1 r b
        go args = let !(args', u) = mkUnit'l args
                  in encode'l @(VersionedInputOutput 0) @(VersionedPort v1) @(VersionedPort v1)
                     (YulCall sel)
                     id
                     (merge'l (merge'l (unsafeCoerceYulPort addr, emb'l 0 u), args'))
