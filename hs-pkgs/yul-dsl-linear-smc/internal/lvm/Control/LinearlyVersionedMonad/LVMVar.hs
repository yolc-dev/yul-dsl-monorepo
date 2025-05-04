{-# LANGUAGE TypeFamilyDependencies #-}
{-|

Copyright   : (c) 2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides linearly version-restrictable variables and their references to work with LVM without dealing with
the linear arrows.

The idiom to work with unrestricted data over linear arrows is the "Ur" (unrestricted) constructor. However, the purpose
of the LVM is to linearly version-restrict data where they can be used. Abandoning the linear arrows is not an option,
since the restriction logic depends on it. Hence, two new constructors are created in addition to the "Ur" constructor:
"Rv" (restricted variables) and "Uv" (Unrestricted variables).

-}
module Control.LinearlyVersionedMonad.LVMVar
  ( -- $LinearlyVersionRestrictable
    LinearlyVersionRestrictable (VersionRestrictedData, restrictVersion)
    -- $UsableLVMVar
    -- $LVMVarRegistry
  , LVMVarRegistry, initLVMVarRegistry, consumeLVMVarRegistry
  , ReferenciableLVMVar (takeLVMVarRef, takevLVMVarRef)
  , UvLVMVarRef, registerUvLVMVar
  , RvLVMVarRef (VerUvLVMVarRef), registerRvLVMVar
  ) where
-- base
import Data.Kind                                  (Type)
import GHC.TypeLits                               (KnownNat)
import Prelude                                    (Int, Maybe (..), type (~), (-))
-- linear-base
import Prelude.Linear                             qualified as L
import Unsafe.Linear                              qualified as UnsafeLinear
-- constraints
import Data.Constraint.Linear                     (Dict (Dict))
--
import Control.LinearlyVersionedMonad.Combinators
import Control.LinearlyVersionedMonad.LVM         qualified as LVM
import Data.LinearContext


------------------------------------------------------------------------------------------------------------------------
-- $LinearlyVersionRestrictable
-- * Linearly Version Restrictable Data
------------------------------------------------------------------------------------------------------------------------

-- | Data that is linearly restrictable to any version.
class KnownNat v =>  LinearlyVersionRestrictable v ctx a where
  type family VersionRestrictedData v ctx a = (a_rv :: Type) | a_rv -> ctx
  restrictVersion :: forall. a ⊸ LVM.LVM ctx v v (VersionRestrictedData v ctx a)

--
-- Version-unrestricted LVM Var (Uv)
--

data UvLVMVar ctx a where
  UvLVMVar :: forall ctx a.
    ( ContextualDupable ctx a
    , ContextualSeqable ctx a a
    , ContextualConsumable ctx a
    ) =>
    (forall v_. KnownNat v_ => LVM.LVM ctx v_ v_ a) ⊸ UvLVMVar ctx a

data AnyUvLVMVar ctx where MkAnyUvLVMVar :: forall ctx a. UvLVMVar ctx a ⊸ AnyUvLVMVar ctx

mkUvLVMVar :: forall ctx a.
  ( ContextualDupable ctx a
  , ContextualSeqable ctx a a
  , ContextualConsumable ctx a
  ) =>
  a ⊸ UvLVMVar ctx a
mkUvLVMVar a = UvLVMVar (LVM.MkLVM (Dict, , a))

copyUvLVMVar :: forall a ctx v. KnownNat v => UvLVMVar ctx a ⊸ LVM.LVM ctx v v (UvLVMVar ctx a, a)
copyUvLVMVar (UvLVMVar var) = LVM.do
  a <- LVM.unsafeCoerceLVM var
  (a', a'') <- pass1 a LVM.pure
  LVM.pure (mkUvLVMVar a', a'')

--
-- Linearly version-restricted LVM Variable (Rv)
--

data RvLVMVar ctx v a where
  RvLVMVar :: forall ctx v a.
    ( KnownNat v
    , ContextualDupable ctx a
    , ContextualSeqable ctx a a
    , LinearlyVersionRestrictable v ctx a
    ) =>
    LVM.LVM ctx v v a ⊸ RvLVMVar ctx v a

data AnyRvLVMVar ctx where MkAnyRvLVMVar :: forall ctx v_ a. RvLVMVar ctx v_ a ⊸ AnyRvLVMVar ctx

mkRvLVMVar :: forall ctx v a.
  ( KnownNat v
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  , LinearlyVersionRestrictable v ctx a
  ) =>
  a ⊸ RvLVMVar ctx v a
mkRvLVMVar a = RvLVMVar (LVM.MkLVM (Dict, , a) :: LVM.LVM ctx v v a)

copyRvLVMVar :: forall a ctx v. KnownNat v => RvLVMVar ctx v a ⊸ LVM.LVM ctx v v (RvLVMVar ctx v a, a)
copyRvLVMVar (RvLVMVar var) = LVM.do
  a <- var
  (a', a'') <- pass1 a LVM.pure
  LVM.pure (mkRvLVMVar a', a'')

----------------------------------------------------------------------------------------------------
-- $LVMVarRegistry
-- * LVMVar Registry
----------------------------------------------------------------------------------------------------

-- | The registry of LVM variables. It must be used over linear arrows.
data LVMVarRegistry ctx where
  MkLVMVarRegistry :: forall ctx.
    [AnyUvLVMVar ctx] ⊸
    [AnyRvLVMVar ctx] ⊸
    LVMVarRegistry ctx

-- | Initialize a 'LVMVarRegistry'.
initLVMVarRegistry :: LVMVarRegistry ctx
initLVMVarRegistry = MkLVMVarRegistry [] []

-- | Consumes a 'LVMVarRegistry'.
consumeLVMVarRegistry :: forall ctx v. KnownNat v => LVMVarRegistry ctx ⊸ LVM.LVM ctx v v ()
consumeLVMVarRegistry (MkLVMVarRegistry uvs vrs) = go1 uvs LVM.>> go2 vrs
  where go1 ([])                                = LVM.pure ()
        go1 (MkAnyUvLVMVar (UvLVMVar var) : xs) = LVM.unsafeCoerceLVM (var LVM.>>= eject) LVM.>> go1 xs
        go2 ([])                                = LVM.pure ()
        go2 (MkAnyRvLVMVar (RvLVMVar var) : xs) = LVM.veryUnsafeCoerceLVM (var LVM.>>= eject) LVM.>> go2 xs

-- | A reference to a variable in the 'LVMVarRegistry'.
class ( KnownNat v
      , LinearlyVersionRestrictable v ctx a
      ) =>
      ReferenciableLVMVar v vref ctx a | v vref -> ctx a where
  -- | Take a copy of the variable stored in the reference.
  takeLVMVarRef :: forall. vref ⊸ LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (a, LVMVarRegistry ctx)

  -- | Take a linearly version-restricted copy of the variable stored in the reference.
  takevLVMVarRef :: forall a_rv.
    VersionRestrictedData v ctx a ~ a_rv =>
    vref ⊸ LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (a_rv, LVMVarRegistry ctx)
  takevLVMVarRef ref registry = LVM.do
    (a, registry') <- takeLVMVarRef ref registry
    a' <- restrictVersion a
    LVM.pure (a', registry')

--
-- UvLVMVarRef
--

-- | A reference to 'UvLVMVar' in the 'LVMVarRegistry'.
data UvLVMVarRef ctx a where
  MkUvLVMVarRef :: Int -> UvLVMVarRef ctx a
type role UvLVMVarRef nominal nominal

-- | Register a 'UvLVMVar' in the 'LVMVarRegistry' and get the reference to it.
registerUvLVMVar :: forall ctx a.
  ( ContextualConsumable ctx a
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (UvLVMVarRef ctx a), LVMVarRegistry ctx)
registerUvLVMVar a (MkLVMVarRegistry uvs vrs) =
  let var = mkUvLVMVar a :: UvLVMVar ctx a
      !(L.Ur ridx, uvs') = L.length uvs
  in (L.Ur (MkUvLVMVarRef ridx), MkLVMVarRegistry (MkAnyUvLVMVar var : uvs') vrs)

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         ReferenciableLVMVar v (UvLVMVarRef ctx a) ctx a where
  takeLVMVarRef (MkUvLVMVarRef ridx) (MkLVMVarRegistry uvs vrs) =
    let !(L.Ur len, uvs') = L.length uvs
        !(ys, zzs) = L.splitAt (len - ridx - 1) uvs'
        !(var :: UvLVMVar ctx a, zs') = case L.uncons zzs of
          -- It is safe to assume that @a_ ~ a@.
          Just (MkAnyUvLVMVar (var_ :: UvLVMVar ctx a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                            -> L.error "Bad UvLVMVarRef index"
    in LVM.do
         (var', a) <- copyUvLVMVar var
         LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyUvLVMVar var' : zs')) vrs)

--
-- RvLVMVarRef
--

-- | A reference to 'RvLVMVar' or version-restricted 'UvLVMVarRef' in the 'LVMVarRegistry'.
data RvLVMVarRef ctx v a where
  -- ^ Restricted version variable reference.
  MkRvLVMVarRef :: forall v ctx a.
    KnownNat v =>
    Int ->
    RvLVMVarRef ctx v a
  -- ^ 'UvLVMVarRef' that got restricted.
  VerUvLVMVarRef :: forall v ctx ua.
    (KnownNat v, LinearlyVersionRestrictable v ctx ua) =>
    UvLVMVarRef ctx ua ->
    RvLVMVarRef ctx v (VersionRestrictedData v ctx ua)
type role RvLVMVarRef nominal nominal nominal

-- | Register a 'RvLVMVar' in the 'LVMVarRegistry' and get the reference to it.
registerRvLVMVar :: forall v ctx a.
  ( KnownNat v
  , LinearlyVersionRestrictable v ctx a
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (RvLVMVarRef ctx v a), LVMVarRegistry ctx)
registerRvLVMVar a (MkLVMVarRegistry vurs vrs) =
  let !(var :: RvLVMVar ctx v a) = mkRvLVMVar a
      !(L.Ur ridx, xs') = L.length vrs
  in (L.Ur (MkRvLVMVarRef ridx), MkLVMVarRegistry vurs (MkAnyRvLVMVar var : xs'))

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         ReferenciableLVMVar v (RvLVMVarRef ctx v a) ctx a where
  takeLVMVarRef (MkRvLVMVarRef ridx) (MkLVMVarRegistry vurs vrs) =
    let !(L.Ur len, vrs') = L.length vrs
        !(ys, zzs) = L.splitAt (len - ridx - 1) vrs'
        !(var :: RvLVMVar ctx v a, zs') = case L.uncons zzs of
          -- It is safe to assume that @a_ ~ a, v_ ~ v@.
          Just (MkAnyRvLVMVar (var_ :: RvLVMVar ctx v_ a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                               -> L.error "Bad RvLVMVarRef index"
    in LVM.do
         (var', a) <- copyRvLVMVar var
         LVM.pure (a, MkLVMVarRegistry vurs (ys L.++ (MkAnyRvLVMVar var' : zs')))
  takeLVMVarRef (VerUvLVMVarRef uv) rgstr = LVM.do
    (a, rgstr') <- takeLVMVarRef uv rgstr
    a_rs <- restrictVersion a
    LVM.pure (a_rs, rgstr')
