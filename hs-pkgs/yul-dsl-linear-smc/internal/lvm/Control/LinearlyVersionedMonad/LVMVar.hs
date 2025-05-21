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

data UvLVMVar ctx m a where
  UvLVMVar :: forall ctx m a.
    ( ContextualDupable ctx m a
    , ContextualSeqable ctx m a m a
    , ContextualConsumable ctx m a
    ) =>
    (forall v_. KnownNat v_ => LVM.LVM ctx v_ v_ a) ⊸ UvLVMVar ctx m a

data AnyUvLVMVar ctx where MkAnyUvLVMVar :: forall ctx m a. UvLVMVar ctx m a ⊸ AnyUvLVMVar ctx

mkUvLVMVar :: forall ctx a m.
  ( ContextualDupable ctx m (m a)
  , ContextualSeqable ctx m (m a) m (m a)
  , ContextualConsumable ctx m (m a)
  ) =>
  m a ⊸ UvLVMVar ctx m (m a)
mkUvLVMVar a = UvLVMVar (LVM.MkLVM (Dict, , a))

copyUvLVMVar :: forall a ctx m v.
  KnownNat v =>
  UvLVMVar ctx m (m a) ⊸ LVM.LVM ctx v v (UvLVMVar ctx m (m a), m a)
copyUvLVMVar (UvLVMVar var) = LVM.do
  a <- LVM.unsafeCoerceLVM var :: LVM.LVM ctx v v (m a)
  (a', a'') <- pass1 a LVM.pure
  LVM.pure (mkUvLVMVar a', a'')

--
-- Linearly version-restricted LVM Variable (Rv)
--

data RvLVMVar ctx m v a where
  RvLVMVar :: forall ctx m v a.
    ( KnownNat v
    , ContextualDupable ctx m a
    , ContextualSeqable ctx m a m a
    , LinearlyVersionRestrictable v ctx a
    ) =>
    LVM.LVM ctx v v a ⊸ RvLVMVar ctx m v a

data AnyRvLVMVar ctx where
  MkAnyRvLVMVar :: forall ctx m v_ a. RvLVMVar ctx m v_ a ⊸ AnyRvLVMVar ctx

mkRvLVMVar :: forall ctx m v a.
  ( KnownNat v
  , ContextualDupable ctx m (m a)
  , ContextualSeqable ctx m (m a) m (m a)
  , LinearlyVersionRestrictable v ctx (m a)
  ) =>
  m a ⊸ RvLVMVar ctx m v (m a)
mkRvLVMVar a = RvLVMVar (LVM.MkLVM (Dict, , a) :: LVM.LVM ctx v v (m a))

copyRvLVMVar :: forall a ctx m v.
  KnownNat v =>
  RvLVMVar ctx m v (m a) ⊸ LVM.LVM ctx v v (RvLVMVar ctx m v (m a), m a)
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
consumeLVMVarRegistry :: forall ctx v. KnownNat v => LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (L.Ur ())
consumeLVMVarRegistry (MkLVMVarRegistry uvs vrs) = go1 uvs LVM.>> go2 vrs
  where
    go1 :: [AnyUvLVMVar ctx] ⊸  LVM.LVM ctx v v (L.Ur ())
    go1 ([])                                = LVM.pure (L.Ur ())
    go1 (MkAnyUvLVMVar (UvLVMVar var) : xs) = LVM.unsafeCoerceLVM (var LVM.>>= eject) LVM.>> go1 xs
    go2 :: [AnyRvLVMVar ctx] ⊸  LVM.LVM ctx v v (L.Ur ())
    go2 ([])                                = LVM.pure (L.Ur ())
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
data UvLVMVarRef ctx m a where
  MkUvLVMVarRef :: Int -> UvLVMVarRef ctx m a
type role UvLVMVarRef nominal nominal nominal

-- | Register a 'UvLVMVar' in the 'LVMVarRegistry' and get the reference to it.
registerUvLVMVar :: forall ctx a m.
  ( ContextualConsumable ctx m (m a)
  , ContextualDupable ctx m (m a)
  , ContextualSeqable ctx m (m a) m (m a)
  ) =>
  m a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (UvLVMVarRef ctx m (m a)), LVMVarRegistry ctx)
registerUvLVMVar a (MkLVMVarRegistry uvs vrs) =
  let var = mkUvLVMVar a :: UvLVMVar ctx m (m a)
      !(L.Ur ridx, uvs') = L.length uvs
  in (L.Ur (MkUvLVMVarRef ridx), MkLVMVarRegistry (MkAnyUvLVMVar var : uvs') vrs)

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx (m a)
         ) =>
         ReferenciableLVMVar v (UvLVMVarRef ctx m (m a)) ctx (m a) where
  takeLVMVarRef (MkUvLVMVarRef ridx) (MkLVMVarRegistry uvs vrs) =
    let !(L.Ur len, uvs') = L.length uvs
        !(ys, zzs) = L.splitAt (len - ridx - 1) uvs'
        !(var :: UvLVMVar ctx m (m a), zs') = case L.uncons zzs of
          -- It is safe to assume that @a_ ~ a@.
          Just (MkAnyUvLVMVar var_, zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                       -> L.error "Bad UvLVMVarRef index"
    in LVM.do
         (var', a) <- copyUvLVMVar var
         LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyUvLVMVar var' : zs')) vrs)

--
-- RvLVMVarRef
--

-- | A reference to 'RvLVMVar' or version-restricted 'UvLVMVarRef' in the 'LVMVarRegistry'.
data RvLVMVarRef ctx m v a where
  -- ^ Restricted version variable reference.
  MkRvLVMVarRef :: forall v ctx m a.
    KnownNat v =>
    Int ->
    RvLVMVarRef ctx m v (m a)
  -- ^ 'UvLVMVarRef' that got restricted.
  VerUvLVMVarRef :: forall v ctx m um ua.
    (KnownNat v, LinearlyVersionRestrictable v ctx (um ua)) =>
    UvLVMVarRef ctx um (um ua) ->
    RvLVMVarRef ctx m v (VersionRestrictedData v ctx (um ua))
type role RvLVMVarRef nominal nominal nominal nominal

-- | Register a 'RvLVMVar' in the 'LVMVarRegistry' and get the reference to it.
registerRvLVMVar :: forall v ctx a m.
  ( KnownNat v
  , LinearlyVersionRestrictable v ctx (m a)
  , ContextualDupable ctx m (m a)
  , ContextualSeqable ctx m (m a) m (m a)
  ) =>
  m a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (RvLVMVarRef ctx m v (m a)), LVMVarRegistry ctx)
registerRvLVMVar a (MkLVMVarRegistry vurs vrs) =
  let !(var :: RvLVMVar ctx m v (m a)) = mkRvLVMVar a
      !(L.Ur ridx, xs') = L.length vrs
  in (L.Ur (MkRvLVMVarRef ridx), MkLVMVarRegistry vurs (MkAnyRvLVMVar var : xs'))

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx (m a)
         ) =>
         ReferenciableLVMVar v (RvLVMVarRef ctx m v (m a)) ctx (m a) where
  takeLVMVarRef (MkRvLVMVarRef ridx) (MkLVMVarRegistry vurs vrs) =
    let !(L.Ur len, vrs') = L.length vrs
        !(ys, zzs) = L.splitAt (len - ridx - 1) vrs'
        !(var :: RvLVMVar ctx m v (m a), zs') = case L.uncons zzs of
          -- It is safe to assume that @a_ ~ a, v_ ~ v@.
          Just (MkAnyRvLVMVar var_, zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                       -> L.error "Bad RvLVMVarRef index"
    in LVM.do
         (var', a) <- copyRvLVMVar var
         LVM.pure (a, MkLVMVarRegistry vurs (ys L.++ (MkAnyRvLVMVar var' : zs')))
  takeLVMVarRef (VerUvLVMVarRef uv) rgstr = LVM.do
    (a, rgstr') <- takeLVMVarRef uv rgstr
    a_rs <- restrictVersion a
    LVM.pure (a_rs, rgstr')
