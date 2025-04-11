{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Control.LinearlyVersionedMonad.LVMVar
  ( -- * Linearly Version Restrictable Data
    LinearlyVersionRestrictable (LinearlyRestrictedVersion, restrictVersion)
    -- * LVMVar Registry
  , LVMVarRegistry, initLVMVarRegistry, consumeLVMVarRegistry
  , LVMVarReferenciable (readLVMVarRef, vreadLVMVarRef)
  , UvLVMVarRef, registerUvLVMVar
  , VrLVMVarRef, registerVrLVMVar
  ) where
-- base
import Data.Kind                                  (Type)
import GHC.TypeLits                               (KnownNat, Nat)
import Prelude                                    (Int, Maybe (..), type (~))
-- linear-base
import Prelude.Linear                             qualified as L
import Unsafe.Linear                              qualified as UnsafeLinear
-- constraints
import Data.Constraint.Linear                     (Dict (Dict))
--
import Control.LinearlyVersionedMonad             as LVM
import Control.LinearlyVersionedMonad.Combinators
import Data.LinearContext


----------------------------------------------------------------------------------------------------
-- LinearlyVersionRestrictable: Uv & Vr LVMVar
----------------------------------------------------------------------------------------------------

-- | Data that is linearly restrictable to any version.
class LinearlyVersionRestrictable ctx a where
  type family LinearlyRestrictedVersion ctx a (v :: Nat) = (a' :: Type) | a' -> ctx
  restrictVersion :: forall v. KnownNat v => a ⊸ LVM ctx v v (LinearlyRestrictedVersion ctx a v)

class (KnownNat v, LinearlyVersionRestrictable ctx a) => UsableLVMVar v var ctx a | var -> ctx a where
  copyLVMVar :: forall. var ⊸ LVM ctx v v (var, a)

--
-- Unrestricted-version (Uv) LVMVar
--

-- | Restricted-version (Uv) linearly-versioned monadic (LVM) value in its version.
data UvLVMVar ctx a where
  UvLVMVar :: forall ctx a.
    ( LinearlyVersionRestrictable ctx a
    , ContextualDupable ctx a
    , ContextualSeqable ctx a a
    , ContextualConsumable ctx a
    ) =>
    (forall v_. KnownNat v_ => LVM ctx v_ v_ a) ⊸ UvLVMVar ctx a

data AnyUvLVMVar ctx where MkAnyUvLVMVar :: forall ctx a. UvLVMVar ctx a ⊸ AnyUvLVMVar ctx

mkUvLVMVar :: forall ctx a.
    ( LinearlyVersionRestrictable ctx a
    , ContextualDupable ctx a
    , ContextualSeqable ctx a a
    , ContextualConsumable ctx a
    ) =>
  a ⊸ UvLVMVar ctx a
mkUvLVMVar a = UvLVMVar (MkLVM (Dict, , a))

instance ( KnownNat v
         , LinearlyVersionRestrictable ctx a
         ) =>
         UsableLVMVar v (UvLVMVar ctx a) ctx a where
  copyLVMVar (UvLVMVar var) = LVM.do
    a <- unsafeCoerceLVM var
    (a', a'') <- pass1 a LVM.pure
    LVM.pure (mkUvLVMVar a', a'')

--
-- Version-restricted (Vr) LVMVar
--

-- | Version-Restricted (Vr) linearly-versioned monadic (LVM) value.
data VrLVMVar ctx v a where
  VrLVMVar :: forall ctx v a.
    ( KnownNat v
    , ContextualDupable ctx a
    , ContextualSeqable ctx a a
    , LinearlyVersionRestrictable ctx a
    ) =>
    LVM ctx v v a ⊸ VrLVMVar ctx v a

data AnyVrLVMVar ctx where MkAnyVrLVMVar :: forall ctx v_ a. VrLVMVar ctx v_ a ⊸ AnyVrLVMVar ctx

mkVrLVMVar :: forall ctx v a.
  ( KnownNat v
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  , LinearlyVersionRestrictable ctx a
  ) =>
  a ⊸ VrLVMVar ctx v a
mkVrLVMVar a = VrLVMVar (MkLVM (Dict, , a) :: LVM ctx v v a)

instance ( KnownNat v
         , LinearlyVersionRestrictable ctx a
         ) =>
         UsableLVMVar v (VrLVMVar ctx v a) ctx a where
  copyLVMVar (VrLVMVar var) = LVM.do
    a <- var
    (a', a'') <- pass1 a LVM.pure
    LVM.pure (mkVrLVMVar a', a'')

----------------------------------------------------------------------------------------------------
-- LVMVar Registry
----------------------------------------------------------------------------------------------------

data LVMVarRegistry ctx where
  MkLVMVarRegistry :: forall ctx.
    [AnyUvLVMVar ctx] ⊸
    [AnyVrLVMVar ctx] ⊸
    LVMVarRegistry ctx

initLVMVarRegistry :: LVMVarRegistry ctx
initLVMVarRegistry = MkLVMVarRegistry [] []

consumeLVMVarRegistry :: forall ctx v. KnownNat v => LVMVarRegistry ctx ⊸ LVM ctx v v ()
consumeLVMVarRegistry (MkLVMVarRegistry vurs vrs) = go1 vurs LVM.>> go2 vrs
  where go1 ([])                                = LVM.pure ()
        go1 (MkAnyUvLVMVar (UvLVMVar var) : xs) = unsafeCoerceLVM (var LVM.>>= eject) LVM.>> go1 xs
        go2 ([])                                = LVM.pure ()
        go2 (MkAnyVrLVMVar (VrLVMVar var) : xs) = veryUnsafeCoerceLVM (var LVM.>>= eject) LVM.>> go2 xs

class ( KnownNat v
      , LinearlyVersionRestrictable ctx a
      ) => LVMVarReferenciable v ref ctx a | ref -> ctx a where
  readLVMVarRef :: forall. ref ⊸ LVMVarRegistry ctx ⊸ LVM ctx v v (a, LVMVarRegistry ctx)

  vreadLVMVarRef :: forall a'.
    LinearlyRestrictedVersion ctx a v ~ a' =>
    ref ⊸ LVMVarRegistry ctx ⊸ LVM ctx v v (a', LVMVarRegistry ctx)
  vreadLVMVarRef ref registry = LVM.do
    (a, registry') <- readLVMVarRef ref registry
    a' <- restrictVersion a
    LVM.pure (a', registry')

--
-- UvLVMVarRef
--

newtype UvLVMVarRef ctx a = UvLVMVarRef Int
type role UvLVMVarRef nominal nominal

registerUvLVMVar :: forall ctx a.
  ( ContextualConsumable ctx a
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  , LinearlyVersionRestrictable ctx a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (UvLVMVarRef ctx a), LVMVarRegistry ctx)
registerUvLVMVar a (MkLVMVarRegistry vurs vrs) =
  let var = mkUvLVMVar a :: UvLVMVar ctx a
      !(L.Ur idx, vurs') = L.length vurs
  in (L.Ur (UvLVMVarRef idx), MkLVMVarRegistry (MkAnyUvLVMVar var : vurs') vrs)

instance ( KnownNat v
         , LinearlyVersionRestrictable ctx a
         ) =>
         LVMVarReferenciable v (UvLVMVarRef ctx a) ctx a where
  readLVMVarRef (UvLVMVarRef idx) (MkLVMVarRegistry vurs vrs) =
    let !(ys, zzs) = L.splitAt idx vurs
        !(var :: UvLVMVar ctx a, zs') = case L.uncons zzs of
          Just (MkAnyUvLVMVar (var_ :: UvLVMVar ctx a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                            -> L.error "Bad UvLVMVarRef index"
    in LVM.do
         (var', a) <- copyLVMVar var
         LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyUvLVMVar var' : zs')) vrs)

--
-- VrLVMVarRef
--

newtype VrLVMVarRef ctx v a = VrLVMVarRef Int
type role VrLVMVarRef nominal nominal nominal

registerVrLVMVar :: forall v ctx a.
  ( KnownNat v
  , LinearlyVersionRestrictable ctx a
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (VrLVMVarRef ctx v a), LVMVarRegistry ctx)
registerVrLVMVar a (MkLVMVarRegistry vurs vrs) =
  let !(var :: VrLVMVar ctx v a) = mkVrLVMVar a
      !(L.Ur idx, xs') = L.length vrs
  in (L.Ur (VrLVMVarRef idx), MkLVMVarRegistry vurs (MkAnyVrLVMVar var : xs'))

instance ( KnownNat v
         , LinearlyVersionRestrictable ctx a
         ) =>
         LVMVarReferenciable v (VrLVMVarRef ctx v a) ctx a where
  readLVMVarRef (VrLVMVarRef idx) (MkLVMVarRegistry vurs vrs) =
    let !(ys, zzs) = L.splitAt idx vrs
        !(var :: VrLVMVar ctx v a, zs') = case L.uncons zzs of
          Just (MkAnyVrLVMVar (var_ :: VrLVMVar ctx v_ a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                               -> L.error "Bad VrLVMVarRef index"
    in LVM.do
         (var', a) <- copyLVMVar var
         LVM.pure (a, MkLVMVarRegistry vurs (ys L.++ (MkAnyVrLVMVar var' : zs')))
