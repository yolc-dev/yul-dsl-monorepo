{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Control.LinearlyVersionedMonad.LVMVar
  ( -- * Linearly Version Restrictable Data
    LinearlyVersionRestrictable (LinearlyRestrictedVersion, restrictVersion)
    -- * LVMVar Registry
  , LVMVarRegistry, initLVMVarRegistry, consumeLVMVarRegistry
  , LVMVarReferenciable (takeLVMVarRef, takevLVMVarRef)
  , UvLVMVarRef, registerUvLVMVar
  , VrLVMVarRef, registerVrLVMVar
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


----------------------------------------------------------------------------------------------------
-- LinearlyVersionRestrictable: Uv & Vr LVMVar
----------------------------------------------------------------------------------------------------

-- | Data that is linearly restrictable to any version.
class KnownNat v =>  LinearlyVersionRestrictable v ctx a where
  type family LinearlyRestrictedVersion ctx a v = (a' :: Type) | a' -> ctx
  restrictVersion :: forall. a ⊸ LVM.LVM ctx v v (LinearlyRestrictedVersion ctx a v)

class (KnownNat v, LinearlyVersionRestrictable v ctx a) => UsableLVMVar v var ctx a | var -> ctx a where
  copyLVMVar :: forall. var ⊸ LVM.LVM ctx v v (var, a)

--
-- Unrestricted-version (Uv) LVMVar
--

-- | Restricted-version (Uv) linearly-versioned monadic (LVM) value in its version.
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

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         UsableLVMVar v (UvLVMVar ctx a) ctx a where
  copyLVMVar (UvLVMVar var) = LVM.do
    a <- LVM.unsafeCoerceLVM var
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
    , LinearlyVersionRestrictable v ctx a
    ) =>
    LVM.LVM ctx v v a ⊸ VrLVMVar ctx v a

data AnyVrLVMVar ctx where MkAnyVrLVMVar :: forall ctx v_ a. VrLVMVar ctx v_ a ⊸ AnyVrLVMVar ctx

mkVrLVMVar :: forall ctx v a.
  ( KnownNat v
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  , LinearlyVersionRestrictable v ctx a
  ) =>
  a ⊸ VrLVMVar ctx v a
mkVrLVMVar a = VrLVMVar (LVM.MkLVM (Dict, , a) :: LVM.LVM ctx v v a)

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
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

consumeLVMVarRegistry :: forall ctx v. KnownNat v => LVMVarRegistry ctx ⊸ LVM.LVM ctx v v ()
consumeLVMVarRegistry (MkLVMVarRegistry uvs vrs) = go1 uvs LVM.>> go2 vrs
  where go1 ([])                                = LVM.pure ()
        go1 (MkAnyUvLVMVar (UvLVMVar var) : xs) = LVM.unsafeCoerceLVM (var LVM.>>= eject) LVM.>> go1 xs
        go2 ([])                                = LVM.pure ()
        go2 (MkAnyVrLVMVar (VrLVMVar var) : xs) = LVM.veryUnsafeCoerceLVM (var LVM.>>= eject) LVM.>> go2 xs

class ( KnownNat v
      , LinearlyVersionRestrictable v ctx a
      ) =>
      LVMVarReferenciable v ref ctx a | v ref -> ctx a where
  takeLVMVarRef :: forall. ref ⊸ LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (a, LVMVarRegistry ctx)

  takevLVMVarRef :: forall a'.
    LinearlyRestrictedVersion ctx a v ~ a' =>
    ref ⊸ LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (a', LVMVarRegistry ctx)
  takevLVMVarRef ref registry = LVM.do
    (a, registry') <- takeLVMVarRef ref registry
    a' <- restrictVersion a
    LVM.pure (a', registry')

--
-- UvLVMVarRef
--

data UvLVMVarRef ctx a where UvLVMVarRef :: Int -> UvLVMVarRef ctx a
type role UvLVMVarRef nominal nominal

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
  in (L.Ur (UvLVMVarRef ridx), MkLVMVarRegistry (MkAnyUvLVMVar var : uvs') vrs)

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         LVMVarReferenciable v (UvLVMVarRef ctx a) ctx a where
  takeLVMVarRef (UvLVMVarRef ridx) (MkLVMVarRegistry uvs vrs) =
    let !(L.Ur len, uvs') = L.length uvs
        !(ys, zzs) = L.splitAt (len - ridx - 1) uvs'
        !(var :: UvLVMVar ctx a, zs') = case L.uncons zzs of
          Just (MkAnyUvLVMVar (var_ :: UvLVMVar ctx a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                            -> L.error "Bad UvLVMVarRef index"
    in LVM.do
         (var', a) <- copyLVMVar var
         LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyUvLVMVar var' : zs')) vrs)

--
-- VrLVMVarRef
--

data VrLVMVarRef ctx v a where VrLVMVarRef :: Int -> VrLVMVarRef ctx v a
type role VrLVMVarRef nominal nominal nominal

registerVrLVMVar :: forall v ctx a.
  ( KnownNat v
  , LinearlyVersionRestrictable v ctx a
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (VrLVMVarRef ctx v a), LVMVarRegistry ctx)
registerVrLVMVar a (MkLVMVarRegistry vurs vrs) =
  let !(var :: VrLVMVar ctx v a) = mkVrLVMVar a
      !(L.Ur ridx, xs') = L.length vrs
  in (L.Ur (VrLVMVarRef ridx), MkLVMVarRegistry vurs (MkAnyVrLVMVar var : xs'))

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         LVMVarReferenciable v (VrLVMVarRef ctx v a) ctx a where
  takeLVMVarRef (VrLVMVarRef ridx) (MkLVMVarRegistry vurs vrs) =
    let !(L.Ur len, vrs') = L.length vrs
        !(ys, zzs) = L.splitAt (len - ridx - 1) vrs'
        !(var :: VrLVMVar ctx v a, zs') = case L.uncons zzs of
          Just (MkAnyVrLVMVar (var_ :: VrLVMVar ctx v_ a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                               -> L.error "Bad VrLVMVarRef index"
    in LVM.do
         (var', a) <- copyLVMVar var
         LVM.pure (a, MkLVMVarRegistry vurs (ys L.++ (MkAnyVrLVMVar var' : zs')))
