{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Control.LinearlyVersionedMonad.LVMVar
  ( -- * Linearly Version Restrictable Data
    LinearlyVersionRestrictable (VersionRestrictedData, restrictVersion)
    -- * LVMVar Registry
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


----------------------------------------------------------------------------------------------------
-- LinearlyVersionRestrictable: Uv & Vr LVMVar
----------------------------------------------------------------------------------------------------

-- | Data that is linearly restrictable to any version.
class KnownNat v =>  LinearlyVersionRestrictable v ctx a where
  type family VersionRestrictedData v ctx a = (a' :: Type) | a' -> ctx
  restrictVersion :: forall. a ⊸ LVM.LVM ctx v v (VersionRestrictedData v ctx a)

class (KnownNat v, LinearlyVersionRestrictable v ctx a) => UsableLVMVar v var ctx a | var -> ctx a where
  copyLVMVar :: forall. var ⊸ LVM.LVM ctx v v (var, a)

--
-- Unrestricted-in-version (Uv) LVMVar
--

-- | Linearly-versioned monadic (LVM) value unrestricted in its version (Uv).
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
-- Restricted-in-version (Rv) LVMVar
--

-- | Linearly-versioned monadic (LVM) value restricted in version (Rv).
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

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         UsableLVMVar v (RvLVMVar ctx v a) ctx a where
  copyLVMVar (RvLVMVar var) = LVM.do
    a <- var
    (a', a'') <- pass1 a LVM.pure
    LVM.pure (mkRvLVMVar a', a'')

----------------------------------------------------------------------------------------------------
-- LVMVar Registry
----------------------------------------------------------------------------------------------------

data LVMVarRegistry ctx where
  MkLVMVarRegistry :: forall ctx.
    [AnyUvLVMVar ctx] ⊸
    [AnyRvLVMVar ctx] ⊸
    LVMVarRegistry ctx

initLVMVarRegistry :: LVMVarRegistry ctx
initLVMVarRegistry = MkLVMVarRegistry [] []

consumeLVMVarRegistry :: forall ctx v. KnownNat v => LVMVarRegistry ctx ⊸ LVM.LVM ctx v v ()
consumeLVMVarRegistry (MkLVMVarRegistry uvs vrs) = go1 uvs LVM.>> go2 vrs
  where go1 ([])                                = LVM.pure ()
        go1 (MkAnyUvLVMVar (UvLVMVar var) : xs) = LVM.unsafeCoerceLVM (var LVM.>>= eject) LVM.>> go1 xs
        go2 ([])                                = LVM.pure ()
        go2 (MkAnyRvLVMVar (RvLVMVar var) : xs) = LVM.veryUnsafeCoerceLVM (var LVM.>>= eject) LVM.>> go2 xs

class ( KnownNat v
      , LinearlyVersionRestrictable v ctx a
      ) =>
      ReferenciableLVMVar v ref ctx a | v ref -> ctx a where
  takeLVMVarRef :: forall. ref ⊸ LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (a, LVMVarRegistry ctx)

  takevLVMVarRef :: forall ar.
    VersionRestrictedData v ctx a ~ ar =>
    ref ⊸ LVMVarRegistry ctx ⊸ LVM.LVM ctx v v (ar, LVMVarRegistry ctx)
  takevLVMVarRef ref registry = LVM.do
    (a, registry') <- takeLVMVarRef ref registry
    a' <- restrictVersion a
    LVM.pure (a', registry')

--
-- UvLVMVarRef
--

data UvLVMVarRef ctx a where
  MkUvLVMVarRef :: Int -> UvLVMVarRef ctx a
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
  in (L.Ur (MkUvLVMVarRef ridx), MkLVMVarRegistry (MkAnyUvLVMVar var : uvs') vrs)

instance ( KnownNat v
         , LinearlyVersionRestrictable v ctx a
         ) =>
         ReferenciableLVMVar v (UvLVMVarRef ctx a) ctx a where
  takeLVMVarRef (MkUvLVMVarRef ridx) (MkLVMVarRegistry uvs vrs) =
    let !(L.Ur len, uvs') = L.length uvs
        !(ys, zzs) = L.splitAt (len - ridx - 1) uvs'
        !(var :: UvLVMVar ctx a, zs') = case L.uncons zzs of
          Just (MkAnyUvLVMVar (var_ :: UvLVMVar ctx a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                            -> L.error "Bad UvLVMVarRef index"
    in LVM.do
         (var', a) <- copyLVMVar var
         LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyUvLVMVar var' : zs')) vrs)

--
-- RvLVMVarRef
--

data RvLVMVarRef ctx v a where
  MkRvLVMVarRef  :: forall v ctx a.  -- ^ Restricted version variable reference.
    Int ->
    RvLVMVarRef ctx v a
  VerUvLVMVarRef :: forall v ctx ua. -- ^ 'UvLVMVarRef' that got restricted.
    LinearlyVersionRestrictable v ctx ua =>
    UvLVMVarRef ctx ua ->
    RvLVMVarRef ctx v (VersionRestrictedData v ctx ua)
type role RvLVMVarRef nominal nominal nominal

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
          Just (MkAnyRvLVMVar (var_ :: RvLVMVar ctx v_ a_), zs) -> (UnsafeLinear.coerce var_, zs)
          Nothing                                               -> L.error "Bad RvLVMVarRef index"
    in LVM.do
         (var', a) <- copyLVMVar var
         LVM.pure (a, MkLVMVarRegistry vurs (ys L.++ (MkAnyRvLVMVar var' : zs')))
  takeLVMVarRef (VerUvLVMVarRef uv) rgstr = LVM.do
    (ua, rgstr') <- takeLVMVarRef uv rgstr
    ar <- restrictVersion ua
    LVM.pure (ar, rgstr')
