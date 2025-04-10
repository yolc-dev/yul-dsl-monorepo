{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
module Control.LinearlyVersionedMonad.LVMVar
  (-- LVMVar type classes
    -- UsableLVMVar (useLVMVar), EjectableLVMVar (ejectLVMVar)
    -- Unrestricted LVMVar
  -- , UrLVMVar, mkUrLVMVar
    -- Version-Restricted LVMVar
    LinearlyVersionRestrictable (LinearlyRestrictedVersion, restrictVersion)
  , VrLVMVar, mkVrLVMVar
    -- LVMVar Registry
  , LVMVarRegistry, initLVMVarRegistry, UrLVMVarRef, VrLVMVarRef
  , addUrLVMVar, addVrLVMVar, takeUrLVMVar, takeVrLVMVar, consumeLVMVarRegistry
  ) where
-- base
import Data.Kind                                  (Type)
import GHC.TypeLits                               (KnownNat, Nat)
import Prelude                                    (type (~))
-- linear-base
import Prelude.Linear                             qualified as L
import Unsafe.Linear                              qualified as UnsafeLinear
-- constraints
import Data.Constraint.Linear                     (Dict (Dict))
--
import Control.LinearlyVersionedMonad             as LVM
import Control.LinearlyVersionedMonad.Combinators
import Data.LinearContext


class KnownNat v => UsableLVMVar v var ctx a' | var -> ctx, var v -> a' where
  useLVMVar :: forall. var ⊸ LVM ctx v v (var, a')

class EjectableLVMVar var ctx | var -> ctx where
  ejectLVMVar :: forall v. KnownNat v => var ⊸ LVM ctx v v ()

--
-- Unrestricted LVMVar
--

-- | Data that is linearly restrictable to any version.
class LinearlyVersionRestrictable ctx a where
  type family LinearlyRestrictedVersion ctx a (v :: Nat) = (a' :: Type) | a' -> ctx
  restrictVersion :: forall v. KnownNat v => a ⊸ LVM ctx v v (a, LinearlyRestrictedVersion ctx a v)

-- | UnRestricted (Ur) linearly-versioned monadic (LVM) value in its version.
data UrLVMVar ctx a where
  UrLVMVar :: forall ctx a.
    LinearlyVersionRestrictable ctx a =>
    (forall v_. KnownNat v_ => LVM ctx v_ v_ a) ⊸ UrLVMVar ctx a

mkUrLVMVar :: forall ctx a.
  LinearlyVersionRestrictable ctx a =>
  a ⊸ UrLVMVar ctx a
mkUrLVMVar a = UrLVMVar (MkLVM (Dict, , a))

--
-- Version-Restricted LVMVar
--

-- | Version-Restricted (Vr) linearly-versioned monadic (LVM) value.
data VrLVMVar ctx v a where
  VrLVMVar :: forall ctx v a.
    LinearlyVersionRestrictable ctx a =>
    LVM ctx v v a ⊸ VrLVMVar ctx v a

mkVrLVMVar :: forall ctx v a.
  ( KnownNat v
  , LinearlyVersionRestrictable ctx a
  ) =>
  a ⊸ VrLVMVar ctx v a
mkVrLVMVar a = VrLVMVar (MkLVM (Dict, , a) :: LVM ctx v v a)

instance ( KnownNat v
         , LinearlyVersionRestrictable ctx a
         , LinearlyRestrictedVersion ctx a v ~ a'
         ) =>
         UsableLVMVar v (UrLVMVar ctx a) ctx a' where
  useLVMVar (UrLVMVar var) = LVM.do
    a <- unsafeCoerceLVM var
    (a', a'') <- restrictVersion a
    LVM.pure (mkUrLVMVar a', a'')

instance ( LinearlyVersionRestrictable ctx a
         , ContextualConsumable ctx a
         ) =>
         EjectableLVMVar (UrLVMVar ctx a) ctx where
  ejectLVMVar (UrLVMVar var) = unsafeCoerceLVM (var LVM.>>= eject)

instance ( KnownNat v
         , ContextualDupable ctx a
         , ContextualSeqable ctx a a
         ) =>
         UsableLVMVar v (VrLVMVar ctx v a) ctx a where
  useLVMVar (VrLVMVar var) = LVM.do
    a <- var
    (a', a'') <- pass1 a LVM.pure
    LVM.pure (mkVrLVMVar a', a'')

instance ( KnownNat v
         , ContextualConsumable ctx a
         ) =>
         EjectableLVMVar (VrLVMVar ctx v a) ctx where
  ejectLVMVar (VrLVMVar var) = veryUnsafeCoerceLVM (var LVM.>>= eject)

--
-- LVMVar Registry
--

data AnyLVMVar ctx where
  MkAnyUrLVMVar :: forall ctx a.
    ( LinearlyVersionRestrictable ctx a
    , ContextualConsumable ctx a
    ) =>
    UrLVMVar ctx a ⊸ AnyLVMVar ctx
  MkAnyVrLVMVar :: forall ctx v a.
    ( KnownNat v
    , ContextualDupable ctx a
    , ContextualSeqable ctx a a
    ) =>
    VrLVMVar ctx v a ⊸ AnyLVMVar ctx

instance EjectableLVMVar (AnyLVMVar ctx) ctx where
  ejectLVMVar (MkAnyUrLVMVar var) = ejectLVMVar var
  ejectLVMVar (MkAnyVrLVMVar var) = ejectLVMVar var

data LVMVarRegistry ctx where
  MkLVMVarRegistry :: forall ctx. [AnyLVMVar ctx] ⊸ LVMVarRegistry ctx

initLVMVarRegistry :: LVMVarRegistry ctx
initLVMVarRegistry = MkLVMVarRegistry []

newtype UrLVMVarRef ctx a = UrLVMVarRef L.Int
type role UrLVMVarRef nominal nominal
newtype VrLVMVarRef ctx v a = VrLVMVarRef L.Int
type role VrLVMVarRef nominal nominal nominal

addUrLVMVar :: forall ctx a.
  ( LinearlyVersionRestrictable ctx a
  , ContextualConsumable ctx a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (UrLVMVarRef ctx a), LVMVarRegistry ctx)
addUrLVMVar a (MkLVMVarRegistry xs) =
  let var = mkUrLVMVar a
      !(L.Ur idx, xs') = L.length xs
  in (L.Ur (UrLVMVarRef idx), MkLVMVarRegistry (MkAnyUrLVMVar var : xs'))

takeUrLVMVar :: forall ctx v a a'.
  ( KnownNat v
  , LinearlyVersionRestrictable ctx a
  , LinearlyRestrictedVersion ctx a v ~ a'
  , ContextualConsumable ctx a
  ) =>
  UrLVMVarRef ctx a ⊸
  LVMVarRegistry ctx ⊸
  LVM ctx v v (a', LVMVarRegistry ctx)
takeUrLVMVar (UrLVMVarRef idx) (MkLVMVarRegistry xs) =
  let !(ys, zs) = L.splitAt idx xs
      !(avar, zs') = case L.uncons zs of
                      L.Just var_zs' -> var_zs'
                      L.Nothing      -> L.error "Bad LVMVarRef index"
      !(var :: UrLVMVar ctx a) = case avar of
              (MkAnyUrLVMVar (var' :: UrLVMVar ctx a_)) -> UnsafeLinear.coerce var'
              (MkAnyVrLVMVar var') -> L.lseq (L.error "Expected UrLVMVar" :: ()) (UnsafeLinear.coerce var')
  in LVM.do
       (var', a) <- useLVMVar var
       LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyUrLVMVar var' : zs')))

addVrLVMVar :: forall v ctx a.
  ( KnownNat v
  , LinearlyVersionRestrictable ctx a
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  ) =>
  a ⊸
  LVMVarRegistry ctx ⊸
  (L.Ur (VrLVMVarRef ctx v a), LVMVarRegistry ctx)
addVrLVMVar a (MkLVMVarRegistry xs) =
  let !(var :: VrLVMVar ctx v a) = mkVrLVMVar a
      !(L.Ur idx, xs') = L.length xs
  in (L.Ur (VrLVMVarRef idx), MkLVMVarRegistry (MkAnyVrLVMVar var : xs'))

takeVrLVMVar :: forall ctx v a.
  ( KnownNat v
  , ContextualDupable ctx a
  , ContextualSeqable ctx a a
  ) =>
  VrLVMVarRef ctx v a ⊸
  LVMVarRegistry ctx ⊸
  LVM ctx v v (a, LVMVarRegistry ctx)
takeVrLVMVar (VrLVMVarRef idx) (MkLVMVarRegistry xs) =
  let !(ys, zs) = L.splitAt idx xs
      !(avar, zs') = case L.uncons zs of
                      L.Just var_zs' -> var_zs'
                      L.Nothing      -> L.error "Bad LVMVarRef index"
      !(var :: VrLVMVar ctx v a) = case avar of
              (MkAnyUrLVMVar var') -> L.lseq (L.error "Expected VrLVMVar" :: ()) (UnsafeLinear.coerce var')
              (MkAnyVrLVMVar (var' :: VrLVMVar ctx v_ a_)) -> UnsafeLinear.coerce var'
  in LVM.do
       (var', a) <- useLVMVar var
       LVM.pure (a, MkLVMVarRegistry (ys L.++ (MkAnyVrLVMVar var' : zs')))

consumeLVMVarRegistry :: forall ctx v. KnownNat v => LVMVarRegistry ctx ⊸ LVM ctx v v ()
consumeLVMVarRegistry (MkLVMVarRegistry [])         = LVM.pure ()
consumeLVMVarRegistry (MkLVMVarRegistry (var : xs)) = LVM.do
  ejectLVMVar var
  consumeLVMVarRegistry (MkLVMVarRegistry xs)
