{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms        #-}
module Control.LinearlyVersionedMonad.LVMVar where
-- base
import GHC.TypeLits                               (KnownNat, SNat, pattern SNat)
-- linear-base
import Prelude.Linear                             qualified as L
import Unsafe.Linear                              qualified as UnsafeLinear
-- constraints
import Data.Constraint.Linear                     (Dict (Dict))
import Data.Constraint.Unsafe                     (unsafeAxiom)
--
import Control.LinearlyVersionedMonad             as LVM
import Control.LinearlyVersionedMonad.Combinators
import Data.LinearContext


class KnownNat v => UsableLVMVar v var ctx a' | var -> ctx a' where
  useLVMVar :: forall. var ⊸ LVM ctx v v (var, a')

  ejectLVMVar :: forall. var ⊸ LVM ctx v v ()

--
-- Unrestricted LVMVar
--

-- | Linearly version unrestricted data
class KnownNat v => LinearlyVersionUnrestricted v ctx a a' | ctx a v -> a' where
  restrictLinearlyVersioned :: forall. a ⊸ LVM ctx v v (a, a')
  discardLinearlyVersioned :: forall. a ⊸ LVM ctx v v ()

-- | UnRestricted (Ur) linearly-versioned monadic (LVM) value in its version.
data UrLVMVar ctx a a' where
  UrLVMVar :: forall ctx a a'.
    (forall v_. LinearlyVersionUnrestricted v_  ctx a a' => LVM ctx v_ v_ a) ⊸ UrLVMVar ctx a a'

mkUrLVMVar :: forall ctx a a'. a ⊸ UrLVMVar ctx a a'
mkUrLVMVar a = UrLVMVar (MkLVM (Dict, , a))

--
-- Version-Restricted LVMVar
--

-- | Version-Restricted (Vr) linearly-versioned monadic (LVM) value.
data VrLVMVar ctx v a where
  VrLVMVar :: forall ctx v a.
    LVM ctx v v a ⊸ VrLVMVar ctx v a

mkVrLVMVar :: forall ctx v a. KnownNat v =>
  a ⊸ VrLVMVar ctx v a
mkVrLVMVar a = VrLVMVar (MkLVM (Dict, , a) :: LVM ctx v v a)

instance ( KnownNat v
         , LinearlyVersionUnrestricted v ctx a a'
         , ContextualConsumable ctx a
         ) =>
         UsableLVMVar v (UrLVMVar ctx a a') ctx a' where
  useLVMVar (UrLVMVar var) = LVM.do
    a <- unsafeCoerceLVM var
    (a', a'') <- restrictLinearlyVersioned a
    LVM.pure (mkUrLVMVar a', a'')

  ejectLVMVar (UrLVMVar var) = var LVM.>>= eject

instance ( KnownNat v
         , ContextualDupable ctx a
         , ContextualSeqable ctx a a
         ) =>
         UsableLVMVar v (VrLVMVar ctx v a) ctx a where
  useLVMVar (VrLVMVar var) = LVM.do
    a <- var
    (a', a'') <- pass1 a LVM.pure
    LVM.pure (mkVrLVMVar a', a'')

  ejectLVMVar (VrLVMVar var) = var LVM.>>= eject

--
-- VarList
--

-- newtype AnyLVMVar ctx = MkAnyLVMVar (forall var a v. UsableLVMVar var ctx a v =>  var)
data AnyLVMVar ctx where
  MkAnyLVMVar :: forall ctx var a v_. UsableLVMVar v_ var ctx a => SNat v_ -> var ⊸ AnyLVMVar ctx

consLVMVar :: forall ctx.
  AnyLVMVar ctx ⊸ [AnyLVMVar ctx] ⊸ [AnyLVMVar ctx]
consLVMVar x xs = x : xs

clearLVMVarList :: KnownNat v => [AnyLVMVar ctx] ⊸ LVM ctx v v ()
clearLVMVarList []                     = LVM.pure ()
clearLVMVarList (MkAnyLVMVar (SNat @v_) var : xs) = LVM.do
  veryUnsafeCoerceLVM (ejectLVMVar @v_ var)
  clearLVMVarList xs

-- Unsafely coerce version proofs, with the same initial version @va@.
veryUnsafeCoerceLVM :: forall va vb vp vq ctx a.
  LVM ctx va vb a ⊸ LVM ctx vp vq a
veryUnsafeCoerceLVM (MkLVM f) = MkLVM \ctx ->
  let !(d, ctx', a) = f ctx
  in (L.lseq d unsafeAxiom, ctx', a)
