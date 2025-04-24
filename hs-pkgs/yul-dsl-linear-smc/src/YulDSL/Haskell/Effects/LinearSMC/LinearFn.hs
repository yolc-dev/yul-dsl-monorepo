{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DefaultSignatures      #-}
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
  ( -- $LinearEffects
    StaticFn, OmniFn
    -- $ConstructibleLinearFn
  , lfn', lfn
    -- $CallableLinearFn
  , ycall, ycall0, ycallN
  , externalCall
  ) where
-- base
import GHC.TypeLits                                  (KnownNat, type (+), type (<=))
-- template-haskell
import Language.Haskell.TH                           qualified as TH
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (linearly-versioned-monoad)
import Control.LinearlyVersionedMonad.LVM            qualified as LVM
--
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YLVM
import YulDSL.Haskell.Effects.LinearSMC.YulPort


------------------------------------------------------------------------------------------------------------------------
-- $LinearEffects
-- = Linear Non-Pure Effects
------------------------------------------------------------------------------------------------------------------------

data StaticFn f where
  MkStaticFn :: forall (eff :: LinearEffectKind) f xs b.
                ( KnownYulCatEffect eff
                , AssertStaticEffect eff
                , EquivalentNPOfFunction f xs b
                ) => NamedYulCat eff (NP xs) b ⊸ StaticFn f

instance EquivalentNPOfFunction f xs b => KnownNamedYulCat (StaticFn f) StaticEffect (NP xs) b where
  withKnownNamedYulCat (MkStaticFn f) g = g f

data OmniFn f where
  MkOmniFn :: forall (eff :: LinearEffectKind) f xs b.
              ( KnownYulCatEffect eff
              , AssertOmniEffect eff
              , EquivalentNPOfFunction f xs b
              ) => NamedYulCat eff (NP xs) b ⊸ OmniFn f

instance EquivalentNPOfFunction f xs b => KnownNamedYulCat (OmniFn f) OmniEffect (NP xs) b where
  withKnownNamedYulCat (MkOmniFn f) g = g f

------------------------------------------------------------------------------------------------------------------------
-- $ConstructibleLinearFn
-- = Constructible Linear Functions
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

instance ConstructibleLinearFn PureFn PurePort PurePort where
  lfn' cid f = MkPureFn (cid, decode'l f)

instance ConstructibleLinearFn StaticFn PurePort (VersionedPort 0) where
  lfn' cid f = MkStaticFn (cid, decode'l f)

instance ConstructibleLinearFn StaticFn (VersionedPort 0) (VersionedPort 0) where
  lfn' cid f = MkStaticFn (cid, decode'l f)

instance ( KnownNat vd
         , KnownYulCatEffect (VersionedInputOutput vd)
         , AssertOmniEffect (VersionedInputOutput vd)
         ) =>
         ConstructibleLinearFn OmniFn (VersionedPort 0) (VersionedPort vd) where
  lfn' cid f = MkOmniFn (cid, decode'l f)

instance ( KnownNat vd
         , KnownYulCatEffect (PureInputVersionedOutput vd)
         , AssertOmniEffect (PureInputVersionedOutput vd)
         ) =>
         ConstructibleLinearFn OmniFn PurePort (VersionedPort vd) where
  lfn' cid f = MkOmniFn (cid, decode'l f)

-- | Create a curruying linear function with pure input ports.
lfn :: TH.Q TH.Exp
lfn = [e| lfn' ("$lfn_" ++ $fnLocId) |]

------------------------------------------------------------------------------------------------------------------------
-- $CallableLinearFn
-- = Callable Linear Functions
------------------------------------------------------------------------------------------------------------------------

instance forall f x xs b g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'P r) (P'P r) (YulCat'LPP r ()) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'P r) (P'P r) One where
  call (MkPureFn f') x =
    let !(x', u) = mkunit'l x
    in curryNP @g @xs @b @(P'P r) @(P'P r) @(YulCat'LPP r ()) @One
       \(MkYulCat'LPP fxs) -> encodeWith'l (YulJmpU f') id (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'V va r) (P'V va r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'V va r) (P'V va r) One where
  call (MkPureFn f) x =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP (x:xs)) b
        !(x', u) = mkunit'l x
    in curryNP @g @xs @b @(P'V va r) @(P'V va r) @(YulCat'LVV va va r ()) @One
       \(MkYulCat'LVV fxs) -> encodeWith'l (YulJmpU f') id (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (P'V va r) (P'V va r) (YulCat'LVV va va r ()) One
         ) =>
         CallableFunctionNP StaticFn f x xs b (P'V va r) (P'V va r) One where
  call (MkStaticFn f) = call (MkPureFn (unsafeCoerceNamedYulCat f))

--
-- ycall, ycall0
--

class YulO2 (NP xs) b => YCallableFunction fn xs b vd | fn -> xs b vd where
  -- | Get function object from fn
  ycall_get_funcobj:: fn -> YulCat (VersionedInputOutput vd) (NP xs) b
  default ycall_get_funcobj :: forall fncls.
    KnownNamedYulCat fn fncls (NP xs) b =>
    fn -> YulCat (VersionedInputOutput vd) (NP xs) b
  ycall_get_funcobj f = YulJmpU (withKnownNamedYulCat f unsafeCoerceNamedYulCat)

instance (YulO2 (NP xs) b, EquivalentNPOfFunction f xs b) => YCallableFunction (PureFn f)   xs b 0
instance (YulO2 (NP xs) b, EquivalentNPOfFunction f xs b) => YCallableFunction (StaticFn f) xs b 0
instance (YulO2 (NP xs) b, EquivalentNPOfFunction f xs b) => YCallableFunction (OmniFn f)   xs b 1

class YCallableFunction fn (x:xs) b vd => YCallableFunctionNonNil fn x xs b vd | fn -> x xs b vd where
  ycall :: forall va vb g r.
    ( KnownNat va, KnownNat vb, va <= vb
    , YulO3 r x (NP xs)
    , va + vd ~ vb
    , CurriableNP g xs (Rv vb r b) (Rv va r) (YLVM va vb r) (YulCat'LVV va va r ()) One
    , MakeableYulVarRef vb r (P'V vb r) (Rv vb r)
    ) =>
    fn ->
    (Rv va r x ⊸ LiftFunction (CurryNP (NP xs) (Rv vb r b)) (Rv va r) (YLVM va vb r) One)
  ycall f (Rv xvar) =
    curryNP @g @xs @(Rv vb r b) @(Rv va r) @(YLVM va vb r) @(YulCat'LVV va va r ()) @One
      \(MkYulCat'LVV fxs) -> LVM.do
        x <- ytake1 xvar
        let !(x', u) = mkunit'l x
        encodeWith'l (ycall_get_funcobj f)
          (\b -> LVM.unsafeCoerceLVM (LVM.pure ()) LVM.>> ymkref b)
          (consNP x' (fxs u))

instance YCallableFunction (PureFn f)   (x:xs) b 0 => YCallableFunctionNonNil (PureFn f)   x xs b 0
instance YCallableFunction (StaticFn f) (x:xs) b 0 => YCallableFunctionNonNil (StaticFn f) x xs b 0
instance YCallableFunction (OmniFn f)   (x:xs) b 1 => YCallableFunctionNonNil (OmniFn f)   x xs b 1

class KnownNat vd => YCallableFunctionNil fn vd | fn -> vd where
  ycall0 :: forall va r b.
    ( KnownNat va, KnownNat (va + vd), va <= va + vd
    , YulO2 b r
    , EquivalentNPOfFunction b '[] b
    , YCallableFunction fn '[] b vd
    ) =>
    fn -> YLVM va (va + vd) r (P'V (va + vd) r b)
  ycall0 f = LVM.do
    u <- embed ()
    encodeWith'l @(VersionedInputOutput vd) @(VersionedPort va)
      (ycall_get_funcobj f) (LVM.unsafeCoerceLVM . LVM.pure) (coerceType'l u)

instance YCallableFunctionNil (PureFn f) 0
instance YCallableFunctionNil (StaticFn f) 0
instance YCallableFunctionNil (OmniFn f) 1

--
-- ycallN
--

class YLVMCallableFunctionN fn f xs b r va vd | fn -> vd where
  ycallN :: forall fncls.
    ( YulO3 (NP xs) b r
    , EquivalentNPOfFunction f xs b
    , ConvertibleNPtoTupleN (NP (MapList (P'V va r) xs))
    , KnownNamedYulCat fn fncls (NP xs) b
    ) =>
    fn ->
    NPtoTupleN (NP (MapList (P'V va r) xs)) ⊸
    YLVM va (va + vd) r (P'V (va + vd) r b)

instance KnownNat va => YLVMCallableFunctionN (PureFn b) b '[] b r va 0 where
  ycallN (MkPureFn f) () = embed () LVM.>>= \u ->
    encodeWith'l @(VersionedInputOutput 0) @(VersionedPort va)
    (YulJmpU (unsafeCoerceNamedYulCat f)) LVM.pure (coerceType'l u)

instance forall f x xs b r va.
         ( KnownNat va
         , YulO2 x (NP xs)
         , LinearDistributiveNP (P'V va r) (x:xs)
         ) =>
         YLVMCallableFunctionN (PureFn f) f (x:xs) b r va 0 where
  ycallN (MkPureFn f) tpl = embed () LVM.>>= \u ->
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP (x:xs)) b
        xxs = linearDistributeNP (fromTupleNtoNP tpl) u :: P'V va r (NP (x:xs))
    in encodeWith'l (YulJmpU f') LVM.pure xxs

instance YLVMCallableFunctionN (PureFn f) f xs b r va 0 =>
         YLVMCallableFunctionN (StaticFn f) f xs b r va 0 where
  ycallN (MkStaticFn f) = ycallN (MkPureFn (unsafeCoerceNamedYulCat f))

instance ( KnownNat va, KnownNat (va + 1), va <= va + 1
         ) => YLVMCallableFunctionN (OmniFn b) b '[] b r va 1 where
  ycallN (MkOmniFn f) () = embed () LVM.>>= \u ->
    encodeWith'l @(VersionedInputOutput 1) @(VersionedPort va)
    (YulJmpU (unsafeCoerceNamedYulCat f)) (LVM.unsafeCoerceLVM . LVM.pure) (coerceType'l u)

instance forall f x xs b r va.
         ( KnownNat va, KnownNat (va + 1), va <= va + 1
         , YulO4 x (NP xs) b r
         , LinearDistributiveNP (P'V va r) (x:xs)
         , ConvertibleNPtoTupleN (NP (MapList (P'V va r) (x:xs)))
         ) =>
         YLVMCallableFunctionN (OmniFn f) f (x:xs) b r va 1 where
  ycallN (MkOmniFn f) tpl = embed () LVM.>>= \u ->
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 1) (NP (x:xs)) b
        xxs = linearDistributeNP (fromTupleNtoNP tpl) u :: P'V va r (NP (x:xs))
    in encodeWith'l (YulJmpU f') (LVM.unsafeCoerceLVM . LVM.pure) xxs

------------------------------------------------------------------------------------------------------------------------
-- calling external functions (Yul Monadic)
------------------------------------------------------------------------------------------------------------------------

externalCall :: forall f x xs b g b' r v1 addrEff.
  ( KnownNat v1, KnownNat (v1 + 1), v1 <= v1 + 1
  , YulO4 x (NP xs) b r
  , P'V (v1 + 1) r b ~ b'
  , EquivalentNPOfFunction f (x:xs) b
  , EquivalentNPOfFunction g xs b'
  , CurriableNP g xs b' (P'V v1 r) (YLVM v1 (v1 + 1) r) (YulCat'LVV v1 v1 r ()) One
  ) =>
  ExternalFn f ->
  P'x addrEff r ADDR ⊸
  (P'V v1 r x ⊸ LiftFunction (CurryNP (NP xs) b') (P'V v1 r) (YLVM v1 (v1 + 1) r) One)
externalCall (MkExternalFn sel) addr x =
  mkunit'l x
  & \(x', u) ->
      curryNP @g @xs @b' @(P'V v1 r) @(YLVM v1 (v1 + 1) r) @(YulCat'LVV v1 v1 r ()) @One
      $ \(MkYulCat'LVV fxs) -> encodeWith'l
                               @(VersionedInputOutput 1) @(VersionedPort v1) @(VersionedPort (v1 + 1))
                               @_ @_ @_ {- r a b -}
                               @(YLVM v1 (v1 + 1) r b')
                               YulId
                               (\b' -> LVM.unsafeCoerceLVM
                                       (LVM.pure b' :: YLVM v1 v1 r (P'V (v1 + 1) r b))
                                       :: YLVM v1 (v1 + 1) r (P'V (v1 + 1) r b))
                               $ go (consNP x' (fxs u))
  where go :: forall. P'x (VersionedPort v1) r (NP (x : xs)) ⊸ P'V v1 r b
        go args = let !(args', u) = mkunit'l args
                      !(gasLimit, value) = dup'l (emb'l 0 u)
                  in encodeWith'l @(VersionedInputOutput 0) @(VersionedPort v1) @(VersionedPort v1)
                     (YulCall sel)
                     id
                     (merge'l (be (unsafeCoerceYulPort addr, gasLimit, value), args'))
