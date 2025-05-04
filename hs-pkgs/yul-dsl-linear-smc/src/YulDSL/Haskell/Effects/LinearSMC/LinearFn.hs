{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE PatternSynonyms        #-}
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
  , ExternalOmniFn, externalOmniFn
    -- $ConstructibleLinearFn
  , lfn', lfn
    -- $MethodBinding
  , bindMethod, (@->)
    -- $CallableFnWithYulVars
  , ycalluv, ycalluv_0, ycall, ycall0
    -- $CallableFnWithYulPorts
  ) where
-- base
import Data.Proxy                                    (Proxy (Proxy))
import GHC.TypeError                                 qualified as TypeError
import GHC.TypeLits                                  (type (+), type (<=))
-- template-haskell
import Language.Haskell.TH                           qualified as TH
-- constraints
import Data.Constraint                               (Dict, withDict)
import Data.Constraint.Unsafe                        (unsafeAxiom)
-- linear-base
import Prelude.Linear
import Unsafe.Linear                                 (toLinear2)
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

instance EquivalentNPOfFunction f xs b =>
         KnownNamedYulCat (StaticFn f) StaticEffect (NP xs) b where
  withKnownNamedYulCat (MkStaticFn f) g = g f

data OmniFn f where
  MkOmniFn :: forall (eff :: LinearEffectKind) f xs b.
              ( KnownYulCatEffect eff
              , AssertOmniEffect eff
              , EquivalentNPOfFunction f xs b
              ) => NamedYulCat eff (NP xs) b ⊸ OmniFn f

instance EquivalentNPOfFunction f xs b =>
         KnownNamedYulCat (OmniFn f) OmniEffect (NP xs) b where
  withKnownNamedYulCat (MkOmniFn f) g = g f

-- | External contract functions that can be called via its selector.
data ExternalOmniFn f where
  MkExternalOmniFn :: forall f xs b. EquivalentNPOfFunction f xs b => SELECTOR -> ExternalOmniFn f

-- | Create a 'ExternalFn' value by providing its function name function form @f@.
externalOmniFn :: forall f xs b.
  ( EquivalentNPOfFunction f xs b
  , YulO2 (NP xs) b
  ) =>
  String -> ExternalOmniFn f
externalOmniFn fname = MkExternalOmniFn (mkTypedSelector @(NP xs) fname)

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
-- $MethodBinding
-- = Binding Methods of Contracts
------------------------------------------------------------------------------------------------------------------------

data BoundMethod ref_contract f xs b where
  MkBoundMethod :: forall ref_contract f xs b.
    EquivalentNPOfFunction f xs b =>
    ( forall v r.
      (KnownNat v, VersionableYulVarRef v r ADDR ref_contract) =>
      Proxy (SNat v, r) -> (Rv v r ADDR, SELECTOR)
    ) ->
    BoundMethod ref_contract f xs b

(@->), bindMethod :: forall ref_contract f xs b.
  ( EquivalentNPOfFunction f xs b
  ) =>
  ref_contract ->
  ExternalOmniFn f ->
  BoundMethod ref_contract f xs b
bindMethod c (MkExternalOmniFn sel) = MkBoundMethod \(_ :: Proxy (SNat v, r)) -> (ver c, sel)
(@->) = bindMethod

------------------------------------------------------------------------------------------------------------------------
-- $CallableFnWithYulVars
-- = Callable Functions Using Yul Variables
------------------------------------------------------------------------------------------------------------------------

--
-- ycall_get_funcobj
--

class (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
      EncodableFn fn eff v r f xs b | fn -> f where
  -- | Get function object from fn
  encodeFnWith'l:: forall c ie oe.
    (YulO1 r, EncodableYulPortDiagram eff ie oe) =>
    fn ->
    (P'x oe r b ⊸ c) ->
    YLVM v v r (P'x ie r (NP xs) ⊸ c)
  default encodeFnWith'l :: forall c ie oe fncls.
    ( YulO1 r, EncodableYulPortDiagram eff ie oe
    , KnownNamedYulCat fn fncls (NP xs) b
    ) =>
    fn ->
    (P'x oe r b ⊸ c) ->
    YLVM v v r (P'x ie r (NP xs) ⊸ c)
  encodeFnWith'l f cont = LVM.pure $
    encodeWith'l @eff (YulJmpU (withKnownNamedYulCat f unsafeCoerceNamedYulCat)) cont

instance (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
         EncodableFn (PureFn f)   PureInputPureOutput v r f xs b

instance (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
         EncodableFn (PureFn f)   (VersionedInputOutput 0) v r f xs b

instance (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
         EncodableFn (StaticFn f) (PureInputVersionedOutput 0) v r f xs b

instance (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
         EncodableFn (StaticFn f) (VersionedInputOutput 0) v r f xs b

instance (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
         EncodableFn (OmniFn f)   (PureInputVersionedOutput vd) v r f xs b

instance (KnownNat v, EquivalentNPOfFunction f xs b, YulO2 (NP xs) b) =>
         EncodableFn (OmniFn f)   (VersionedInputOutput vd) v r f xs b

--
-- ycalluv, ycalluv_0
--

ycalluv :: forall f x xs b v g r.
  ( KnownNat v, YulO4 x (NP xs) b r
  , EncodableFn (PureFn f) PureInputPureOutput v r f (x:xs) b
  , CurriableNP g xs (Ur (Uv r b)) (YulCat'LPP r ()) (YLVM v v r) One (Uv r) One
  , YulVarRef v r (P'P r) (Uv r)
  ) =>
  PureFn f ->
  (Uv r x ⊸ LiftFunction (CurryNP (NP xs) (Ur (Uv r b))) (Uv r) (YLVM v v r) One)
ycalluv f xVar =
  curryNP @g @xs @(Ur (Uv r b)) @(YulCat'LPP r ()) @(YLVM v v r) @One @(Uv r)
  \(MkYulCat'LPP fxs) -> LVM.do
    x <- ytkvar xVar
    let !(x', u) = mkunit'l x
    f' <- encodeFnWith'l @_ @PureInputPureOutput @v f ymkvar
    f' (consNP x' (fxs u))

ycalluv_0 :: forall b v r.
  ( KnownNat v, YulO2 b r
  , EncodableFn (PureFn b) PureInputPureOutput v r b '[] b
  , YulVarRef v r (P'P r) (Uv r)
  ) =>
  PureFn b ->
  LiftFunction (Ur (Uv r b)) (Uv r) (YLVM v v r) One
ycalluv_0 f = LVM.do
  u :: P'P r () <- embed ()
  f' <- encodeFnWith'l @_ @PureInputPureOutput @v f ymkvar
  f' (coerceType'l u)

--
-- ycall
--

class YCallableFunctionNonNil fn f x xs b va vd r | fn -> f vd where
  ycall :: forall vb g.
    ( EncodableFn fn (VersionedInputOutput vd) va r f (x:xs) b
    , YulVarRef vb r (P'V vb r) (Rv vb r)
    , CurriableNP g xs (Ur (Rv vb r b)) (YulCat'LVV va va r ()) (YLVM va vb r) One (Rv va r) Many
    , va + vd ~ vb, KnownNat va, KnownNat vd, KnownNat vb, YulO3 r x (NP xs)
    ) =>
    fn ->
    (Rv va r x -> LiftFunction (CurryNP (NP xs) (Ur (Rv vb r b))) (Rv va r) (YLVM va vb r) Many)
  ycall f xVar =
    -- the axiom proof makes the error messages better:
    toLinear2 (withDict) (unsafeAxiom :: Dict (va <= va + vd)) $
    curryNP @g @xs @(Ur (Rv vb r b)) @(YulCat'LVV va va r ()) @(YLVM va vb r) @_ @(Rv va r) @_
    \(MkYulCat'LVV fxs) -> LVM.do
      x <- ytkvar xVar
      let !(x', u) = mkunit'l x
      f' <- encodeFnWith'l @_ @(VersionedInputOutput vd) @va
            f (\b -> LVM.unsafeCoerceLVM (LVM.pure ()) LVM.>> ymkvar b)
      f' (consNP x' (fxs u))

instance YCallableFunctionNonNil (PureFn f) f x xs b va 0 r
instance YCallableFunctionNonNil (StaticFn f) f x xs b va 0 r
instance YCallableFunctionNonNil (OmniFn f) f x xs b va 1 r

--
-- ycall0
--

class YCallableFunctionNil fn b va vd r | fn -> b vd where
  ycall0 :: forall vb.
    ( EncodableFn fn (VersionedInputOutput vd) va r b '[] b
    , YulVarRef (va + vd) r (P'V (va + vd) r) (Rv (va + vd) r)
    , va + vd ~ vb, KnownNat va,  KnownNat vd, KnownNat vb, YulO2 b r
    ) =>
    fn -> YLVM va (va + vd) r (Ur (Rv (va + vd) r b))
  ycall0 f =
    -- the axiom proof makes the error messages better:
    toLinear2 (withDict) (unsafeAxiom :: Dict (va <= va + vd)) $ LVM.do
    u :: P'V va r () <- embed ()
    f' <- encodeFnWith'l @_ @(VersionedInputOutput vd) @va
          f (\b -> LVM.unsafeCoerceLVM (LVM.pure ()) LVM.>> ymkvar b)
    f' (coerceType'l u)

instance YCallableFunctionNil (PureFn b) b va 0 r
instance YCallableFunctionNil (StaticFn b) b va 0 r
instance YCallableFunctionNil (OmniFn b) b va 1 r

--
-- BoundMethod Support
--

instance ( KnownNat va, YulO2 (NP xs) b, EquivalentNPOfFunction f xs b
         , VersionableYulVarRef va r ADDR ref_contract
         ) =>
         EncodableFn (BoundMethod ref_contract f xs b) (VersionedInputOutput 1) va r f xs b where
  encodeFnWith'l (MkBoundMethod getMethod) cont = LVM.do
    let !(contractVar, sel) = getMethod (Proxy @(SNat va, r))
    contract <- ytkvar contractVar
    u <- embed ()
    let !(gasLimit, value) = dup'l (emb'l 0 u)
    LVM.pure $ \xs -> encodeWith'l @(VersionedInputOutput 1)
                      (YulCall sel) cont (merge'l (be (unsafeCoerceYulPort contract, gasLimit, value), xs))

instance YCallableFunctionNonNil (BoundMethod ref_contract f (x:xs) b) f x xs b va 1 r

instance {-# OVERLAPPABLE #-}
         TypeError.Unsatisfiable (TypeError.Text "You are using ycall0 with a non-nullary function") =>
         YCallableFunctionNil (BoundMethod ref_contract f xs b) f va vd r where
instance YCallableFunctionNil (BoundMethod ref_contract b '[] b) b va 1 r where

--
-- ycallN (FIXME)
--

-- class YLVMCallableFunctionN fn f xs b r va vd | fn -> vd where
--   ycallN :: forall fncls.
--     ( YulO3 (NP xs) b r
--     , EquivalentNPOfFunction f xs b
--     , ConvertibleNPtoTupleN (NP (MapList (P'V va r) xs))
--     , KnownNamedYulCat fn fncls (NP xs) b
--     ) =>
--     fn ->
--     NPtoTupleN (NP (MapList (P'V va r) xs)) ⊸
--     YLVM va (va + vd) r (P'V (va + vd) r b)

-- instance KnownNat va => YLVMCallableFunctionN (PureFn b) b '[] b r va 0 where
--   ycallN (MkPureFn f) () = embed () LVM.>>= \u ->
--     encodeWith'l @(VersionedInputOutput 0) @(VersionedPort va)
--     (YulJmpU (unsafeCoerceNamedYulCat f)) LVM.pure (coerceType'l u)

-- instance forall f x xs b r va.
--          ( KnownNat va
--          , YulO2 x (NP xs)
--          , LinearDistributiveNP (P'V va r) (x:xs)
--          ) =>
--          YLVMCallableFunctionN (PureFn f) f (x:xs) b r va 0 where
--   ycallN (MkPureFn f) tpl = embed () LVM.>>= \u ->
--     let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP (x:xs)) b
--         xxs = linearDistributeNP (fromTupleNtoNP tpl) u :: P'V va r (NP (x:xs))
--     in encodeWith'l (YulJmpU f') LVM.pure xxs

-- instance YLVMCallableFunctionN (PureFn f) f xs b r va 0 =>
--          YLVMCallableFunctionN (StaticFn f) f xs b r va 0 where
--   ycallN (MkStaticFn f) = ycallN (MkPureFn (unsafeCoerceNamedYulCat f))

-- instance ( KnownNat va, KnownNat (va + 1), va <= va + 1
--          ) => YLVMCallableFunctionN (OmniFn b) b '[] b r va 1 where
--   ycallN (MkOmniFn f) () = embed () LVM.>>= \u ->
--     encodeWith'l @(VersionedInputOutput 1) @(VersionedPort va)
--     (YulJmpU (unsafeCoerceNamedYulCat f)) (LVM.unsafeCoerceLVM . LVM.pure) (coerceType'l u)

-- instance forall f x xs b r va.
--          ( KnownNat va, KnownNat (va + 1), va <= va + 1
--          , YulO4 x (NP xs) b r
--          , LinearDistributiveNP (P'V va r) (x:xs)
--          , ConvertibleNPtoTupleN (NP (MapList (P'V va r) (x:xs)))
--          ) =>
--          YLVMCallableFunctionN (OmniFn f) f (x:xs) b r va 1 where
--   ycallN (MkOmniFn f) tpl = embed () LVM.>>= \u ->
--     let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 1) (NP (x:xs)) b
--         xxs = linearDistributeNP (fromTupleNtoNP tpl) u :: P'V va r (NP (x:xs))
--     in encodeWith'l (YulJmpU f') (LVM.unsafeCoerceLVM . LVM.pure) xxs


------------------------------------------------------------------------------------------------------------------------
-- $CallableFnWithYulPorts
-- = Callable Functions Using Yul Ports (FIXME)
------------------------------------------------------------------------------------------------------------------------

--
-- call'l FIXME
--

instance forall f x xs b g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (YulCat'LPP r ()) (P'P r) One (P'P r) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'P r) (P'P r) One where
  call (MkPureFn f') x =
    let !(x', u) = mkunit'l x
    in curryNP @g @xs @b @(YulCat'LPP r ()) @(P'P r) @_ @(P'P r) @_
       \(MkYulCat'LPP fxs) -> encodeWith'l (YulJmpU f') id (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (YulCat'LVV va va r ()) (P'V va r) One (P'V va r) One
         ) =>
         CallableFunctionNP PureFn f x xs b (P'V va r) (P'V va r) One where
  call (MkPureFn f) x =
    let f' = unsafeCoerceNamedYulCat f :: NamedYulCat (VersionedInputOutput 0) (NP (x:xs)) b
        !(x', u) = mkunit'l x
    in curryNP @g @xs @b @(YulCat'LVV va va r ()) @(P'V va r) @_ @(P'V va r)
       \(MkYulCat'LVV fxs) -> encodeWith'l (YulJmpU f') id (consNP x' (fxs u))

instance forall f x xs b va g r.
         ( YulO4 x (NP xs) b r
         , EquivalentNPOfFunction f (x:xs) b
         , CurriableNP g xs b (YulCat'LVV va va r ()) (P'V va r) One (P'V va r) One
         ) =>
         CallableFunctionNP StaticFn f x xs b (P'V va r) (P'V va r) One where
  call (MkStaticFn f) = call (MkPureFn (unsafeCoerceNamedYulCat f))
