{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE UndecidableInstances   #-}
module YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
  ( -- $LinearEffectKind
    LinearEffectKind (PureInputPureOutput, PureInputVersionedOutput, VersionedInputOutput)
  , LinearEffectVersionDelta
    -- $YulPortDiagrams
  , YulCat'LVV (MkYulCat'LVV), YulCat'LPV (MkYulCat'LPV), YulCat'LPP (MkYulCat'LPP)
  , DecodableYulPortDiagram (decode'l)
  , EncodableYulPortDiagram (encodeWith'l)
  , yulports'pp, yulports'pv, yulports'vv
  ) where
-- base
import GHC.TypeLits                             (type (+))
-- linear-base
import Prelude.Linear
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort


------------------------------------------------------------------------------------------------------------------------
-- $LinearEffectKind
--
-- = Linear Effect Kind
------------------------------------------------------------------------------------------------------------------------

-- | Various types of linear effects for the yul category.
--
-- Note that the pure input pure output linear effect is included. For that, use the pure effect from the 'YulDSL.core'
-- directly.
data LinearEffectKind = PureInputPureOutput          -- ^ Pure input ports, pure output ports
                      | PureInputVersionedOutput Nat -- ^ Pure input ports, versioned output ports
                      | VersionedInputOutput Nat     -- ^ Versioned input and output ports

-- | Extract Linear effect version delta.
type family LinearEffectVersionDelta (eff :: LinearEffectKind) :: Nat where
  LinearEffectVersionDelta PureInputPureOutput           = 0
  LinearEffectVersionDelta (VersionedInputOutput vd)     = vd
  LinearEffectVersionDelta (PureInputVersionedOutput vd) = vd

-- Note: Using (<=?) from TypeLits would require UndecidableInstances because it is a nested type family application.
type family IsNoneZero (vd :: Nat) :: Bool where
  IsNoneZero 0 = False
  IsNoneZero vd = True

type instance IsEffectNonPure PureInputPureOutput = False
type instance MayAffectWorld PureInputPureOutput = False
instance KnownYulCatEffect PureInputPureOutput

type instance IsEffectNonPure (PureInputVersionedOutput _) = True
type instance MayAffectWorld (PureInputVersionedOutput vd) = IsNoneZero vd
instance (KnownNat vd, KnownBool (IsNoneZero vd)) => KnownYulCatEffect (PureInputVersionedOutput vd)

type instance IsEffectNonPure (VersionedInputOutput _) = True
type instance MayAffectWorld (VersionedInputOutput vd) = IsNoneZero vd
instance (KnownNat vd, KnownBool (IsNoneZero vd)) => KnownYulCatEffect (VersionedInputOutput vd)

------------------------------------------------------------------------------------------------------------------------
-- $YulPortDiagrams
--
-- = Yul Port Diagrams
--
-- A yul port diagram is a morphism in the yul category represented by one input yul port and one output yul port.
--
-- There are three variants with different purity for input and output ports as their names suggest, where V means
-- versioned and P means pure.
--
-- Additionally, they are data types instead of type synonyms because of GHC's lack of type-level lambda support. As a
-- result, each of them also comes with an unYulCat function to unwrap them linearly.
------------------------------------------------------------------------------------------------------------------------

-- | Yul port diagram for versioned input and outputs.
newtype YulCat'LVV v1 vn r a b = MkYulCat'LVV (P'V v1 r a ⊸ P'V vn r b)

-- | Yul port diagram for pure input and versioned outputs.
newtype YulCat'LPV vn r a b = MkYulCat'LPV (P'P r a ⊸ P'V vn r b)

-- | Yul port diagram for pure input and pure outputs.
newtype YulCat'LPP r a b = MkYulCat'LPP (P'P r a ⊸ P'P r b)

-- | Decodable yul port diagrams.
class DecodableYulPortDiagram ie oe eff | ie oe -> eff where
  -- | Decode a linear yul port function to a yul port diagrams.
  decode'l :: forall a b.
    YulO2 a b =>
    (forall r. YulO1 r => P'x ie r a ⊸ P'x oe r b) ->
    YulCat eff a b
  decode'l f = YulUnsafeCoerceEffect (decodeP'x (unsafeCoerceYulPortDiagram f))

instance DecodableYulPortDiagram (VersionedPort 0) (VersionedPort vd) (VersionedInputOutput vd)
instance DecodableYulPortDiagram PurePort (VersionedPort vd) (PureInputVersionedOutput vd)
instance DecodableYulPortDiagram PurePort PurePort Pure

-- | Encodable yul port diagrams.
class EncodableYulPortDiagram eff ie oe | eff ie -> oe where
  --  | Encode a yul port diagrams to a yul port function with a continuation.
  --
  --  Note: @r@ is a skolem type variable from port encoding. The continuation is the way to allow access to it.
  encodeWith'l :: forall r a b c.
    YulO3 r a b =>
    YulCat eff a b ->
    (P'x oe r b ⊸ c) ->
    (P'x ie r a ⊸ c)
  encodeWith'l c f x = f (unsafeCoerceYulPort (encodeP'x (YulUnsafeCoerceEffect c) x))

instance EncodableYulPortDiagram Pure PurePort PurePort

instance EncodableYulPortDiagram PureInputPureOutput PurePort PurePort

instance va + vd ~ vb => EncodableYulPortDiagram (PureInputVersionedOutput vd) (VersionedPort va) (VersionedPort vd)

-- instance EncodableYulPortDiagram (VersionedInputOutput vd) PurePort (VersionedPort vd)

instance va + vd ~ vb => EncodableYulPortDiagram (VersionedInputOutput vd) (VersionedPort va) (VersionedPort vb)

unsafe_uncurry_nil :: forall a b r ie oe m1.
  YulO3 a b r =>
  P'x oe r b ⊸
  (m1 a ⊸ P'x ie r (NP '[])) ->
  (m1 a ⊸ P'x oe r b)
unsafe_uncurry_nil b h a =
  h a                   -- :: P'x ie v1 (NP '[])
  & coerceType'l @_ @() -- :: P'x ie v1 ()
  & unsafeCoerceYulPort -- :: P'x ie vn ()
  & \u -> ignore'l u b

uncurry_nonnil :: forall m1 m2_ m2b_ m2 mb g x xs b r a ie.
  ( YulO4 x (NP xs) r a
  , UncurriableNP g xs b m1 mb One (m2_ a) (m2b_ a) One
  --
  , P'x ie r ~ m1
  , m1 ~ m2
  ) =>
  (m1 x ⊸ LiftFunction g m1 mb One) ->    -- ^ f: m1 x ⊸ m1 (xs ⊸...) ⊸ m1b b; the function to be uncurried
  (m2 a ⊸ m2 (NP (x : xs))) ->             -- ^ h: m2' (a ⊸ NP xxs)
  ((m2 a ⊸ m2 (NP xs)) ⊸ m2_ a (NP xs)) -> -- ^ mk: m2' (a ⊸ NP xs) ⊸ m2_ a (NP xs)
  (m2b_ a b ⊸ (m2 a ⊸ mb b)) ->         -- ^ un: m2b_ a b ⊸ (m2' a ⊸ m2b' b)
  (m2 a ⊸ mb b)
uncurry_nonnil f h mk un a =
  let !(a1, a2) = dup'l a
      !(x, xs) = unconsNP (h a1)
  in let g = uncurryNP @g @xs @b @m1 @mb @One @(m2_ a) @(m2b_ a) @One
             (f x)
             (mk (const'l xs))
     in (un g) a2

------------------------------------------------------------------------------------------------------------------------
-- (P'P ⊸ P'P ⊸ ... P'P) <=> YulCat'LPP
------------------------------------------------------------------------------------------------------------------------

instance forall b r a.
         ( YulO3 b a r
         , EquivalentNPOfFunction b '[] b
         , LiftFunction b (P'P r) (P'P r) One ~ P'P r b
         , LiftFunction b (YulCat'LPP r a) (YulCat'LPP r a) One ~ YulCat'LPP r a b
         ) =>
         UncurriableNP b '[] b (P'P r) (P'P r) One (YulCat'LPP r a) (YulCat'LPP r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPP (unsafe_uncurry_nil b h)

instance forall x xs b g r a.
         ( YulO5 x (NP xs) b r a
         , UncurriableNP g xs b (P'P r) (P'P r) One (YulCat'LPP r a) (YulCat'LPP r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) b (P'P r) (P'P r) One (YulCat'LPP r a) (YulCat'LPP r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPP (uncurry_nonnil f h MkYulCat'LPP (\(MkYulCat'LPP g) -> g))

-- | Convert a currying function to a yul port diagram of pure input and pure output.
yulports'pp :: forall f xs b r m1 m1b m2 m2b.
  ( YulO3 (NP xs) b r
  --
  , P'P r ~ m1
  , P'P r ~ m1b
  , YulCat'LPP r (NP xs)    ~ m2
  , YulCat'LPP r (NP xs) ~ m2b
  , UncurriableNP f xs b m1 m1b One m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'P r (NP xs) ⊸ P'P r b)
yulports'pp f = let !(MkYulCat'LPP f') = (uncurryNP @f @xs @b @m1 @m1b @_ @m2 @m2b @_ f (MkYulCat'LPP id)) in f'

instance forall b r a.
         ( YulO3 b r a
         , EquivalentNPOfFunction b '[] b
         , LiftFunction (CurryNP (NP '[]) b) (P'P r) (P'P r) One ~ P'P r b
         , LiftFunction (CurryNP (NP '[]) b) (YulCat'LPP r a) (P'P r) One ~ P'P r b
         ) =>
         CurriableNP b '[] b (YulCat'LPP r a) (P'P r) One (P'P r) One where
  curryNP fNP = fNP (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall g x xs b r a.
         ( YulO5 x (NP xs) b r a
         , CurriableNP g xs b (YulCat'LPP r a) (P'P r) One (P'P r) One
         ) =>
         CurriableNP (x -> g) (x:xs) b (YulCat'LPP r a) (P'P r) One (P'P r) One where
  curryNP fNP x = curryNP @g @xs @b @(YulCat'LPP r a) @(P'P r) @_ @(P'P r) @_
                  (\(MkYulCat'LPP fxs) -> fNP (MkYulCat'LPP (\a -> (consNP (unsafeCoerceYulPort x) (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- (P'P r x1 ⊸ P'P r x2 ⊸ ... P'V vd r b) <=> YulCat'LPV vd r (NP xs) b
------------------------------------------------------------------------------------------------------------------------

instance forall b vd r a.
         ( YulO3 b a r
         , EquivalentNPOfFunction b '[] b
         , LiftFunction b (P'P r) (P'V vd r) One ~ P'V vd r b
         , LiftFunction b (YulCat'LPP r a) (YulCat'LPV vd r a) One ~ YulCat'LPV vd r a b
         ) =>
         UncurriableNP b '[] b (P'P r) (P'V vd r) One (YulCat'LPP r a) (YulCat'LPV vd r a) One where
  uncurryNP b (MkYulCat'LPP h) = MkYulCat'LPV (unsafe_uncurry_nil b h)

instance forall x xs b g vd r a.
         ( YulO5 x (NP xs) b r a
         , UncurriableNP g xs b (P'P r) (P'V vd r) One (YulCat'LPP r a) (YulCat'LPV vd r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) b (P'P r) (P'V vd r) One (YulCat'LPP r a) (YulCat'LPV vd r a) One where
  uncurryNP f (MkYulCat'LPP h) = MkYulCat'LPV (uncurry_nonnil f h MkYulCat'LPP (\(MkYulCat'LPV g) -> g))

-- | Convert a currying function to a yul port diagram of pure input and versioned output.
yulports'pv :: forall f xs b r vd m1 m1b m2 m2b.
  ( YulO3 (NP xs) b r
  --
  , P'P    r ~ m1
  , P'V vd r ~ m1b
  , YulCat'LPP r (NP xs)    ~ m2
  , YulCat'LPV vd r (NP xs) ~ m2b
  , UncurriableNP f xs b m1 m1b One m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'P r (NP xs) ⊸ P'V vd r b)
yulports'pv f = let !(MkYulCat'LPV f') = (uncurryNP @f @xs @b @m1 @m1b @_ @m2 @m2b @_ f (MkYulCat'LPP id)) in f'

instance forall b v1 vn r a.
         ( YulO3 b r a
         , EquivalentNPOfFunction b '[] b
         , LiftFunction (CurryNP (NP '[]) b) (P'P r) (P'V vn r) One ~ P'V vn r b
         , LiftFunction (CurryNP (NP '[]) b) (YulCat'LVV v1 v1 r a) (P'V vn r) One ~ P'V vn r b
         ) =>
         CurriableNP b '[] b (YulCat'LVV v1 v1 r a) (P'V vn r) One (P'P r) One where
  curryNP fNP = fNP (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall g x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurriableNP g xs b (YulCat'LVV v1 v1 r a) (P'V vn r) One (P'P r) One
         ) =>
         CurriableNP (x -> g) (x:xs) b (YulCat'LVV v1 v1 r a) (P'V vn r) One (P'P r) One where
  curryNP cb x = curryNP @g @xs @b @(YulCat'LVV v1 v1 r a) @(P'V vn r) @_ @(P'P r) @_
                 (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (consNP (unsafeCoerceYulPort x) (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- (P'V v1 r x1 ⊸ P'V v1 r x2 ⊸ ... P'V vn r b) <=> YulCat'LVV v1 vn r (NP xs) b
------------------------------------------------------------------------------------------------------------------------

instance forall b v1 vn r a.
         ( YulO3 b r a
         , EquivalentNPOfFunction b '[] b
         , LiftFunction b (P'V v1 r) (P'V vn r) One ~ P'V vn r b
         , LiftFunction b (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One ~ YulCat'LVV v1 vn r a b
         ) =>
         UncurriableNP b '[] b (P'V v1 r) (P'V vn r) One (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One where
  uncurryNP b (MkYulCat'LVV h) = MkYulCat'LVV (unsafe_uncurry_nil b h)

instance forall g x xs b v1 vn r a.
         ( YulO5 x (NP xs) b r a
         , UncurriableNP g xs b (P'V v1 r) (P'V vn r) One (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One
         ) =>
         UncurriableNP (x -> g) (x:xs) b (P'V v1 r) (P'V vn r) One (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One where
  uncurryNP f (MkYulCat'LVV h) = MkYulCat'LVV (uncurry_nonnil f h MkYulCat'LVV (\(MkYulCat'LVV g) -> g))

-- | Convert a currying function to a yul port diagram of versioned input output.
yulports'vv :: forall f xs b r vd m1 m1b m2 m2b.
  ( YulO3 (NP xs) b r
  --
  , P'V  0 r ~ m1
  , P'V vd r ~ m1b
  , YulCat'LVV 0  0 r (NP xs) ~ m2
  , YulCat'LVV 0 vd r (NP xs) ~ m2b
  , UncurriableNP f xs b m1 m1b One m2 m2b One
  ) =>
  LiftFunction f m1 m1b One ->
  (P'V 0 r (NP xs) ⊸ P'V vd r b)
yulports'vv f = let !(MkYulCat'LVV f') = uncurryNP @f @xs @b @m1 @m1b @_ @m2 @m2b @_ f (MkYulCat'LVV id) in f'

instance forall b v1 vn r a.
         ( YulO3 b r a
         , EquivalentNPOfFunction b '[] b
         , LiftFunction (CurryNP (NP '[]) b) (P'V v1 r) (P'V vn r) One ~ P'V vn r b
         , LiftFunction (CurryNP (NP '[]) b) (YulCat'LVV v1 v1 r a) (P'V vn r) One ~ P'V vn r b
         ) =>
         CurriableNP b '[] b (YulCat'LVV v1 v1 r a) (P'V vn r) One (P'V v1 r) One where
  curryNP cb = cb (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall g x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurriableNP g xs b (YulCat'LVV v1 v1 r a) (P'V vn r) One (P'V v1 r) One
         ) =>
         CurriableNP (x -> g) (x:xs) b (YulCat'LVV v1 v1 r a) (P'V vn r) One (P'V v1 r) One where
  curryNP cb x = curryNP @g @xs @b @(YulCat'LVV v1 v1 r a) @(P'V vn r) @_ @(P'V v1 r) @_
                 (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (consNP x (fxs a)))))
