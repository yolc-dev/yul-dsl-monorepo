{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
module YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
  ( -- * Linear Effect Kind
    -- $LinearEffectKind
    LinearEffectKind (PureInputVersionedOutput, VersionedInputOutput)
  , LinearEffectVersionDelta, IsLinearEffectNonStatic
    -- * Yul Port Diagrams
    -- $YulPortDiagrams
  , YulCat'LVV (MkYulCat'LVV), YulCat'LPV (MkYulCat'LPV), YulCat'LPP (MkYulCat'LPP)
  , DecodableYulPortDiagram (decode'l)
  , EncodableYulPortDiagram (encodeWith'l)
  , uncurry'lvv, uncurry'lpv
  ) where
-- base
import GHC.TypeLits                             (KnownNat, type (+))
import Prelude                                  qualified as BasePrelude
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.Lib                       (PureEffectKind (Pure))
--
import YulDSL.Haskell.Effects.LinearSMC.YulPort


------------------------------------------------------------------------------------------------------------------------
-- $LinearEffectKind
------------------------------------------------------------------------------------------------------------------------

-- | Various types of linear effects for the yul category.
--
-- Note that the pure input pure output linear effect is included. For that, use the pure effect from the 'YulDSL.core'
-- directly.
data LinearEffectKind = PureInputVersionedOutput Nat -- ^ Pure input ports, versioned output ports
                      | VersionedInputOutput Nat     -- ^ Versioned input and output ports

-- | Extract Linear effect version delta.
type family LinearEffectVersionDelta (eff :: LinearEffectKind) :: Nat where
  LinearEffectVersionDelta (VersionedInputOutput vd) = vd
  LinearEffectVersionDelta (PureInputVersionedOutput vd) = vd

-- | Judging if the linear effect is static from its version delta.
type family IsLinearEffectNonStatic (vd :: Nat) :: Bool where
  IsLinearEffectNonStatic 0 = False
  IsLinearEffectNonStatic vd = True

-- ^ A linear effect is always not pure.
type instance IsEffectNotPure (eff :: LinearEffectKind) = True

type instance MayEffectWorld (VersionedInputOutput vd) = IsLinearEffectNonStatic vd
type instance MayEffectWorld (PureInputVersionedOutput vd) = IsLinearEffectNonStatic vd

instance KnownNat vd => KnownYulCatEffect (VersionedInputOutput vd) where
  classifyYulCatEffect = if fromSNat (natSing @vd) BasePrelude.== 0 then StaticEffect else OmniEffect

instance KnownNat vd => KnownYulCatEffect (PureInputVersionedOutput vd) where
  classifyYulCatEffect = if fromSNat (natSing @vd) BasePrelude.== 0 then StaticEffect else OmniEffect

------------------------------------------------------------------------------------------------------------------------
-- $YulPortDiagrams
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
  decode'l :: forall a b. YulO2 a b
    => (forall r. YulO1 r => P'x ie r a ⊸ P'x oe r b)
    -> YulCat eff a b
  decode'l f = YulUnsafeCoerceEffect (decode'x (unsafeCoerceYulPortDiagram f))

instance DecodableYulPortDiagram (VersionedPort 0) (VersionedPort vd) (VersionedInputOutput vd)
instance DecodableYulPortDiagram PurePort (VersionedPort vd) (PureInputVersionedOutput vd)
instance DecodableYulPortDiagram PurePort PurePort Pure

-- | Encodable yul port diagrams.
class EncodableYulPortDiagram eff ie oe where
  --  | Encode a yul port diagrams to a yul port function with a continuation.
  --
  --  Note: @r@ is a skolem type variable from encoding. The continuation is the only way to have access to it.
  encodeWith'l :: forall r a b c. YulO3 r a b
    => (P'x oe r b ⊸ c)
    -> YulCat eff a b
    -> (P'x ie r a ⊸ c)
  encodeWith'l f c x = f (unsafeCoerceYulPort (encode'x (YulUnsafeCoerceEffect c) x))

instance (va + vd ~ vb) => EncodableYulPortDiagram (VersionedInputOutput vd) (VersionedPort va) (VersionedPort vb)
instance EncodableYulPortDiagram (PureInputVersionedOutput v) PurePort (VersionedPort v)
instance EncodableYulPortDiagram eff PurePort PurePort

------------------------------------------------------------------------------------------------------------------------
-- (P'V v1 r x1 ⊸ P'V v1 r x2 ⊸ ... P'V vn r b) <=> YulCat'LVV v1 vn r (NP xs) b
------------------------------------------------------------------------------------------------------------------------

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction x (P'V v1 r) (P'V vn r) One ~ P'V vn r x
         ) => UncurryingNP (x) '[] x (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One where
  uncurryingNP x (MkYulCat'LVV h) = MkYulCat'LVV
    (\a -> h a                   -- :: P'V v1 (NP '[])
           & coerceType'l @_ @() -- :: P'V v1 ()
           & unsafeCoerceYulPort -- :: P'V vn ()
           & \u -> ignore'l u x) -- :: P'V vn x

instance forall x xs b g v1 vn r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One
         ) => UncurryingNP (x -> g) (x:xs) b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One where
  uncurryingNP f (MkYulCat'LVV h) = MkYulCat'LVV
    (\xxs ->
        dup2'l xxs
      & \(xxs1, xxs2) -> split'l (coerceType'l @(NP (x:xs)) @(x, NP xs) (h xxs1))
      & \(x, xs) -> let !(MkYulCat'LVV g) =
                          (uncurryingNP
                            @g @xs @b
                            @(P'V v1 r) @(P'V vn r) @(YulCat'LVV v1 v1 r a) @(YulCat'LVV v1 vn r a) @One
                            (f x)
                            (MkYulCat'LVV (\a -> ignore'l (discard'l a) xs))
                          )
                    in g xxs2
    )

-- | Convert a currying function to a yul port diagram of versioned input output.
uncurry'lvv :: forall f xs b r vd m1 m1b m2 m2b.
  ( YulO3 (NP xs) b r
  --
  , EquivalentNPOfFunction f xs b
  --
  , P'V  0 r ~ m1
  , P'V vd r ~ m1b
  , YulCat'LVV 0  0 r (NP xs) ~ m2
  , YulCat'LVV 0 vd r (NP xs) ~ m2b
  --
  , LiftFunction b m2 m2b One ~ m2b b
  --
  , UncurryingNP f xs b m1 m1b m2 m2b One
  )
  => LiftFunction f m1 m1b One      -- ^ @LiftFunction           f  m1 m1b One@
  -> (P'V 0 r (NP xs) ⊸ P'V vd r b) -- ^ @LiftFunction (NP xs -> b) m1 m1b One@
uncurry'lvv f = let !(MkYulCat'LVV f') = uncurryingNP @f @xs @b @m1 @m1b @m2 @m2b @One f (MkYulCat'LVV id)
                in f'

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction (CurryNP (NP '[]) x) (P'V v1 r) (P'V vn r) One ~ P'V vn r x
         ) => CurryingNP '[] x (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb = cb (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) One
         ) => CurryingNP (x:xs) b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'V v1 r) @(P'V vn r) @(YulCat'LVV v1 v1 r a) @One
                    (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (consNP'l x (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- (P'P r x1 ⊸ P'P r x2 ⊸ ... P'V vd r b) <=> YulCat'LPV vd r (NP xs) b
------------------------------------------------------------------------------------------------------------------------

instance forall x vd r a.
         ( YulO3 x r a
         , LiftFunction x (P'P r) (P'V vd r) One ~ P'V vd r x
         ) => UncurryingNP (x) '[] x (P'P r) (P'V vd r) (YulCat'LPP r a) (YulCat'LPV vd r a) One where
  uncurryingNP x (MkYulCat'LPP h) = MkYulCat'LPV (\a -> h a                   -- :: P'P (NP '[])
                                                        & coerceType'l @_ @() -- :: P'P ()
                                                        & unsafeCoerceYulPort -- :: P'V vn ()
                                                        & \u -> ignore'l u x) -- :: P'V vn x

instance forall x xs b g vd r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs b (P'P r) (P'V vd r) (YulCat'LPP r a) (YulCat'LPV vd r a) One
         ) => UncurryingNP (x -> g) (x:xs) b (P'P r) (P'V vd r) (YulCat'LPP r a) (YulCat'LPV vd r a) One where
  uncurryingNP f (MkYulCat'LPP h) = MkYulCat'LPV
    (\xxs ->
        dup2'l xxs
      & \(xxs1, xxs2) -> split'l (coerceType'l @(NP (x:xs)) @(x, NP xs) (h xxs1))
      & \(x, xs) -> let !(MkYulCat'LPV g) =
                          (uncurryingNP
                           @g @xs @b
                           @(P'P r) @(P'V vd r) @(YulCat'LPP r a) @(YulCat'LPV vd r a) @One
                           (f x)
                           (MkYulCat'LPP (\a -> ignore'l (discard'l a) xs))
                          )
                    in g xxs2
    )

-- | Convert a currying function to a yul port diagram of pure input and versioned output.
uncurry'lpv :: forall f xs b r vd m1 m1b m2 m2b.
  ( YulO3 (NP xs) b r
  --
  , EquivalentNPOfFunction f xs b
  --
  , P'P    r ~ m1
  , P'V vd r ~ m1b
  , YulCat'LPP r (NP xs)    ~ m2
  , YulCat'LPV vd r (NP xs) ~ m2b
  --
  , LiftFunction b m2 m2b One ~ m2b b
  --
  , UncurryingNP f xs b m1 m1b m2 m2b One
  )
  => LiftFunction f m1 m1b One
  -> (P'P r (NP xs) ⊸ P'V vd r b)
uncurry'lpv f = let !(MkYulCat'LPV f') = (uncurryingNP @f @xs @b @m1 @m1b @m2 @m2b @One f (MkYulCat'LPP id))
                in f'

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction (CurryNP (NP '[]) x) (P'P r) (P'V vn r) One ~ P'V vn r x
         ) => CurryingNP '[] x (P'P r) (P'V vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb = cb (MkYulCat'LVV (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'P r) (P'V vn r) (YulCat'LVV v1 v1 r a) One
         ) => CurryingNP (x:xs) b (P'P r) (P'V vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'P r) @(P'V vn r) @(YulCat'LVV v1 v1 r a) @One
                    (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (consNP'l (unsafeCoerceYulPort x) (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- YulCat'LPP ==> (P'P ⊸ P'P ⊸ ... P'P)
------------------------------------------------------------------------------------------------------------------------

instance forall x r a.
         ( YulO3 x r a
         , LiftFunction (CurryNP (NP '[]) x) (P'P r) (P'P r) One ~ P'P r x
         ) => CurryingNP '[] x (P'P r) (P'P r) (YulCat'LPP r a) One where
  curryingNP cb = cb (MkYulCat'LPP (\a -> coerceType'l (discard'l a)))

instance forall x xs b r a.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'P r) (P'P r) (YulCat'LPP r a) One
         ) => CurryingNP (x:xs) b (P'P r) (P'P r) (YulCat'LPP r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'P r) @(P'P r) @(YulCat'LPP r a) @One
                    (\(MkYulCat'LPP fxs) -> cb (MkYulCat'LPP (\a -> (consNP'l (unsafeCoerceYulPort x) (fxs a)))))
