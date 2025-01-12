{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
  ( -- * Linear Effect Kind
    -- $LinearEffectKind
    LinearEffectKind (PureInputVersionedOutput, VersionedInputOutput)
  , LinearEffectVersionDelta, IsLinearEffectNonStatic
    -- * Yul Port Diagrams
    -- $YulPortDiagrams
  , YulCat'LVV (MkYulCat'LVV), YulCat'LPV (MkYulCat'LPV), YulCat'LPP (MkYulCat'LPP)
  , decode'lvv, decode'lpv, encode'lvv, encode'lpp
  , uncurry'lvv, uncurry'lpv
    -- * Pattern Matching Of Yul Ports
    -- $PatternMatching
  , match'l
  ) where
-- base
import GHC.TypeLits                             (KnownNat, type (+))
import Prelude                                  qualified as BasePrelude
-- linear-base
import Control.Category.Linear                  (P, decode, discard, encode, ignore, split)
import Prelude.Linear
import Unsafe.Linear                            qualified as UnsafeLinear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.YulUtils
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

decode'lvv :: forall a b vd. YulO2 a b
  => (forall r. YulO1 r => P'V 0 r a ⊸ P'V vd r b)
  -> YulCat (VersionedInputOutput vd) a b
decode'lvv f = decode (h f) -- an intermediate function to fight the multiplicity hell
  where h :: (forall r. YulO1 r => P'V 0 r a ⊸ P'V vn r b)
          ⊸ (forall r. YulO1 r => P (YulCat oe) r a ⊸ P (YulCat oe) r b)
        h = UnsafeLinear.coerce {- using Unsafe coerce to convert effect after type-checking -}

decode'lpv :: forall a b vd. YulO2 a b
  => (forall r. YulO1 r => P'P r a ⊸ P'V vd r b)
  -> YulCat (PureInputVersionedOutput vd) a b
decode'lpv f = decode (h f) -- an intermediate function to fight the multiplicity hell
  where h :: (forall r. YulO1 r => P'P r a ⊸ P'V vd r b)
          ⊸ (forall r. YulO1 r => P (YulCat oe) r a ⊸ P (YulCat oe) r b)
        h = UnsafeLinear.coerce {- using Unsafe coerce to convert effect after type-checking -}

encode'lvv :: forall a b c r v1 vd. YulO3 a b r
  => YulCat (VersionedInputOutput vd) a b
  -> (P'V (v1 + vd) r b ⊸ c)
  -> (P'V v1 r a ⊸ c)
encode'lvv cat f x = -- ghc can infer it; annotating for readability and double checking expected types
  let cat' = UnsafeLinear.coerce cat :: YulCat (VersionedPort v1) a b
      b = UnsafeLinear.coerce @(P'V v1 r b) @(P'V (v1 + vd) r b) (encode cat' x)
  in f b

encode'lpp :: forall a b c r eff. YulO3 a b r
  => YulCat (eff :: PureEffectKind) a b
  -> (P'P r b ⊸ c)
  -> (P'P r a ⊸ c)
encode'lpp cat f x = -- ghc can infer it; annotating for readability and double checking expected types
  let cat' = UnsafeLinear.coerce cat :: YulCat PurePort a b
      b = UnsafeLinear.coerce @(P'P r b) @(P'P r b) (encode cat' x)
  in f b

------------------------------------------------------------------------------------------------------------------------
-- (P'V v1 r x1 ⊸ P'V v1 r x2 ⊸ ... P'V vn r b) <=> YulCat'LVV v1 vn r (NP xs) b
------------------------------------------------------------------------------------------------------------------------

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction x (P'V v1 r) (P'V vn r) One ~ P'V vn r x
         ) => UncurryingNP (x) '[] x (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One where
  uncurryingNP x (MkYulCat'LVV h) = MkYulCat'LVV
    (\a -> h a &                 -- :: P'V v1 (NP '[])
           coerce'l @_ @() &     -- :: P'V v1 ()
           UnsafeLinear.coerce & -- :: P'V vn ()
           \u -> ignore u x)     -- :: P'V vn x

instance forall x xs b g v1 vn r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One
         ) => UncurryingNP (x -> g) (x:xs) b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) (YulCat'LVV v1 vn r a) One where
  uncurryingNP f (MkYulCat'LVV h) = MkYulCat'LVV
    (\xxs ->
        dup2'l xxs
      & \(xxs1, xxs2) -> split (coerce'l @(NP (x:xs)) @(x, NP xs) (h xxs1))
      & \(x, xs) -> let !(MkYulCat'LVV g) =
                          (uncurryingNP
                            @g @xs @b
                            @(P'V v1 r) @(P'V vn r) @(YulCat'LVV v1 v1 r a) @(YulCat'LVV v1 vn r a) @One
                            (f x)
                            (MkYulCat'LVV (\a -> ignore (discard a) xs))
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
  curryingNP cb = cb (MkYulCat'LVV (\a -> coerce'l (discard a)))

instance forall x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) One
         ) => CurryingNP (x:xs) b (P'V v1 r) (P'V vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'V v1 r) @(P'V vn r) @(YulCat'LVV v1 v1 r a) @One
                    (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (cons'l x (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- (P'P r x1 ⊸ P'P r x2 ⊸ ... P'V vd r b) <=> YulCat'LPV vd r (NP xs) b
------------------------------------------------------------------------------------------------------------------------

instance forall x vd r a.
         ( YulO3 x r a
         , LiftFunction x (P'P r) (P'V vd r) One ~ P'V vd r x
         ) => UncurryingNP (x) '[] x (P'P r) (P'V vd r) (YulCat'LPP r a) (YulCat'LPV vd r a) One where
  uncurryingNP x (MkYulCat'LPP h) = MkYulCat'LPV (\a -> h a &                -- :: P'P (NP '[])
                                                       coerce'l @_ @() &     -- :: P'P ()
                                                       UnsafeLinear.coerce & -- :: P'V vn ()
                                                       \u -> ignore u x)     -- :: P'V vn x

instance forall x xs b g vd r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs b (P'P r) (P'V vd r) (YulCat'LPP r a) (YulCat'LPV vd r a) One
         ) => UncurryingNP (x -> g) (x:xs) b (P'P r) (P'V vd r) (YulCat'LPP r a) (YulCat'LPV vd r a) One where
  uncurryingNP f (MkYulCat'LPP h) = MkYulCat'LPV
    (\xxs ->
        dup2'l xxs
      & \(xxs1, xxs2) -> split (coerce'l @(NP (x:xs)) @(x, NP xs) (h xxs1))
      & \(x, xs) -> let !(MkYulCat'LPV g) =
                          (uncurryingNP
                           @g @xs @b
                           @(P'P r) @(P'V vd r) @(YulCat'LPP r a) @(YulCat'LPV vd r a) @One
                           (f x)
                           (MkYulCat'LPP (\a -> ignore (discard a) xs))
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
  curryingNP cb = cb (MkYulCat'LVV (\a -> coerce'l (discard a)))

instance forall x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'P r) (P'V vn r) (YulCat'LVV v1 v1 r a) One
         ) => CurryingNP (x:xs) b (P'P r) (P'V vn r) (YulCat'LVV v1 v1 r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'P r) @(P'V vn r) @(YulCat'LVV v1 v1 r a) @One
                    (\(MkYulCat'LVV fxs) -> cb (MkYulCat'LVV (\a -> (cons'l (UnsafeLinear.coerce x) (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- YulCat'LPP ==> (P'P ⊸ P'P ⊸ ... P'P)
------------------------------------------------------------------------------------------------------------------------

instance forall x r a.
         ( YulO3 x r a
         , LiftFunction (CurryNP (NP '[]) x) (P'P r) (P'P r) One ~ P'P r x
         ) => CurryingNP '[] x (P'P r) (P'P r) (YulCat'LPP r a) One where
  curryingNP cb = cb (MkYulCat'LPP (\a -> coerce'l (discard a)))

instance forall x xs b r a.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'P r) (P'P r) (YulCat'LPP r a) One
         ) => CurryingNP (x:xs) b (P'P r) (P'P r) (YulCat'LPP r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'P r) @(P'P r) @(YulCat'LPP r a) @One
                    (\(MkYulCat'LPP fxs) -> cb (MkYulCat'LPP (\a -> (cons'l (UnsafeLinear.coerce x) (fxs a)))))

------------------------------------------------------------------------------------------------------------------------
-- $PatternMatching
------------------------------------------------------------------------------------------------------------------------

match'l :: forall p r a b va vd.
  ( YulO4 r a b (p a)
  , BasePrelude.Functor p
  , PatternMatchableYulCat (VersionedInputOutput 0) p a
  )
  => P'V va r (p a)
  ⊸ (forall r1. YulO1 r1 => p (P'V va r1 (p a) ⊸ P'V va r1 a) ⊸ (P'V 0 r1 (p a) ⊸ P'V vd r1 b))
  -> P'V (va + vd) r b
match'l p f = let c = match (YulId :: YulCat (VersionedInputOutput 0) (p a) (p a))
                      \cats -> UnsafeLinear.coerce
                             @(YulCat (VersionedInputOutput vd) (p a) b)
                             @(YulCat (VersionedInputOutput 0) (p a) b)
                             (decode'lvv (f (BasePrelude.fmap (`encode'lvv` id) cats)))
                  c' = UnsafeLinear.coerce
                       @(YulCat (VersionedInputOutput 0) (p a) b)
                       @(YulCat (VersionedInputOutput vd) (p a) b)
                       c
              in encode'lvv c' id p
