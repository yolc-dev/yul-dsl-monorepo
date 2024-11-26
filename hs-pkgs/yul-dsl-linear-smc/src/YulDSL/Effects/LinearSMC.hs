{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE NoImplicitPrelude   #-}
module YulDSL.Effects.LinearSMC where

-- base
import           GHC.TypeLits                                  (type (+))
-- linear-base
import           Prelude.Linear                                hiding (Eq (..), Ord (..))
import qualified Unsafe.Linear                                 as UnsafeLinear
-- linear-smc
import           Control.Category.Constrained                  ()
import           Control.Category.Linear
    ( P
    , copy
    , decode
    , discard
    , encode
    , ignore
    , merge
    , mkUnit
    , split
    )
-- yul-dsl
import           YulDSL.Core
-- orphansed instances for categories in linear-smc
import           Control.Category.Constrained.YulDSL.LinearSMC ()
import           Data.MPOrd.YulDSL.LinearSMC


{- * Yul Port Types -}

{- HLint ignore LinearEffect "Use newtype instead of data" -}
-- | Linearized effect, where @v@ is a type-level version of the data.
data LinearEffect = MkLinearEffect Nat

type instance NonPureEffect (MkLinearEffect v) = True

-- | Linear port API of yul category with `LinearEffect` kind.
type P'L v r = P (YulCat (MkLinearEffect v)) r

-- | Polymorphic port type for linear APIs of the yul category.
-- type P'L v r a = P'L v r a

type UNIT'L v r = P'L v r ()
type ADDR'L v r = P'L v r ADDR
type BOOL'L v r = P'L v r BOOL
type I256'L v r = P'L v r I256
type U256'L v r = P'L v r U256

-- | Yul category port diagram as a data constructor, otherwise type synonym cannot be partial for @YulCat'L r a@.
data YulCat'L v1 vn r a b where
  MkYulCat'L :: forall a b r v1 vn. YulO3 a b r => (P'L v1 r a ⊸ P'L vn r b) ⊸ YulCat'L v1 vn r a b

-- | Unwrap YulCat'L linearly.
unYulCat'L :: forall a b r v1 vn. YulO3 a b r => YulCat'L v1 vn r a b ⊸ (P'L v1 r a ⊸ P'L vn r b)
unYulCat'L (MkYulCat'L c) =  c

{- * Yul Port Combinators -}

emb'l :: forall a d v r. YulO3 a d r
        => a -> (P'L v r d ⊸ P'L v r a)
emb'l a = encode (YulEmbed a) . discard

dup'l :: forall a v r. YulO2 a r
      => P'L v r a ⊸ (P'L v r a, P'L v r a)
dup'l = split . copy

use'l :: forall a b v r. YulO3 a b r
      => P'L v r a ⊸ (P'L v r a ⊸ P'L v r b) ⊸ (P'L v r a, P'L v r b)
use'l a f = dup'l a & \(a', a'') -> (a', f a'')

dis'l :: forall a v r. YulO2 a r
      => P'L v r a ⊸ P'L v r ()
dis'l = discard

const'l :: forall a b v r. YulO3 a b r
      => P'L v r a ⊸ P'L v r b ⊸ P'L v r a
const'l = flip (ignore . discard)

coerce'l :: forall a b v r. (YulO3 a b r, ABITypeCoercible a b)
         => P'L v r a ⊸ P'L v r b
coerce'l = encode YulCoerce

cons'l :: forall x xs v r. YulO3 x (NP xs) r
       => P'L v r x ⊸ P'L v r (NP xs) ⊸ P'L v r (NP (x:xs))
cons'l x xs = coerce'l (merge (x, xs))

-- lift'l :: forall a b v r. YulO3 a b r => YulCat'P a b -> (P'L v r a ⊸ P'L v r b)
-- lift'l c =  let c' :: P (YulCat MkPure) r a ⊸ P (YulCat MkPure) r b
--                 c' = encode c
--             in UnsafeLinear.coerce c' -- coercing from the 'Pure' kind to the 'LinearEffect' kind

{- * Ethereum.ContractABI instances * -}

{- ** UncurryingNP instances -}

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction x (P'L v1 r) (P'L vn r) One ~ P'L vn r x
         ) => UncurryingNP (x) '[] x (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r a) (YulCat'L v1 vn r a) One where
  uncurryingNP x (MkYulCat'L g) = MkYulCat'L (\a -> g a &                 -- :: P'L v1 (NP '[])
                                                    coerce'l @_ @() &     -- :: P'L v1 ()
                                                    UnsafeLinear.coerce & -- :: P'L vn ()
                                                    \u -> ignore u x)     -- :: P'L vn x

instance forall x xs b g v1 vn r a.
         ( YulO5 x (NP xs) b r a
         , UncurryingNP g xs b (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r a) (YulCat'L v1 vn r a) One
         ) => UncurryingNP (x -> g) (x:xs) b (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r a) (YulCat'L v1 vn r a) One where
  uncurryingNP f (MkYulCat'L h) = MkYulCat'L
    (\xxs -> dup'l xxs &
             \(xxs1, xxs2) -> split (coerce'l @(NP (x:xs)) @(x, NP xs) (h xxs1)) &
             \(x, xs) -> unYulCat'L
                         (uncurryingNP
                           @g @xs @b
                           @(P'L v1 r) @(P'L vn r) @(YulCat'L v1 v1 r a) @(YulCat'L v1 vn r a) @One
                           (UnsafeLinear.coerce f x) -- TODO: not sure why this unsafe coercion is required.
                           (g xs)
                         )
                         xxs2
    )
    where g :: P'L v1 r (NP xs) ⊸ YulCat'L v1 v1 r a (NP xs)
          g xs = MkYulCat'L (\as -> ignore (discard as) xs)

{- ** CurryingNP instances -}

instance forall x v1 vn r a.
         ( YulO3 x r a
         , LiftFunction (CurryNP (NP '[]) x) (P'L v1 r) (P'L vn r) One ~ P'L vn r x
         ) => CurryingNP '[] x (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r a) One where
  curryingNP cb = cb (MkYulCat'L (\a -> coerce'l (discard a)))

instance forall x xs b r a v1 vn.
         ( YulO5 x (NP xs) b r a
         , CurryingNP xs b (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r a) One
         ) => CurryingNP (x:xs) b (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r a) One where
  curryingNP cb x = curryingNP @xs @b @(P'L v1 r) @(P'L vn r) @(YulCat'L v1 v1 r a) @One
                    (\(MkYulCat'L fxs) -> cb (MkYulCat'L (\a -> (cons'l x (fxs a)))))

uncurry'l :: forall f xs b r vd m1 m1b m2 m2b.
             ( YulO3 (NP xs) b r
             , xs ~ UncurryNP'Fst f
             , b  ~ UncurryNP'Snd f
             , P'L  0 r ~ m1
             , P'L vd r ~ m1b
             , YulCat'L 0  0 r (NP xs) ~ m2
             , YulCat'L 0 vd r (NP xs) ~ m2b
             , UncurryingNP f xs b m1 m1b m2 m2b One
             , LiftFunction (NP xs -> b) m1 m1b One ~ (P'L 0 r (NP xs) ⊸ P'L vd r b)
             , LiftFunction b m2 m2b One ~ m2b b
             )
          => LiftFunction           f  m1 m1b One
          -> LiftFunction (NP xs -> b) m1 m1b One
uncurry'l f = unYulCat'L $
              uncurryingNP @f @xs @b @m1 @m1b @m2 @m2b @One
              f (MkYulCat'L id)

uncurry'p'l :: forall f xs b r vd m1 m1b m2 m2b.
               ( YulO3 (NP xs) b r
               , xs ~ UncurryNP'Fst f
               , b  ~ UncurryNP'Snd f
               , YulCat'P (NP xs)        ~ m1
               , YulCat'L 0 vd r (NP xs) ~ m1b
               , YulCat'L 0  0 r (NP xs) ~ m2
               , YulCat'L 0 vd r (NP xs) ~ m2b
               , UncurryingNP f xs b m1 m1b m2 m2b Many
               , LiftFunction b m2 m2b Many ~ m2b b
               )
            => LiftFunction f m1 m1b Many
            -> (P'L 0 r (NP xs) ⊸ P'L vd r b)
uncurry'p'l f = unYulCat'L $
                uncurryingNP @f @xs @b @m1 @m1b @m2 @m2b @Many
                f (MkYulCat'L id)

-- Type alias for 'Fn' of linear effect, where @vd@ tracks number of state revisions in type-level.
type LinearFn vd = Fn (MkLinearEffect vd)

-- | Define a `YulCat` morphism from a linear port function.
fn'l :: forall f xs b vd.
        ( YulO2 (NP xs) b
        , CurryNP (NP xs) b ~ f
        , UncurryNP'Fst f ~ xs
        , UncurryNP'Snd f ~ b
        )
     => String
     -> (forall r. YulObj r => P'L 0 r (NP xs) ⊸ P'L vd r b)
     -> LinearFn vd (CurryNP (NP xs) b)
fn'l fid f = MkFn (MkFnCat fid (decode (h f)))
  where h :: (forall r. YulObj r => P'L 0 r (NP xs) ⊸ P'L vd r b)
          ⊸ (forall r. YulObj r => P'L vd r (NP xs) ⊸ P'L vd r b)
        h = UnsafeLinear.coerce

call'l :: forall f x xs b g' r v1 vd vn.
          ( YulO4 x (NP xs) b r
          , UncurryNP'Fst f ~ (x:xs)
          , UncurryNP'Snd f ~ b
          , v1 + vd ~ vn
          , LiftFunction (CurryNP (NP xs) b) (P'L v1 r) (P'L vn r) One ~ g'
          , CurryingNP xs b (P'L v1 r) (P'L vn r) (YulCat'L v1 v1 r ()) One
          , LiftFunction b (YulCat'L v1 v1 r ()) (P (YulCat (MkLinearEffect vn)) r) One ~ P'L vn r b
          )
       => LinearFn vd f
       -> (P'L v1 r x ⊸ g')
call'l (MkFn f) x' = dup'l x' &
  \(x'', x''') ->
    curryingNP @xs @b @(P'L v1 r) @(P'L vn r) @(YulCat'L v1 v1 r ()) @One
    (\(MkYulCat'L fxs) -> g x'' (fxs (discard x''')))
  where cat :: YulCat (MkLinearEffect v1) (NP (x:xs)) b
        cat = UnsafeLinear.coerce (fnCat f)
        g :: forall. P'L v1 r x ⊸ P'L v1 r (NP xs) ⊸ P'L vn r b
        g x xs = UnsafeLinear.coerce (encode (YulJump (fnId f) cat) (cons'l x xs))

{- * storage utilities -}

sget :: forall a r v. (YulO2 a r, ABIWordValue a)
     => P'L v r ADDR ⊸ P'L v r a
sget = encode YulSGet

sput :: forall a r v. (YulO2 a r, ABIWordValue a)
     => P'L v r ADDR ⊸ P'L v r a ⊸ P'L (v + 1) r a
sput to x = dup'l x &
            \(x', x'') -> encode YulSPut (merge (to, x')) &
            \u -> UnsafeLinear.coerce (ignore u x'')

sputAt :: forall a r v. (YulO2 a r, ABIWordValue a)
       => ADDR -> P'L v r a ⊸ P'L (v + 1) r a
sputAt to x = mkUnit x & \(x', u) -> emb'l to u & \a -> sput a x'


--
-- Prelude type class instances
--

-- | 'MPEq' instance for linear yul ports.
instance (YulObj r, YulNum a) => MPEq (P'L v r a) (BOOL'L v r) where
  a == b = encode (YulNumCmp (false, true , false)) (merge (a, b))
  a /= b = encode (YulNumCmp (true , false, true )) (merge (a, b))

-- | 'MPOrd' instance for linear yul ports.
instance (YulObj r, YulNum a) => MPOrd (P'L v r a) (BOOL'L v r) where
  a  < b = encode (YulNumCmp (true , false, false)) (merge (a, b))
  a <= b = encode (YulNumCmp (true , true , false)) (merge (a, b))
  a  > b = encode (YulNumCmp (false, false, true )) (merge (a, b))
  a >= b = encode (YulNumCmp (false, true , true )) (merge (a, b))

instance YulO2 a r => IfThenElse (BOOL'L v r) (P'L v r a) where
  ifThenElse c a b = encode YulITE (merge(c, merge(a, b)))