{-# LANGUAGE UndecidableInstances #-}
module Data.ExoFunctor
  ( ExoFunctor (exomap)
  , (<$$>), (<&&>)
  , EndoFunctor, endomap
  , HaskFunctor
  ) where
import Control.Category


-- | A functor maps morphisms of two categories: @cat1@ and @cat2@.
class (Category cat1, Category cat2) => ExoFunctor cat1 cat2 f where
  -- | Functor between @k1@ and @k2@, where @f@ maps objects from @k1@ to @k2@.
  exomap :: forall a b.
   (Obj cat1 a, Obj cat1 b, Obj cat2 (f a), Obj cat2 (f b)) =>
    cat1 a b -> cat2 (f a) (f b)

-- | "<$$>" is the exomap wrapped around HaskCatFunction.
--
-- Note: This is more general than the fmap in hask.
-- >>> fmap2 f (fa :: f a) = ((\ua -> const (f (ua ()))) <$$> const fa) ()
-- >>> :type fmap2
-- fmap2 :: Functor f => (a -> b) -> f a -> f b
(<$$>) :: forall cat1 cat2 f a b r2.
  ( Category cat1, ExoFunctor (HaskCatFunction cat1 ()) cat2 f
  , Obj cat1 (), Obj cat2 r2
  , Obj cat1 a, Obj cat1 b
  , Obj cat2 (f a), Obj cat2 (f b)
  ) =>
  (cat1 () a     -> cat1 () b) ->
  (cat2 r2 (f a) -> cat2 r2 (f b))
(<$$>) g = unHaskCatFunction (anyCatToHask (exomap (MkHaskCatFunction g)))
infixl 4 <$$>

(<&&>) :: forall cat1 cat2 f a b r2.
  ( Category cat1, ExoFunctor (HaskCatFunction cat1 ()) cat2 f
  , Obj cat1 (), Obj cat2 r2
  , Obj cat1 a, Obj cat1 b
  , Obj cat2 (f a), Obj cat2 (f b)
  ) =>
  cat2 r2 (f a) ->
  (cat1 () a     -> cat1 () b) ->
  cat2 r2 (f b)
(<&&>) fa g = unHaskCatFunction (anyCatToHask (exomap (MkHaskCatFunction g))) fa
infixl 1 <&&>

-- | A endo-functor maps the morphisms from the same category @cat@.
type EndoFunctor cat f = ExoFunctor cat cat f

-- | An alias to 'exomap' for endo-functors.
endomap :: forall cat f a b.
  (EndoFunctor cat f, Obj cat a, Obj cat b, Obj cat (f a), Obj cat (f b)) =>
  cat a b -> cat (f a) (f b)
endomap = exomap

--
-- working With Hask Category
--

-- | An alias to the hask's endo-functor.
type HaskFunctor = Functor

-- ^ This makes hask's function arrows available for more exo-functor instances.
instance (Obj cat1 r1, Obj cat2 r2, ExoFunctor (HaskCatFunction cat1 r1) cat2 f) =>
         ExoFunctor (HaskCatFunction cat1 r1) (HaskCatFunction cat2 r2) f where
  exomap catab = MkHaskCatFunction (exomap catab ∘)

-- ^ Function arrows of the hask make all Hask's endo-functors exo-functors.
instance HaskFunctor f => ExoFunctor (->) (->) f where
  exomap = fmap

-- ^ We need this for the @ExoFunctor (->) (->) f@ instance.
instance HaskFunctor f => ExoFunctor (HaskCatFunction (->) ()) (->) f where
  exomap (MkHaskCatFunction g) = fmap (flip g () . const)
