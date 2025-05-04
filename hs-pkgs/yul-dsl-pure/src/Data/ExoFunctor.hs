{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

This modules provides the functor proper, named ExoFunctor to avoid naming conflict with hask's endo-functor.

-}
module Data.ExoFunctor
  ( HexoFunctor (hexomap, (<$$>), (<&&>)), HendoFunctor, hendomap, (<$>>), (<<&>)
  , ExoFunctor (exomap), EndoFunctor, endomap
  , HaskFunctor
  ) where
import Control.Category


-- | A functor maps morphisms of two categories. Each morphism is encoded on the Hask arrows as a morphism [C^op,
-- Set](C(-,a), C(-,b)) in the category of presheaves.
class (Category cat1, Category cat2) => HexoFunctor f cat1 r1 cat2 r2 | cat1 cat2 r2 -> r1 where
  -- | hexomap, or (<$$>), is the exomap wrapped over hask arrows.
  hexomap, (<$$>) :: forall a b.
    ( Obj cat1 r1, Obj cat2 r2
    , Obj cat1 a, Obj cat1 b
    , Obj cat2 (f a), Obj cat2 (f b)
    ) =>
    (cat1 r1 a     -> cat1 r1 b) ->
    (cat2 r2 (f a) -> cat2 r2 (f b))
  (<$$>) = hexomap

  -- | An analogue to the (<&>) operator but for exo-functors.
  (<&&>) :: forall a b.
    ( Obj cat1 r1, Obj cat2 r2
    , Obj cat1 a, Obj cat1 b
    , Obj cat2 (f a), Obj cat2 (f b)
    ) =>
    cat2 r2 (f a) ->
    (cat1 r1 a -> cat1 r1 b) ->
    cat2 r2 (f b)
  (<&&>) fa g = hexomap g fa

-- | A alias to the endo-functor variant of the HexoFunctor.
type HendoFunctor f cat r = HexoFunctor f cat r cat r

-- | A endo-functor version of the <$$>. It may help the type inference in some cases.
hendomap, (<$>>) ::  forall a b f cat r.
  ( HendoFunctor f cat r
  , Obj cat a, Obj cat b, Obj cat r
  , Obj cat (f a), Obj cat (f b)
  ) =>
  (cat r a     -> cat r b) ->
  (cat r (f a) -> cat r (f b))
hendomap = hexomap
(<$>>) = hexomap

-- | A endo-functor version of the <&&>. It may help the type inference in some cases.
(<<&>) ::  forall a b f cat r.
  ( HendoFunctor f cat r
  , Obj cat a, Obj cat b, Obj cat r
  , Obj cat (f a), Obj cat (f b)
  ) =>
  cat r (f a) ->
  (cat r a     -> cat r b) ->
  cat r (f b)
(<<&>) = (<&&>)

infixl 4 <$$>, <$>>
infixl 1 <&&>, <<&>

-- | A functor maps morphisms of two categories: @cat1@ and @cat2@.
class (Category cat1, Category cat2) => ExoFunctor f cat1 cat2 where
  -- | Functor between @cat1@ and @cat2@, where @f@ maps objects from @cat1@ to @cat2@.
  exomap :: forall a b.
    (Obj cat1 a, Obj cat1 b, Obj cat2 (f a), Obj cat2 (f b)) =>
    cat1 a b -> cat2 (f a) (f b)

-- | A endo-functor maps the morphisms from the same category @cat@.
type EndoFunctor f cat = ExoFunctor f cat cat

-- | An alias to 'exomap' for endo-functors.
endomap :: forall cat f a b.
  (EndoFunctor f cat, Obj cat a, Obj cat b, Obj cat (f a), Obj cat (f b)) =>
  cat a b -> cat (f a) (f b)
endomap = exomap

--
-- working With Hask Category
--

-- | An alias to the hask's endo-functor.
type HaskFunctor = Functor

-- ^ Function arrows of the hask make all Hask's endo-functors exo-functors.
instance HaskFunctor f => ExoFunctor f (->) (->) where
  exomap = fmap
