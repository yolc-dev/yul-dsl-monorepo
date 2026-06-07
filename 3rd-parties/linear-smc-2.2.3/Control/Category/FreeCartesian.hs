{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE LinearTypes                #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Control.Category.FreeCartesian (Cat, π1, π2, embed, (▴), toSMC) where

import Control.Category.Constrained
import Prelude                      hiding (Ordering (..), curry, id, (.))
import Unsafe.Coerce
-- import Control.Category.InitialSMC (type TensorClosed)

data Trie  k con a b where
  (:▴:) :: (con b, con c) => Trie k con a b -> Trie k con a c -> Trie k con a (b,c) -- fork
  Z :: Trie  k con a a -- Stop
  (:.) :: (con a, con b) => k a b -> Trie k con b c -> Trie k con a c -- Embed
  L :: Trie  k con  a c -> Trie  k con (a,b) c -- (∘ π₁)
  R :: Trie  k con  b c -> Trie  k con (a,b) c -- (∘ π₂)
  -- composition, with the invariant that the 1st argument is a fork (so b is a product object) (unsimplified). (If it were not a fork, then the composition can be linearized)
  -- Furthermore, the 2nd argument must feed both components to an 'embed', or to the final output.
  -- The 1st argument isn't simplified. Because: 1. simplifying isn't going to help comparision. 2. this way we simplify only one of the copies.
  (:∘) :: (con b) => Trie k con a b -> Trie k con b c -> Trie k con a c

compareTries :: Trie cat con a b -> Trie cat con a c -> Order b c
compareTries Z Z = EQ
compareTries (L f) (L g) = compareTries f g
compareTries (R f) (R g) = compareTries f g
compareTries (_ :. f) (_ :. g) = compareTries f (unsafeCoerceSource g)
  -- same source: because of linearity, if the source is fully
  -- consumed, there can only be a single way in which the source is
  -- transformed.
compareTries (x :∘ f) (y :∘ g) = case compareTries x y of
  EQ -> compareTries f g
  LT -> LT
  GT -> GT
compareTries ((:▴:) x _) ((:▴:) y _) = case compareTries x y of
  EQ -> unsafeCoerce EQ -- the first component of the forks are equal. We maintain the invariant ① that both components are going to be used.
  -- Because of linearity, this means that the 1st component fully determines the output pair.
  LT -> LT
  GT -> GT
compareTries Z _ = LT
compareTries _ Z = GT
compareTries (L {}) _ = LT
compareTries _ (L {})= GT
compareTries (R {}) _ = LT
compareTries _ (R {})= GT
compareTries ((:. ) {}) _ = LT
compareTries _ ((:. ) {})= GT
compareTries ((:∘) {}) _ = LT
compareTries _ ((:∘) {})= GT

pshows :: Show a => a -> ShowS
pshows x = showParen True (shows x)

instance (ProdObj con, forall x y. (con x, con y) => Show (k x y)) => Show  (Trie k con a b) where
  showsPrec _d = \case
    f :▴: g -> showString "⟨" . shows f . showString "," . shows g . showString "⟩"
    m :∘ f -> pshows m . showString "." . shows f
    L k -> showString "1" . shows k
    R k  -> showString "2" . shows k
    φ :. k -> shows φ . shows k
    Z -> showString "!"

type Cat k con a b = forall c. Trie k con b c -> Trie k con a c

embed  :: {-<-}(con a, con b) => {->-}k a b -> Cat k {-<-}con{->-} a b
embed φ = (φ :.)

π1  :: {-<-}con b => {->-} Cat k {-<-}con{->-} (a ⊗ b) a
π1 = L

π2     :: {-<-}con a => {->-} Cat k {-<-}con{->-} (a ⊗ b) b {-<-}
π2 = R

(▴) :: (con a, con b, con d, TensorClosed con) => (Cat k con a b) -> (Cat k con a d) -> (Cat k con a (b ⊗ d))
f ▴ g = \case Z -> h
              e -> h :∘ e
     where h = f Z :▴: g Z


-- -- | Make a branch with a possible continuation.
-- -- We do not create (M f Z).
-- toBranch :: (con a, con b, TensorClosed con) => FreeCartesian  k con a b -> Cat k con a b
-- toBranch = \case
--   I -> id
--   (f :.: g) -> toBranch g . toBranch f
--   (Embed φ) -> (φ :.)
--   P1 -> L
--   P2 -> R
--   (f :▵: g) -> \case Z -> h
--                      e -> h :∘ e
--      where h = toTrie f :▴: toTrie g

-- toTrie :: (con a, con b, TensorClosed con) => FreeCartesian  k con a b -> Trie k con a b
-- toTrie f = toBranch f Z

-- | Insert a morphism (normalised)
ee :: (con a, TensorClosed con,con b, con d, Obj k ~ con, Monoidal k)
  => k a b -> Trie  k con  b d -> (forall c. con c => Trie k con a c -> k c d -> ξ) -> ξ
ee φ Z k = k Z φ -- A morphism at the end of computation. It's connected to the output directly, so because of linearity it will be fully consumed. So we can extract it.
ee φ f k = k (φ :. f) id

-- | Insert a fork (normalised). Precondition: f is a Fork.
trieComp :: (con a, TensorClosed con,con b, con d, Obj k ~ con, Monoidal k)
  => Trie k con a b -> Trie k con  b d -> (forall c. con c => Trie k con a c -> k c d -> ξ) -> ξ
trieComp f Z k = normalize f k -- Nothing after, so we expand the fork, so that it can be merged with other branches.
trieComp f g k = k (f :∘ g) id

unsafeCoerceSource :: k a b -> k a' b
unsafeCoerceSource = undefined -- unsafeCoerce

-- | Normalised fork, in the case where the heads of the components are not themselves forks.
-- Attempt a merge and return Right if successful, otherwise Left and the ordering of componets.
fork2 :: forall a b c con k ξ. (con a, con b, con c, Monoidal k, TensorClosed con, con ~ Obj k)
  => Trie k con a b -> Trie k con a c -> (forall x. con x => Trie k con a x -> k x (b⊗c) -> ξ) -> Either (Order b c) ξ
fork2 (φ :. f) (_ :. g) k = Right $ fork f (unsafeCoerceSource g) $ \fg s -> ee φ fg $ \φfg t -> k φfg (s . t)
   -- same source ⇒ same morphism. -- (φ∘f ▵ φ∘g) = φ ∘ (f▵g)
fork2 (L Z) (R Z) k  = Right $ k Z id -- π₁ ▵ π₂ = id
fork2 (R Z) (L Z) k  = Right $ k Z swap -- π₂ ▵ π₁ = swap
fork2 (R f) (R g) k  = objprod @con @a // Right $ fork f g $ \fg s -> k (R fg) s -- (π₂∘f ▵ π₂∘g) = π₂ ∘ (f▵g)
fork2 (L f) (L g) k  = objprod @con @a // Right $ fork f g $ \fg s -> k (L fg) s -- shared start
fork2 (x :∘ f) (y :∘ g) k = case compareTries x y of
  EQ -> Right $ fork f g $ \fg s -> trieComp x fg $ \ xfg t -> k xfg (s . t) -- shared start
  LT -> Left LT -- not equal starts, return ordering
  GT -> Left GT
fork2 f g _ = Left (compareTries f g) -- guaranteed not equal morphisms; we return their ordering.

-- | Normalised fork:
-- 1. Leaves are merged as much as possible.
-- 2. Fork combinators are right associated. (The first component of a fork can never itself be a fork)
-- 3. Leaves are sorted so that equal (heads) can be discovered.
-- (This performs rather badly on a long chain of forks--- but this
-- won't normally happen because we don't have very deeply nested
-- tuples, typically.)
fork :: forall a b c con k ξ. (con a, con b, con c, Monoidal k, TensorClosed con, con ~ Obj k)
  => Trie k con a b -> Trie k con a c -> (forall x. con x => Trie k con a x -> k x (b⊗c) -> ξ) -> ξ
fork (f :▴: g) h k = -- fork on left: reassociate
  fork g h $ \gh s -> fork f gh $ \fgh t -> k fgh (assoc' . (id×s) . t)
fork f (g :▴: h) k =  -- fork on right: attempt merging 1st and 2nd positions
  case fork2 f g $ \fg s ->
    -- attempt sucessful in the contiuation:
       fork fg h $ \lfgh t -> k lfgh (assoc . (s × id)  . t) of
    Right r -> r
    Left c -> case c of
      EQ -> error "fork: missed equality"
      LT -> k (f :▴: (g :▴: h)) id -- already in normal form
      GT ->  -- wrong order, swap necessary (so we're bubble-sorting the chain of forks)
        fork f h $ \fh s ->
        fork g fh $ \gfh t ->
        k gfh (assoc . (swap × id) . assoc' . (id × s) . t)
fork f g k = case fork2 f g k of
  Right r -> r -- sucessful reduction
  Left c -> case c of
    EQ -> error "fork: missed equality"
    LT -> k (f :▴: g) id
    GT -> k (g :▴: f) swap

-- | Recursively normalise. If the input is SMC equivalent in the
-- sense of the paper, the result is Z plus the SMC equivalent
-- morphism.
normalize :: forall a b con k ξ. (Obj k ~ con, Monoidal k, con a, con b, TensorClosed con)
  => Trie k con a b -> (forall c. con c => Trie k con a c -> k c b -> ξ) -> ξ
normalize t0 k = case t0 of
  Z       -> k Z id
  f :▴: g -> normalize f $ \f' s -> normalize g $ \g' t -> (fork f' g') $ \f'g u -> k f'g ((s × t) . u)
  L f     -> objprod @con @a // normalize f $ \f' s -> k (L f') s
  R f     -> objprod @con @a // normalize f $ \f' s -> k (R f') s
  f :∘ g  -> normalize g $ \g' s -> trieComp f g' $ \fg' t -> k fg' (s . t)
  φ :. f  -> normalize f $ \f' s -> ee φ f' $ \φf' t -> k φf' (s . t)

toSMC :: forall a b con k. (Obj k ~ con, Monoidal k, con a, con b, TensorClosed con) => Cat k con a b -> k a b
toSMC t = normalize (t Z) $ \f g -> case f of
  Z -> g
  _ -> error "toSMC: normalisation process failed"
