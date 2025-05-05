{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

This modules provides the alternative class of Category whose objects are constrained. Some helper categories, including
hask category, are provided as well as a convenience.

-}
module Control.Category
  ( Category (Obj, idₖ, (∘))
  , OpCat (MkOpCat)
  , HaskObj
  ) where
-- base
import Data.Kind (Constraint, Type)


-- | An alternative type class of Category used for YulCat, where objects are constrained through a associated type
-- synonym.
class Category (cat :: Type -> Type-> Type) where
  type family Obj cat :: Type -> Constraint
  -- | Identity function in the category of @cat@.
  idₖ :: forall a. Obj cat a => a `cat` a
  -- | Composition operator in the category of @cat@.
  (∘) :: forall a b c. (Obj cat a, Obj cat b, Obj cat c) => (b `cat` c) -> (a `cat` b) -> a `cat` c

------------------------------------------------------------------------------------------------------------------------
-- Opposite category (OpCat)
------------------------------------------------------------------------------------------------------------------------

-- | The opposite category of a category @cat@.
data OpCat cat a b where
  MkOpCat :: forall cat a b. (Category cat, Obj cat a, Obj cat b) => cat b a -> OpCat cat a b

instance Category cat => Category (OpCat cat) where
  type instance Obj (OpCat cat) = Obj cat
  idₖ = MkOpCat idₖ
  (MkOpCat f1) ∘ (MkOpCat f2) = MkOpCat (f2 ∘ f1)

------------------------------------------------------------------------------------------------------------------------
-- Hask category
------------------------------------------------------------------------------------------------------------------------

-- All types are hask objects in Haskell.
class HaskObj a
instance HaskObj a

-- ^ Function arrow in Hask is a category, trivially.
instance Category (->) where
  type instance Obj (->) = HaskObj
  idₖ = Prelude.id
  (∘) = (Prelude..)
