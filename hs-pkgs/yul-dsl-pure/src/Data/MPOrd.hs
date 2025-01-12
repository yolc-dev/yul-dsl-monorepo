{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LinearTypes            #-}
module Data.MPOrd where

-- | Multi-parameter equality type class where boolean type is @b@
class MPEq a b | a -> b where
  (==) :: forall. a %1-> a %1-> b
  (/=) :: forall. a %1-> a %1-> b

-- | Multi-parameter ordering type class where boolean type is @b@
class MPEq a b => MPOrd a b | a -> b where
  ( <) :: forall. a %1-> a %1-> b
  (<=) :: forall. a %1-> a %1-> b
  ( >) :: forall. a %1-> a %1-> b
  (>=) :: forall. a %1-> a %1-> b

infixr 4 <, <=, >, >=, ==, /=
