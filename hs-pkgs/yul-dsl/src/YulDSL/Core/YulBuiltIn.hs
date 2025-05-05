{-|
Copyright   : (c) 2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides type class and data types for defining yul built-in functions.

-}
{-# LANGUAGE OverloadedStrings #-}
module YulDSL.Core.YulBuiltIn
  ( YulBuiltInPrefix (IsYulBuiltInNonPure, yulB_prefix , yulB_fname, yulB_body, yulB_eval)
  , YulBuiltIn (MkYulBuiltIn), AnyYulBuiltIn (MkAnyYulBuiltIn)
  , yulB_code
  , Symbol
  ) where
-- base
import GHC.TypeLits                (KnownSymbol (symbolSing), Symbol, fromSSymbol)
-- text
import Data.Text.Lazy              qualified as T
-- (codegen-util)
import CodeGenUtils.CodeFormatters (Code, Indenter, indent)
import CodeGenUtils.Variable       (Var, spread_vars)


-- | Yul built-in definition.
class KnownSymbol prefix => YulBuiltInPrefix (prefix :: Symbol) a b where
  -- | Declare whether if the built-in non-pure.
  type family IsYulBuiltInNonPure prefix :: Bool
  -- | By default, built-ins are pure, hence can be used in all morphisms.
  type instance IsYulBuiltInNonPure prefix = False

  -- | Yul prefix to string.
  yulB_prefix :: forall. YulBuiltIn prefix a b -> String
  yulB_prefix _ = fromSSymbol $ symbolSing @prefix
  -- | Yul function name for the built-in.
  yulB_fname :: forall. YulBuiltIn prefix a b -> String
  -- | Optional yul function body, which consists of in-vars, out-vars, lines of code, and built-in dependencies.
  yulB_body :: forall. YulBuiltIn prefix a b -> ([Var], [Var], [Code], [AnyYulBuiltIn])
  -- | Equivalent evaluation function for the built-in.
  yulB_eval :: forall. YulBuiltIn prefix a b -> (a -> b)

instance YulBuiltInPrefix p a b => Show (YulBuiltIn p a b) where
  show = yulB_fname

-- | Reference to an instance of yul built-in by its prefix @p@, domain and codomain types @a -> b@.
data YulBuiltIn p a b where
  MkYulBuiltIn :: forall p a b. YulBuiltInPrefix p a b => YulBuiltIn p a b

-- | Existential wrapper for 'YulBuiltIn'.
data AnyYulBuiltIn where
  MkAnyYulBuiltIn :: forall p a b. YulBuiltInPrefix p a b => YulBuiltIn p a b -> AnyYulBuiltIn

-- | Generate code from any yul built-in.
yulB_code :: AnyYulBuiltIn -> (Indenter -> Code, [AnyYulBuiltIn])
yulB_code (MkAnyYulBuiltIn p) =
  let fname = yulB_fname p
      (inVars, outVars, codeLines, deps) = yulB_body p
  in (, deps) $ \ind ->
    let ind' = indent ind
    in ind ("function " <> T.pack fname <>
            "(" <> spread_vars inVars <> ")" <>
            (if null outVars then "" else " -> " <> spread_vars outVars) <>
            " { ") <>
       (foldr (T.append . ind') T.empty codeLines) <>
       ind ("}")

instance YulBuiltInPrefix p a b => Eq (YulBuiltIn p a b) where
  a == b = yulB_fname a == yulB_fname b

instance YulBuiltInPrefix p a b => Ord (YulBuiltIn p a b) where
  a <= b = yulB_fname a <= yulB_fname b

instance Eq AnyYulBuiltIn where
  (MkAnyYulBuiltIn a) == (MkAnyYulBuiltIn b) = yulB_fname a == yulB_fname b

instance Ord AnyYulBuiltIn where
  (MkAnyYulBuiltIn a) <= (MkAnyYulBuiltIn b) = yulB_fname a <= yulB_fname b
