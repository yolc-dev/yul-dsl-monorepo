{-# LANGUAGE OverloadedStrings #-}
module YulDSL.CodeGens.Yul.Internal.RhsExpr
  ( -- * Right-hand-side Expression
    RhsExpr (LetVar, SimpleExpr, RhsThunk)
  , extract_rhs_thunk, rhs_expr_to_code, spread_rhs, assign_vars
    -- * Right-hand-side Expression Generator
  , CodeExprs', CodeExprs (get_code_exprs), mk_code_exprs
  , CodeGen (MkCodeGen, gen_code)
  , build_rhs_aliases, build_inline_expr
  ) where
-- base
import Unsafe.Coerce                        (unsafeCoerce)
-- text
import Data.Text.Lazy                       qualified as T
-- yul-dsl
import YulDSL.Core
-- CodeGenUtils
import CodeGenUtils.CodeFormatters
import CodeGenUtils.Variable
--
import YulDSL.CodeGens.Yul.Internal.CodeGen


------------------------------------------------------------------------------------------------------------------------
-- RhsExpr
------------------------------------------------------------------------------------------------------------------------

-- | Types of right-hand-side (RHS) expressions.
data RhsExpr
  = LetVar Var      -- ^ Declared let var
  | SimpleExpr Code -- ^ Simple expression that can be used directly in place of a let var
  | forall eff a b. YulO2 a b => RhsThunk ([RhsExpr] -> YulCat eff a b)

instance Show RhsExpr where
  show (LetVar var)   = "LetVar " ++ show var
  show (SimpleExpr _) = "SimpleExpr"
  show (RhsThunk _)   = "RhsThunk"

extract_rhs_thunk :: forall eff a b. (HasCallStack, YulO2 a b) => RhsExpr -> [RhsExpr] -> YulCat eff a b
extract_rhs_thunk (RhsThunk (g :: [RhsExpr] -> YulCat eff' a' b')) a_ins =
  gen_assert_msg ("extract_rhs_thunk: bad type " <>
                  abiTypeCompactName @a' <> " ?= " <> abiTypeCompactName @a <> ";" <>
                  abiTypeCompactName @b' <> " ?= " <> abiTypeCompactName @b)
  (abiTypeCompactName @a' == abiTypeCompactName @a && abiTypeCompactName @b' == abiTypeCompactName @b)
  (unsafeCoerce (g a_ins))
extract_rhs_thunk _ _ = error "extract_rhs_thunk: not a thunk"

-- | Render RHS expression to code.
rhs_expr_to_code :: HasCallStack => RhsExpr -> Code
rhs_expr_to_code (LetVar x)     = unVar x
rhs_expr_to_code (SimpleExpr x) = x
rhs_expr_to_code (RhsThunk _)   = "0 // thunk" -- error "cannot expand rhs thunk"

-- | Spread variables separated by comma.
spread_rhs :: HasCallStack => [RhsExpr] -> Code
spread_rhs = T.intercalate ", " . fmap rhs_expr_to_code

-- | Assign variables to RHS expressions.
assign_vars :: HasCallStack => Indenter -> [Var] -> [RhsExpr] -> Code
assign_vars ind vars rexprs =
  gen_assert_msg ("assign_vars" ++ show(length vars, length rexprs))
  (length vars == length rexprs)
  (T.unlines $
    zipWith
    (\a b -> T.init $ ind $ a <> " := " <> b)
    (fmap unVar vars)
    (fmap rhs_expr_to_code rexprs))

------------------------------------------------------------------------------------------------------------------------
-- CodeGen
------------------------------------------------------------------------------------------------------------------------

-- | Code and RHS expressions to interact the output of the code (usually variables).
type CodeExprs' = (Code, [RhsExpr])

-- | CodeExprs' with tagged type @a@; to make it type-safe, only its smart constructor should be used.
newtype CodeExprs a = MkCodeExprs { get_code_exprs :: CodeExprs' } deriving Show
type role CodeExprs nominal

-- | Create a CodeExprs with assertions.
mk_code_exprs :: forall a. (HasCallStack, YulO1 a) => CodeExprs' -> CodeExprs a
mk_code_exprs (code, outs) =
  let co = length (abiTypeInfo @a)
  in gen_assert_msg
     ("mk_code_exprs: " ++ abiTypeCanonName @a ++ " != " ++ show outs)
     (length outs == co)
     (MkCodeExprs (code, outs))

-- | Generate code of for a morphism @a ~> b@, where both @a@ and @b@ have its own CodeExprsBuilder.
newtype CodeGen a b = MkCodeGen
  { gen_code :: Indenter -> CodeExprs a -> CGState (CodeExprs b) }

-- | Build RHS expression that are aliases of inputs.
build_rhs_aliases :: forall a b.
  (HasCallStack, YulO2 a b) =>
  CGState (CodeGen a b)
build_rhs_aliases = pure $ MkCodeGen \_ (MkCodeExprs a_ces) -> pure (mk_code_exprs a_ces)

-- | Build expression from the rhs expression of type @a@ to an inline output expression.
build_inline_expr :: forall a b.
  (HasCallStack, YulO2 a b) =>
  ([RhsExpr] -> Code) ->
  CGState (CodeGen a b)
build_inline_expr g = pure $ MkCodeGen \_ (MkCodeExprs (code, a_ins)) -> pure $
  mk_code_exprs (code, [SimpleExpr (g a_ins)])
