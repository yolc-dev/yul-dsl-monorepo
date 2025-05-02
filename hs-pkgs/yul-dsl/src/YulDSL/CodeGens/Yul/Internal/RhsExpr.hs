{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
module YulDSL.CodeGens.Yul.Internal.RhsExpr
  ( -- * Right-hand-side Expression
    RhsExpr (LetVar, SimpleExpr)
  , rhs_expr_to_code, spread_rhs, mk_rhs_vars, assign_vars
    -- * Right-hand-side Expression Generator
  , RhsExprGen (rhs_exprs_spec, gen_rhs_exprs)
  , build_rhs_aliases, build_inline_expr, build_code_block
  ) where
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
  deriving Show

-- | Render RHS expression to code.
rhs_expr_to_code :: RhsExpr -> Code
rhs_expr_to_code (LetVar x)     = unVar x
rhs_expr_to_code (SimpleExpr x) = x

-- | Spread variables separated by comma.
spread_rhs :: [RhsExpr] -> Code
spread_rhs = T.intercalate ", " . fmap rhs_expr_to_code

-- | Create LetVar RHS expressions from variables.
mk_rhs_vars :: [Var] -> [RhsExpr]
mk_rhs_vars = fmap LetVar

-- | Assign variables to RHS expressions.
assign_vars :: HasCallStack =>
  Indenter -> [Var] -> [RhsExpr] -> Code
assign_vars ind vars rexprs = gen_assert_msg ("assign_vars" ++ show(length vars, length rexprs))
                              (length vars == length rexprs) $ T.unlines $
  zipWith
  (\a b -> T.init $ ind $ a <> " := " <> b)
  (fmap unVar vars)
  (fmap rhs_expr_to_code rexprs)

------------------------------------------------------------------------------------------------------------------------
-- RhsExprGen
------------------------------------------------------------------------------------------------------------------------

-- | RHS expression generator.
data RhsExprGen = MkRhsExprGen
  { -- ^ (nIns, nOuts)
    rhs_exprs_spec :: (Int, Int)
    -- ^ Generate from "nIns" of [RhsExpr] to a fragment of code and "nOuts" of [RhsExpr]
  , gen_rhs_exprs  :: Indenter -> (Code, [RhsExpr]) -> CGState (Code, [RhsExpr])
  }

-- | Build RHS expression that are aliases of inputs.
build_rhs_aliases :: forall a. (HasCallStack, YulO1 a) =>
  CGState RhsExprGen
build_rhs_aliases = pure $
  let n = length (abiTypeInfo @a)
  in MkRhsExprGen (n, n) (\_ (code, ins) -> pure (code, ins))

-- | Build expression from the rhs expression of type @a@ to an inline output expression.
build_inline_expr :: forall a. (HasCallStack, YulO1 a) =>
  ([RhsExpr] -> CGState Code) ->
  CGState RhsExprGen
build_inline_expr g = pure $
  let n = length (abiTypeInfo @a)
  in MkRhsExprGen (n, 1) $ \_ (code, ins) ->
    gen_assert_msg ("mk_inline_expr" ++ show (n, length ins))
    (length ins == n)
    (g ins >>= \out -> pure (code, [SimpleExpr out]))

-- | Build a code block from the RHS expression of type @a@ to a RHS expression of type @b@.
build_code_block :: forall a b. (HasCallStack, YulO2 a b) =>
  (Indenter -> (Code, [RhsExpr]) -> CGState (Code, [RhsExpr])) ->
  CGState RhsExprGen
build_code_block g = pure $
  let na = length (abiTypeInfo @a)
      nb = length (abiTypeInfo @b)
  in MkRhsExprGen (na, nb) $ \ind (code, ins) ->
    gen_assert_msg ("mk_code_block nIns" ++ show (na, length ins))
    (length ins == na)
    (g ind (code, ins) >>= \(code', outs) ->
                             gen_assert_msg ("mk_code_block nOuts" ++ show (nb, length outs))
                             (length outs == nb)
                             pure (code', outs))
