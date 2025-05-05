{-# LANGUAGE OverloadedStrings #-}
module YulDSL.CodeGens.Yul.Internal.RhsExpr
  ( -- * Right-hand-side Expression
    RhsExpr (LetVar, SimpleExpr)
  , rhs_expr_to_code, spread_rhs, mk_rhs_vars, assign_vars
    -- * Right-hand-side Expression Generator
  , mk_rhs_expr_builder, build_rhs_expr
  , RhsExprGen (gen_rhs_exprs), NonExpRhsExprGen
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
assign_vars ind vars rexprs =
  gen_assert_msg ("assign_vars" ++ show(length vars, length rexprs))
  (length vars == length rexprs)
  (T.unlines $
    zipWith
    (\a b -> T.init $ ind $ a <> " := " <> b)
    (fmap unVar vars)
    (fmap rhs_expr_to_code rexprs))

------------------------------------------------------------------------------------------------------------------------
-- RhsExprGen
------------------------------------------------------------------------------------------------------------------------

newtype RhsExprBuilder a_ {- contra-variant -} a {- covariant -} = MkTaggedRhsExpr ([RhsExpr] -> [RhsExpr])

mk_rhs_expr_builder :: forall a_ a. YulO2 a_ a => ([RhsExpr] -> [RhsExpr]) -> RhsExprBuilder a_ a
mk_rhs_expr_builder g = MkTaggedRhsExpr
  \contras ->
    let contras' = gen_assert_msg
          ("mk_rhs_expr_builder contras: " ++ abiTypeCanonName @a_ ++ " != " ++ show contras)
          (length (abiTypeInfo @a_) == length contras)
          contras
        covariants = g contras'
        covariants' = gen_assert_msg
          ("mk_rhs_expr_builder covariants: " ++ abiTypeCanonName @a ++ " != " ++ show covariants)
          (length (abiTypeInfo @a) == length covariants)
          covariants
    in covariants'

build_rhs_expr :: forall a_ a. YulO2 a_ a => RhsExprBuilder a_ a -> [RhsExpr] -> [RhsExpr]
build_rhs_expr (MkTaggedRhsExpr g) = g -- we assume it's built with assertion-ridden mk_rhs_expr_builder

-- | RHS expression generator.
newtype RhsExprGen a_ a b_ b = MkRhsExprGen
  { -- ^ Generate new code and transform from @RhsExprBuilder a_ a@ to @RhsExprBuilder b_ b@
    gen_rhs_exprs  :: Indenter ->
                      (Code, RhsExprBuilder a_ a) ->
                      CGState (Code, RhsExprBuilder b_ b)
  }

-- | RHS expression generator that doesn't require contravariants (exponential objects).
type NonExpRhsExprGen a b = RhsExprGen () a () b

-- | Build RHS expression that are aliases of inputs.
build_rhs_aliases :: forall a b.
  (HasCallStack, YulO2 a b) =>
  CGState (RhsExprGen () a () b)
build_rhs_aliases = pure $ MkRhsExprGen
   \_ (code, ins) -> pure (code, mk_rhs_expr_builder @() @b $ const (build_rhs_expr ins []))

-- | Build expression from the rhs expression of type @a@ to an inline output expression.
build_inline_expr :: forall a b.
  (HasCallStack, YulO2 a b) =>
  ([RhsExpr] -> CGState Code) ->
  CGState (RhsExprGen () a () b)
build_inline_expr g = pure $ MkRhsExprGen
  \_ (code, ins) -> do
    out <- g (build_rhs_expr ins [])
    pure (code, mk_rhs_expr_builder (const [SimpleExpr out]))

-- | Build a code block from the RHS expression of type @a@ to a RHS expression of type @b@.
build_code_block :: forall a b.
  (HasCallStack, YulO2 a b) =>
  (Indenter -> (Code, [RhsExpr]) -> CGState (Code, [RhsExpr])) ->
  CGState (RhsExprGen () a () b)
build_code_block g = pure $ MkRhsExprGen
  \ind (code, ins) -> do
    (code', outs) <- g ind (code, build_rhs_expr ins [])
    pure (code', mk_rhs_expr_builder @() @b (const outs))
