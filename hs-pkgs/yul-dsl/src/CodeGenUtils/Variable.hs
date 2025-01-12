{-# LANGUAGE OverloadedStrings #-}
module CodeGenUtils.Variable
  ( Var (MkVar, unVar)
  , AutoVarGen (MkAutoVarGen), cur_var, new_auto_var
  , gen_vars, spread_vars, declare_vars
  ) where
-- base
import Data.Char                   (chr)
import Data.Function               ((&))
-- text
import Data.Text.Lazy              qualified as T
-- CodeGenUtils
import CodeGenUtils.CodeFormatters


-- | A variable represented by its name.
newtype Var = MkVar { unVar :: Code }

-- | Variable generator state.
newtype AutoVarGen = MkAutoVarGen Int

-- | Current variable name the generator: a, b, c,..aa, ab, ac,..
cur_var :: AutoVarGen -> Var
cur_var (MkAutoVarGen i0) = MkVar ("v_" <> T.pack (go i0)) where
  go i = if i < 26 then [chr (i + 97)] else let (j, i') = i `divMod` 26 in [chr (j + 96)] <> go i'

-- | Generate a new auto variable.
new_auto_var :: AutoVarGen -> (Var, AutoVarGen)
new_auto_var g@(MkAutoVarGen i0) = (cur_var g, MkAutoVarGen (i0 + 1))

-- | Generate a list of variables for the 'ABITypeable' a.
--
-- Examples:
-- >>> gen_vars 3
-- ["v_a","v_b","v_c"]
gen_vars :: Int -> [Var]
gen_vars n = snd $ foldr
             (\ _ (gen, vars) -> new_auto_var gen & \ (var, gen') -> (gen', vars <> [var]))
             (MkAutoVarGen 0, [])
             (drop 1 [0..n])

-- | Spread variables separated by comma.
spread_vars :: [Var] -> Code
spread_vars = T.intercalate ", " . fmap unVar

-- | Declare variables in an one-liner let expression.
declare_vars :: Indenter -> [Var] -> Code
declare_vars ind vars = if null vars then ""
                        else ind ("let " <> spread_vars vars)
