{-# LANGUAGE OverloadedStrings #-}
module CodeGenUtils.CodeFormatters
  ( Code
  , Indenter, init_ind, add_indent, indent
  , cbracket_m, cbracket, cbracket1
  , HasCallStack, gen_assert_msg
  ) where
-- base
import Data.Functor.Identity (Identity (runIdentity))
import GHC.Stack             (HasCallStack)
-- text
import Data.Text.Lazy        qualified as T


-- | Code is text.
type Code = T.Text

-- | Indentation formatter, inspired by ShowS.
type Indenter = Code -> Code

-- | Initial line indentation.
init_ind :: Indenter
init_ind s = s <> "\n"

-- | Add one level of indentation to a text.
add_indent :: Indenter
add_indent s = " " <> s

-- | Add one level of indentation to an indenter.
indent :: Indenter -> Indenter
indent ind s = add_indent (ind s)

-- | Wrap monadic code gen in a pair of curly brackets.
cbracket_m :: Monad m => Indenter -> Code -> (Indenter -> m Code) -> m Code
cbracket_m ind prefix codegen = codegen (indent ind) >>=
                                \code -> pure (ind (prefix' <> "{" ) <> code <> ind "}")
  where prefix' = if prefix == "" then "" else prefix <> " "

-- | Wrap code in a pair of curly brackets.
cbracket :: Indenter -> Code -> (Indenter -> Code) -> Code
cbracket ind prefix codegen = runIdentity $ cbracket_m ind prefix (pure . codegen)

-- | Wrap a one liner in a pair of curly brackets.
cbracket1 :: Indenter -> Code -> Code -> Code
cbracket1 ind prefix oneliner = cbracket ind prefix ($ oneliner)

-- | Assert true or stop code generation with a message.
gen_assert_msg :: HasCallStack => String -> Bool -> a -> a
gen_assert_msg msg False _ = error msg
gen_assert_msg _     _ x   = x
