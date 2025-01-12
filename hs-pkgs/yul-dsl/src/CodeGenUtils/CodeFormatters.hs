{-# LANGUAGE OverloadedStrings #-}
module CodeGenUtils.CodeFormatters
  ( Code
  , Indenter
  , add_indent, indent, init_ind
  , cbracket_m, cbracket, cbracket1, decor_code
  , HasCallStack, gen_assert_msg
  ) where
-- base
import Data.Functor.Identity (Identity (runIdentity))
import GHC.Stack             (HasCallStack)
-- text
import Data.Text.Lazy        qualified as T


-- | Code is text.
type Code = T.Text

-- | Indentation formatter.
type Indenter = Code -> Code

-- | Add one level of indentation to a text.
add_indent :: Indenter
add_indent s = " " <> s

-- | Add one level of indentation to an indenter.
indent :: Indenter -> Indenter
indent ind s = add_indent (ind s)

-- | Initial line indentation.
init_ind :: Indenter
init_ind s = s <> "\n"

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

-- | Decorate code with a opening and closing titles for debugging purpose.
decor_code :: Indenter -> T.Text -> Code -> Code
decor_code ind title code =
  ind ("//dbg: +" <> title) <>
  code <>
  ind ("//dbg: -" <> title)

-- | Assert true or stop code generation with a message.
gen_assert_msg :: HasCallStack => String -> Bool -> a -> a
gen_assert_msg msg False _ = error msg
gen_assert_msg _     _ x   = x
