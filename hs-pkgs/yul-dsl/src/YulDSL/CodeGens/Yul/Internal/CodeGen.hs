{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings   #-}
module YulDSL.CodeGens.Yul.Internal.CodeGen
  ( -- $codegen_state
    CodeGenConfig (..)
  , CGState
  , cg_run
  , cg_reset_for_fn
  , cg_reset_for_object
    -- $codegen_vars
  , cg_next_var
  , cg_create_vars
    -- $codegen_dependencies
  , cg_list_dependent_cats
  , cg_insert_dependent_cat
    -- $codegen_builtins
  , cg_use_builtin
  , cg_gen_builtin_codes
  , cg_get_code_decor
  ) where

-- base
import Control.Monad               (replicateM)
import Data.Functor                ((<&>))
-- mtl
import Control.Monad.State.Lazy    (MonadState (..), State, evalState, modify)
-- text
import Data.Text.Lazy              qualified as T
-- containers
import Data.Map.Strict             qualified as Map
import Data.Set                    qualified as Set
--
import YulDSL.Core
-- CodeGenUtils
import CodeGenUtils.CodeFormatters
import CodeGenUtils.Variable


-- $codegen_state
-- == CodeGen State

data CodeGenConfig = MkCodeGenConfig
  { cg_config_debug_level :: Int
  , cg_config_dummy       :: Bool -- for testing
  }

-- | CodeGen state data.
data CGStateData = MkCGStateData
  { cg_config      :: CodeGenConfig
  , var_gen        :: AutoVarGen
  , dependent_cats :: Map.Map String AnyYulCat -- cat_id -> cat
  , builtin_used   :: Set.Set AnyYulBuiltIn
  }

-- | CodeGen state.
type CGState = State CGStateData

-- | Initial CodeGen state data.
init_cg_state_data :: CodeGenConfig -> CGStateData
init_cg_state_data config = MkCGStateData
  { cg_config = config
  , var_gen = MkAutoVarGen 0
  , dependent_cats = Map.empty
  , builtin_used = Set.empty
  }

-- | Generate code from the initial CodeGen state.
cg_run :: CodeGenConfig -> CGState Code -> Code
cg_run config s = evalState s (init_cg_state_data config)

-- | Reset the CodeGen for new function generation.
cg_reset_for_fn :: CGState ()
cg_reset_for_fn = modify $
  \s -> s { var_gen = MkAutoVarGen 0
          }

cg_reset_for_object :: CGState ()
cg_reset_for_object = do
  modify $ \s -> s { dependent_cats = Map.empty
                   , builtin_used = Set.empty
                   }
  cg_reset_for_fn

-- $codegen_vars
-- == CodeGen Variables

-- | Generate the next variable name.
cg_next_var :: CGState Var
cg_next_var = do
  s <- get
  let (v, g) = new_auto_var (var_gen s)
  put (s { var_gen = g
         })
  return v

-- | Create undeclared variables needed for the type @a@.
cg_create_vars :: forall a. YulO1 a => CGState [Var]
cg_create_vars = replicateM (length (abiTypeInfo @a)) cg_next_var

-- $codegen_dependencies
-- == CodeGen YulCat Dependencies

cg_list_dependent_cats :: CGState [(String, AnyYulCat)]
cg_list_dependent_cats = get <&> Map.toList . dependent_cats

cg_insert_dependent_cat :: String -> AnyYulCat -> CGState ()
cg_insert_dependent_cat depId depCat = modify
  (\d@(MkCGStateData { dependent_cats = deps }) -> d { dependent_cats = Map.insert depId depCat deps })

-- $codegen_builtins
-- == CodeGen Builtins

cg_use_builtin :: AnyYulBuiltIn -> CGState ()
cg_use_builtin b = modify
  (\d@(MkCGStateData { builtin_used }) -> d { builtin_used = Set.insert b builtin_used })

cg_gen_builtin_codes :: Indenter -> CGState [Code]
cg_gen_builtin_codes ind = get >>= \(MkCGStateData{ builtin_used }) ->
  let allBuiltIns = closure get_deps builtin_used
  in pure $
     filter (not . T.null) $ -- some built-ins are built-in of yul language, hence with empty extra code.
     map (\b -> fst (yulB_code b) ind) (Set.toList allBuiltIns)
  where closure f s0 = go (Set.toList s0) s0
          where go xs s =
                  let xs' = concatMap f xs
                      s'  = Set.union s (Set.fromList xs')
                  in if Set.size s == Set.size s' then s
                  else go (Set.toList (Set.difference s' s)) s'
        get_deps b@(MkAnyYulBuiltIn b') = let (_,_,_,deps) = yulB_body b' in b:deps


-- | Decorate code with a opening and closing titles for debugging purpose.
decor_code :: Indenter -> String -> Code -> Code
decor_code ind title code =
  ind ("//dbg: +" <> T.pack title) <>
  code <>
  ind ("//dbg: -" <> T.pack title)

cg_get_code_decor :: CGState (Indenter -> String -> Code -> Code)
cg_get_code_decor = get >>= \(MkCGStateData { cg_config = MkCodeGenConfig { cg_config_debug_level = lvl } }) ->
  if lvl > 0
  then pure (decor_code)
  else pure (\_ _ code -> code)
