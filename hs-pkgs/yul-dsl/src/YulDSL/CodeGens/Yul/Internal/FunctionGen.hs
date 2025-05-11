{-# LANGUAGE OverloadedStrings #-}
module YulDSL.CodeGens.Yul.Internal.FunctionGen
  ( compile_cat
  , compile_named_cat
  , compile_exported_fn
  ) where
-- base
import Control.Monad                        (mapAndUnzipM, unless, when)
import Data.Maybe                           (catMaybes)
import Data.Proxy                           (Proxy (Proxy))
import Data.Typeable                        (Typeable, typeRep)
import Unsafe.Coerce                        (unsafeCoerce)
-- text
import Data.Text.Lazy                       qualified as T
--
import YulDSL.Core
-- (codegen-utils)
import CodeGenUtils.CodeFormatters
import CodeGenUtils.Variable
--
import YulDSL.StdBuiltIns.ABICodec          ()
--
import YulDSL.CodeGens.Yul.Internal.CodeGen
import YulDSL.CodeGens.Yul.Internal.RhsExpr


--
-- compile_cat
--
-- Note, naming conventions:
--
-- _ ind :: Indenter
-- - _vars :: [Var]
-- _ _code :: Code
-- _ _cat  :: YulCat eff a b
-- - _ins/_outs :: [RhsExpr]
-- - _ces :: CodeExprs'

-- Compile a morphism with provided input and output variables.
compile_cat :: forall a b eff.
  (HasCallStack, YulO2 a b) =>
  YulCat eff a b ->
  Indenter ->
  ([Var], [Var]) ->
  CGState Code
compile_cat cat ind (a_vars, b_vars) = do
  (code, b_outs) <- gen_code_with_cat cat ind ("", fmap LetVar a_vars)
  pure $
    code <>
    assign_vars ind b_vars b_outs

-- Generate new code expressions from a morphism with provided code expressions.
gen_code_with_cat :: forall a b eff.
  (HasCallStack, YulO2 a b) =>
  YulCat eff a b ->
  Indenter ->
  CodeExprs' ->
  CGState CodeExprs'
gen_code_with_cat cat ind ces = do
  a_cg <- do_compile_cat cat
  get_code_exprs <$> gen_code a_cg ind (mk_code_exprs ces)

-- Workhorse of the morphism compilation routine.
do_compile_cat :: forall a b eff.
  HasCallStack =>
  YulCat eff a b ->
  CGState (CodeGen a b)
do_compile_cat = go
  where
    -- type conversions
    go (YulExtendType)           = build_rhs_aliases @a
    go (YulReduceType)           = build_rhs_aliases @a
    go (YulCoerceType)           = build_rhs_aliases @a
    -- categorical
    go (YulId)                   = build_rhs_aliases @a
    go (YulComp cb ac)           = go_comp cb ac
    -- monoidal
    go (YulProd ab cd)           = go_prod ab cd
    go (YulSwap @_ @m @n)        = go_swap @m @n
    -- cartesian
    go (YulFork ab ac)           = go_fork ab ac
    go (YulExl @_ @m @n)         = go_exl @m @n
    go (YulExr @_ @m @n)         = go_exr @m @n
    go (YulDis)                  = go_dis @a
    go (YulDup)                  = go_dup @a
    -- cartesian closed
    go (YulApply @_ @m @n)       = go_apply @eff @m @n
    go (YulCurry g)              = go_curry g
    -- co-cartesian
    go (YulEmb @_ @m @r x)       = go_emb @m @r x
    go (YulDyn d)                = go_dyn d
    -- control flows
    go (YulMapHask g)            = go_map_hask g
    go (YulSwitch cf cs cdef)    = go_switch cf cs cdef
    go (YulJmpU t)               = go_jmpu t
    go (YulJmpB b)               = go_jmpb b
    go (YulCall @_ @m @n sel)    = go_call @m @n 'O' sel
    -- storage effects
    go (YulSGet @_ @m)           = go_sget @m
    go (YulSPut @_ @m)           = go_sput @m
    --
    go (YulUnsafeCoerceEffect c) = do_compile_cat c

go_comp :: forall eff a b c.
  (HasCallStack, YulO3 a b c) =>
  YulCat eff c b -> YulCat eff a c ->
  CGState (CodeGen a b)
go_comp cb_cat ac_cat = pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
  let title = "comp " ++
        "(" ++ abiTypeCompactName @a ++ ") ~> " ++
        "(" ++ abiTypeCompactName @c ++ ") ~> " ++
        "(" ++ abiTypeCompactName @b ++ ")"
  decor_code <- cg_get_code_decor
  (code', c_outs) <- gen_code_with_cat ac_cat ind (code, a_ins)
  (code'', b_outs) <- gen_code_with_cat cb_cat ind (code', c_outs)
  pure $ mk_code_exprs (decor_code ind title code'', b_outs)

go_prod :: forall eff a b c d.
  (HasCallStack, YulO4 a b c d) =>
  YulCat eff a b -> YulCat eff c d ->
  CGState (CodeGen (a, c) (b, d))
go_prod ab_cat cd_cat = pure $ MkCodeGen \ind (get_code_exprs -> (code, ac_ins)) -> do
  let title = "prod " ++
        ("(" ++ abiTypeCompactName @a ++ ", " ++ abiTypeCompactName @c ++ ") ~> ") ++
        ("(" ++ abiTypeCompactName @b ++ ", " ++ abiTypeCompactName @d ++ ")")
  let  na = length (abiTypeInfo @a)
       a_ins = take na ac_ins
       c_ins = drop na ac_ins
  decor_code <- cg_get_code_decor
  (code', b_outs) <- gen_code_with_cat ab_cat ind (code, a_ins)
  (code'', d_outs) <- gen_code_with_cat cd_cat ind (code', c_ins)
  pure $ mk_code_exprs (decor_code ind title code'', b_outs <> d_outs)

go_swap :: forall a b.
  (HasCallStack, YulO2 a b) =>
  CGState (CodeGen (a, b) (b, a))
go_swap = pure $ MkCodeGen \ind (get_code_exprs -> (code, ab_ins)) -> do
  let title = "swap " ++ ("(" ++ abiTypeCompactName @a ++ ", " ++ abiTypeCompactName @b ++ ")")
  let na = length (abiTypeInfo @a)
      (a_ins, b_ins) = splitAt na ab_ins
  decor_code <- cg_get_code_decor
  pure $ mk_code_exprs (decor_code ind title code, b_ins <> a_ins)

go_fork :: forall a b c eff.
  (HasCallStack, YulO3 a b c) =>
  YulCat eff a b -> YulCat eff a c ->
  CGState (CodeGen a (b, c))
go_fork ab_cat ac_cat = pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
  let title = "fork " ++
        "(" ++ abiTypeCompactName @a ++ ") ~> " ++
        "(" ++ abiTypeCompactName @b ++ ", " ++ abiTypeCompactName @c ++ ")"
  decor_code <- cg_get_code_decor
  (code', b_outs) <- gen_code_with_cat ab_cat ind (code, a_ins)
  (code'', c_outs) <- gen_code_with_cat ac_cat ind (code', a_ins)
  pure $ mk_code_exprs (decor_code ind title code'', b_outs <> c_outs)

go_exl :: forall a b.
  (HasCallStack, YulO2 a b) =>
  CGState (CodeGen (a, b) a)
go_exl = pure $ MkCodeGen \ind (get_code_exprs -> (code, ab_ins)) -> do
  let title = "exl (" ++ abiTypeCompactName @a ++ ", " ++ abiTypeCompactName @b ++ ")"
      na = length (abiTypeInfo @a)
  decor_code <- cg_get_code_decor
  pure $ mk_code_exprs (decor_code ind title code, take na ab_ins)

go_exr :: forall a b.
  (HasCallStack, YulO2 a b) =>
  CGState (CodeGen (a, b) b)
go_exr = pure $ MkCodeGen \ind (get_code_exprs -> (code, ab_ins)) -> do
  let title = "exr (" ++ abiTypeCompactName @a ++ ", " ++ abiTypeCompactName @b ++ ")"
      na = length (abiTypeInfo @a)
  decor_code <- cg_get_code_decor
  pure $ mk_code_exprs (decor_code ind title code, drop na ab_ins)

go_dis :: forall a.
  (HasCallStack, YulO1 a) =>
  CGState (CodeGen a ())
go_dis = pure $ MkCodeGen \ind (get_code_exprs -> (code, _)) -> do
  let title =  "dis " ++ "(" ++ abiTypeCompactName @a ++ ")"
  decor_code <- cg_get_code_decor
  pure $ mk_code_exprs (decor_code ind title code, [])

go_dup :: forall a.
  (HasCallStack, YulO1 a) =>
  CGState (CodeGen a (a, a))
go_dup = pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
  let title = "dup (" ++ abiTypeCompactName @a ++ ")"
  decor_code <- cg_get_code_decor
  (b_vars, new_code_list) <- mapAndUnzipM
    (\case
        -- save SimpleExpr to a let variable to avoid duplicated runs.
        SimpleExpr expr -> do
          var <- cg_next_var
          pure ( var
               , Just (declare_vars ind [var] <>
                       assign_vars ind [var] [SimpleExpr expr])
               )
        -- pass on let variables, otherwise.
        LetVar var -> pure (var, Nothing)
        -- RhsThunk not supported
        RhsThunk _ -> error "dup does not support RhsThunk"
    ) a_ins
  let new_code = T.concat (catMaybes new_code_list)
  pure $ mk_code_exprs
    (decor_code ind title $
      code <>
      new_code
    , fmap LetVar (b_vars ++ b_vars))

go_apply :: forall eff a b.
  (HasCallStack, YulO2 a b) =>
  CGState (CodeGen (YulExp eff a b ⊗ a) b)
go_apply = pure $ MkCodeGen \ind (get_code_exprs -> (code, ga_ins)) -> do
  let a_ins = drop 1 ga_ins
      ab_cat = extract_rhs_thunk (ga_ins !! 0) a_ins :: YulCat eff a b
  mk_code_exprs <$> gen_code_with_cat ab_cat ind (code, a_ins)

go_curry :: forall eff a b c.
  (HasCallStack, YulO3 a b c) =>
  YulCat eff (a ⊗ b) c ->
  CGState (CodeGen a (YulExp eff b c))
go_curry ab2c_cat = pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
  let title = "curry (" ++
              abiTypeCompactName @a ++ ") ~> (" ++
              abiTypeCompactName @b <> " -> " <> abiTypeCompactName @c <> ")"
  decor_code <- cg_get_code_decor
  pure $ mk_code_exprs
    (decor_code ind title code,
     [RhsThunk \b_ins ->
         (YulDyn (mk_code_exprs ("", a_ins <> b_ins)) :: YulCat eff b (a ⊗ b))
         >.> ab2c_cat :: YulCat eff b c
     ])

go_emb :: forall b r.
  (HasCallStack, YulO2 b r) =>
  b ->
  CGState (CodeGen r b)
go_emb b =
  case length (abiTypeInfo @b) of
    -- trivially, embedding a unit generates no new code.
    0 -> pure $ MkCodeGen \_ (get_code_exprs -> (code, _)) -> pure $ mk_code_exprs (code, [])
    -- FIXME: proper implementation of embeddable
    1 -> build_inline_expr (const (T.pack (show b)))
    _ -> error ("Unembedable: " ++ show b)

go_dyn :: forall r b c.
  (Typeable c, YulO2 r b) =>
  c b ->
  CGState (CodeGen r b)
go_dyn cb = pure $ MkCodeGen \_ (get_code_exprs -> (code, _)) -> do
  let (_, b_outs) = gen_assert_msg "go_dyn: unexpected dynamic type"
                    (typeRep (Proxy @(c ())) == typeRep (Proxy @(CodeExprs ())))
                    (get_code_exprs (unsafeCoerce cb :: CodeExprs b))
  pure $ mk_code_exprs (code, b_outs)

go_map_hask :: forall eff a b r.
  YulO3 a b r =>
  (YulCat eff r a -> YulCat eff r b) ->
  CGState (CodeGen (r ⊗ a) b)
go_map_hask g = pure $ MkCodeGen \ind (get_code_exprs -> (code, ra_ins)) -> do
  let title = "maphask (" ++
              abiTypeCompactName @r <> "~>" <> abiTypeCompactName @a <> ") -> (" <>
              abiTypeCompactName @r <> "~>" <> abiTypeCompactName @b <> ")"
  decor_code <- cg_get_code_decor
  let nr = length (abiTypeInfo @r)
      r_ins = take nr ra_ins
      a_ins = drop nr ra_ins
      ra2b_cat = g (YulDyn (mk_code_exprs ("", a_ins)) :: YulCat eff r a) :: YulCat eff r b
  mk_code_exprs <$> gen_code_with_cat ra2b_cat ind (decor_code ind title code, r_ins)

go_switch :: forall eff a b.
  YulO2 a b =>
  YulCat eff a U256 ->        -- ^ case function
  [(U256, YulCat eff a b)] -> -- ^ switch cases
  YulCat eff a b ->           -- ^ default case
  CGState (CodeGen a b)
go_switch cf_cat cs_cats cdef_cat = pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
  let title = "switch (" <> abiTypeCompactName @a <> " ~> " <> abiTypeCompactName @b <> ")"
  decor_code <- cg_get_code_decor
  b_vars <- cg_create_vars @b
  (cf_code, cf_outs) <- gen_code_with_cat cf_cat ind ("", a_ins)
  cs' <- mapM (\(cid, c_cat) -> do
                 c_code <- gen_code_with_cat c_cat (indent ind) ("", a_ins)
                 pure (show cid, c_code)
              ) cs_cats
  (cdef_code, cdef_outs) <- gen_code_with_cat cdef_cat (indent ind) ("", a_ins)
  pure $ mk_code_exprs
    ( decor_code ind title $
      code <>
      cf_code <>
      declare_vars ind b_vars <>
      ind ("switch " <> rhs_expr_to_code (cf_outs !! 0)) <>
      foldMap (
        \(cid, (c_code, c_outs)) ->
          cbracket ind ("case " <> T.pack cid) \ind' ->
          c_code <>
          assign_vars ind' b_vars c_outs
        ) cs' <>
      cbracket ind "default"
      (\ind' -> cdef_code <>
        assign_vars ind' b_vars cdef_outs
      )
    , fmap LetVar b_vars)

go_jmpu :: forall eff a b.
  (HasCallStack, YulO2 a b) =>
  NamedYulCat eff a b ->
  CGState (CodeGen a b)
go_jmpu (cid, cat) = cg_insert_dependent_cat cid (MkAnyYulCat cat)
                     >> go_jmp 'u' ("u$" ++ cid)

go_jmpb :: forall a b p.
  ( HasCallStack, YulO2 a b
  , YulBuiltInPrefix p a b
  ) =>
  YulBuiltIn p a b ->
  CGState (CodeGen a b)
go_jmpb p = cg_use_builtin (MkAnyYulBuiltIn p)
            >> go_jmp 'b' (yulB_fname p)

go_jmp :: forall a b.
  (HasCallStack, YulO2 a b) =>
  Char -> String ->
  CGState (CodeGen a b)
go_jmp t fname = do
  let callExpr a_ins = T.pack fname <> "(" <> T.intercalate ", " (fmap rhs_expr_to_code a_ins) <> ")"
  -- for built-in functions, inline form may also be used to make code look more compact
  -- for internal functions though, we don't want to assume they don't produce any side effect
  if t == 'b' && length (abiTypeInfo @b) <= 1
    -- NOTE only build inline expr if it is pure effect and outputs only one variable
    then build_inline_expr callExpr
    else pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
    b_vars <- cg_create_vars @b
    pure $ mk_code_exprs
      ( code <>
        declare_vars ind b_vars <>
        ind (T.intercalate ", " (fmap unVar b_vars) <> " := " <> callExpr a_ins)
      , fmap LetVar b_vars )

go_call :: forall a b.
  (HasCallStack, YulO2 a b) =>
  Char -> SELECTOR ->
  CGState (CodeGen ((YulCallTarget, YulCallValue, YulCallGasLimit), a) b)
go_call effCode sel = pure $ MkCodeGen \ind (get_code_exprs -> (code, a_ins)) -> do
  let title = "cal" ++ effCode:" " ++ abiTypeCompactName @a ++ " ~> " ++ abiTypeCompactName @b
      callTargetExpr = a_ins !! 0
      callValueExpr = a_ins !! 1
      callGasLimitExpr = a_ins !! 2
      dataSize = length (abiTypeInfo @b) * 32
      abienc_builtin = MkYulBuiltIn @"__abienc_from_stack_c_" @(U256, a) @U256
      abidec_builtin = MkYulBuiltIn @"__abidec_from_memory_c_" @(U256, U256) @b
  decor_code <- cg_get_code_decor
  b_vars <- cg_create_vars @b
  when (length a_ins > 2) $ cg_use_builtin (MkAnyYulBuiltIn abienc_builtin)
  unless (null b_vars) $ cg_use_builtin (MkAnyYulBuiltIn abidec_builtin)
  pure $ mk_code_exprs
    ( decor_code ind title $
      code <>
      declare_vars ind b_vars <>
      T.unlines
      ((T.init . ind) <$>
        [ "let callTarget := " <> rhs_expr_to_code callTargetExpr
        , "let callValue := " <> rhs_expr_to_code callValueExpr
        , "let callGasLimit := " <> rhs_expr_to_code callGasLimitExpr
        , "if iszero(callGasLimit) { callGasLimit := gas() }"
        , "let memPos := allocate_unbounded()"
        , "mstore(memPos, shl(224, " <> T.pack (showSelectorOnly sel) <> "))"
        , "let memEnd := " <>
          if (length a_ins > 2)
          then T.pack (yulB_fname abienc_builtin) <> "(add(memPos, 4), " <> spread_rhs (drop 3 a_ins) <> ")"
          else "add(memPos, 4)"
        ]) <>
      -- call(g, a, v, in, insize, out, outsize)
      --
      -- call contract at address a with input mem[in…(in+insize)) providing g gas and v wei and output area
      -- mem[out…(out+outsize)) returning 0 on error (eg. out of gas) and 1 on success See more
      ind ( "let success := call" <>
            "( callGasLimit" <>
            ", callTarget"<>
            ", callValue" <>
            ", memPos" <> -- in
            ", sub(memEnd, memPos)" <> -- inSize
            ", memPos" <> -- out
            ", " <> T.pack (show dataSize) <>
            ")" -- outSize
          ) <>
      T.unlines
      ((T.init . ind) <$>
        [ "if iszero(success) { revert_forward_1() }"
        , "if success {"
        , " let rsize := " <> T.pack (show dataSize)
        , " if gt (rsize, returndatasize()) { rsize := returndatasize() }"
        , " finalize_allocation(memPos, rsize)"
        ] ++
        ([ " " <> spread_vars b_vars <> " := " <>
           T.pack (yulB_fname abidec_builtin) <> "(memPos, add(memPos, rsize))"
         | not (null b_vars) ]) ++
        [ "}" ])
    , fmap LetVar b_vars )

go_sget :: forall a.
  (HasCallStack, YulO1 a, ABIWordValue a) =>
  CGState (CodeGen B32 a)
go_sget = pure $ MkCodeGen \ind (get_code_exprs -> (code, ins)) -> do
  a_vars <- cg_create_vars @a
  pure $ gen_assert_msg "go_sget expect word value" (length a_vars == 1)
    mk_code_exprs
    ( code <>
      declare_vars ind a_vars <>
      ind (spread_vars a_vars <> " := sload(" <> rhs_expr_to_code (ins !! 0) <> ")")
    , fmap LetVar a_vars)

go_sput :: forall a.
  (HasCallStack, YulO1 a) =>
  CGState (CodeGen (B32, a) ())
go_sput = pure $ MkCodeGen \ind (get_code_exprs -> (code, ins)) -> do
  pure $ mk_code_exprs
    ( code <>
      ind ("sstore(" <> T.intercalate ", " (fmap rhs_expr_to_code ins) <> ")")
    , [])

--
-- other compilation interfaces
--

compile_named_cat :: forall a b eff.
  (HasCallStack, YulO2 a b) =>
  Indenter -> NamedYulCat eff a b -> CGState Code
compile_named_cat ind (cid, cat) = do
  vars_a <- cg_create_vars @a
  vars_b <- cg_create_vars @b

  code <- cbracket_m ind
    ( "function " <> T.pack ("u$" ++ cid) <>
      "(" <> spread_vars vars_a <> ")" <>
      (if null vars_b then "" else " -> " <> spread_vars vars_b)
    )
    ( \ind' -> do
        body <- compile_cat cat ind' (vars_a, vars_b)
        pure $
          body <>
          ind' "leave"
    )

  cg_reset_for_fn
  pure code

compile_exported_fn :: HasCallStack => Indenter -> AnyExportedYulCat -> CGState Code
compile_exported_fn ind f = withAnyExportedYulCat f (compile_named_cat ind)
