{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.CodeGens.ShowGens
  ( yulCatCompactShow
  , yulCatToUntypedLisp
  ) where
-- base
import Data.Bifunctor              (first)
import Data.Functor.Const          (Const (Const))
-- text
import Data.Text.Lazy              qualified as T
-- eth-abi
import Ethereum.ContractABI
--
import CodeGenUtils.CodeFormatters
import YulDSL.Core.YulBuiltIn
import YulDSL.Core.YulCallSpec
import YulDSL.Core.YulCat


-- | Compact and unique representation of 'YulCat', which can be used for generate its fingerprint.
--
--   Note:
--   * It is done so for the compactness of the string representation of the 'YulCat'.
yulCatCompactShow :: YulCat eff a b -> String
yulCatCompactShow = go
  where
    go :: YulCat eff a b -> String
    go (YulReduceType @_ @a @b)    = "Tr" <> abi_type_name2 @a @b
    go (YulExtendType @_ @a @b)    = "Te" <> abi_type_name2 @a @b
    go (YulCoerceType @_ @a @b)    = "Tc" <> abi_type_name2 @a @b
    go (YulUnsafeCoerceEffect c)   = go c
    --
    go (YulId @_ @a)               = "id" <> abi_type_name @a
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    --
    go (YulProd ab cd)             = "(" <> go ab <> ")×(" <> go cd <> ")"
    go (YulSwap @_ @a @b)          = "σ" <> abi_type_name2 @a @b
    --
    go (YulFork ab ac)             = "(" <> go ab <> ")▵(" <> go ac <> ")"
    go (YulExl @_ @a @b)           = "π₁" <> abi_type_name2 @a @b
    go (YulExr @_ @a @b)           = "π₂" <> abi_type_name2 @a @b
    go (YulDis @_ @a)              = "ε" <> abi_type_name @a
    go (YulDup @_ @a)              = "δ" <> abi_type_name @a
    --
    go (YulApply @_ @a @b)         = abi_type_name @b ++ "^" ++ abi_type_name @a
    go (YulCurry ab2c)             = "→" ++ "(" ++ go ab2c ++ ")"
    --
    go (YulEmb @_ @b @r x)         = "{" <> show x <> "}" <> abi_type_name2 @b @r
    go (YulDyn _)                  = "_"
    --
    go (YulMapHask g)              = go (g (YulDyn (Const ())))
    go (YulSwitch cf cs cdef)      = "?" <> "(" <> go cf <> ")(" <> go_switch_case cs cdef <> ")"
    go (YulJmpU @_ @a @b (cid, _)) = "Ju " <> cid <> abi_type_name2 @a @b
    go (YulJmpB @_ @a @b p)        = "Jb " <> yulB_fname p <> abi_type_name2 @a @b
    go (YulCall @_ @a @b sel)      = "C" <> showSelectorOnly sel <> abi_type_name2 @a @b
    --
    go (YulSGet @_ @a)             = "Sg" <> abi_type_name @a
    go (YulSPut @_ @a)             = "Sp" <> abi_type_name @a
    -- A 'abi_type_name variant, enclosing name with "@()".
    abi_type_name :: forall a. ABITypeable a => String
    abi_type_name = "@" ++ abiTypeCompactName @a
    abi_type_name2 :: forall a b. (ABITypeable a, ABITypeable b) => String
    abi_type_name2 = abi_type_name @a ++ abi_type_name @b
    -- TODO escape the value of x
    -- escape = show
    go_switch_case cs cdef = foldMap
      (\(i, c) -> "#" ++ i ++ "(" ++ go c ++ ")")
      (("_", cdef) : fmap (first show) cs)

-- | Morally lisp s-expression representation of 'YulCat'.
yulCatToUntypedLisp :: YulCat eff a b -> Code
yulCatToUntypedLisp cat = T.pack "(" <> go init_ind cat <> T.pack ")"
  where
    go :: Indenter -> YulCat eff a b -> Code
    go _ YulReduceType               = T.empty
    go _ YulExtendType               = T.empty
    go _ YulCoerceType               = T.empty
    go ind (YulUnsafeCoerceEffect c) = go ind c
    --
    go _ YulId                       = T.empty
    go ind (YulComp cb ac)           = gcomp ind cb ac
    --
    go ind (YulProd ab cd)           = g2 ind "prod" ab cd
    go ind YulSwap                   = ind $ T.pack "swap"
    --
    go ind (YulFork ab ac)           = g2 ind "fork" ab ac
    go ind YulExl                    = ind $ T.pack "exl"
    go ind YulExr                    = ind $ T.pack "exr"
    go ind YulDis                    = ind $ T.pack "dis"
    go ind YulDup                    = ind $ T.pack "dup"
    --
    go ind YulApply                  = ind $ T.pack "ap"
    go ind (YulCurry ab2c)           = ind $ T.pack "(curry " <> go ind ab2c <> T.pack ")"
    --
    go _ (YulEmb x)                  = T.pack ("emb {" ++ show x ++ "}")
    go _ (YulDyn _)                  = T.pack "_"
    --
    go ind (YulMapHask g)            = go ind (g (YulDyn (Const ())))
    go ind (YulSwitch cf cs cdef)    = ind $ T.pack "(switch " <> go_switch_case ind cf cs cdef <> T.pack ")"
    go ind (YulJmpU (cid, _))        = ind $ T.pack ("(jmpu " ++ cid ++ ")")
    go ind (YulJmpB p)               = ind $ T.pack ("(jmpb " ++ yulB_fname p ++ ")")
    go ind (YulCall sel)             = ind $ T.pack ("(call " ++ showSelectorOnly sel ++ ")")
    go ind YulSGet                   = ind $ T.pack "sget"
    go ind YulSPut                   = ind $ T.pack "sput"
    --
    gcomp :: forall eff' a' b' c'. Indenter -> YulCat eff' c' b' -> YulCat eff' a' c' -> Code
    gcomp ind cb ac = let c1 = go ind ac
                          c2 = go ind cb
                      in if T.null c1 || T.null c2
                         then c1 <> c2
                         else c1 <> ind (T.pack ":>.>") <> c2
    g2 :: forall eff' m n p q. Indenter -> String -> YulCat eff' m n -> YulCat eff' p q -> Code
    g2 ind op c1 c2 =
      let op' = T.pack "(" <> T.pack op
          ind' = indent ind
          s1 = go ind' c1
          s2 = go ind' c2
          result
            | T.null s1 && T.null s2 = T.empty
            | T.null s1 = ind (op' <> T.pack " id (") <> s2 <> ind (T.pack "))")
            | T.null s2 = ind (op' <> T.pack " (") <> s1 <> ind' (T.pack ") id)")
            | otherwise = ind (op' <> T.pack " (") <> s1 <> ind' (T.pack ") (") <> s2 <> ind (T.pack "))")
      in result
    go_switch_case ind cf cs cdef =
      T.pack "(" <> go ind cf <> T.pack ")" <>
      foldMap
        (\(i, c) -> ind (T.pack ":#" <> i <> T.pack " (" <> go ind c <> T.pack ")"))
        ((T.pack "_", cdef) : fmap (first (T.pack . show)) cs)
