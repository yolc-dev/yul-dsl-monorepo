{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LinearTypes            #-}
{-# LANGUAGE TypeFamilies           #-}
{-|

Copyright   : (c) 2023-2024 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : zhicheng.miao@gmail.com
Stability   : experimental


= Description

[Yul](https://docs.soliditylang.org/en/latest/yul.html) is an intermediate language that is part of the [solidity
compiler](https://docs.soliditylang.org/en/latest/). It is by-design aspiring to be compiled to bytecode for
different backends, while at the moment it is for [Ethereum Virtual
Machine](https://ethereum.org/en/developers/docs/evm/) (EVM).

This module provides an "Embedded (in Haskell) Domain Specific Language" (eDSL) for programming in Yul, called
'YulCat'.


Further more, the 'YulCat' is instantiated as a "Symmetric Monoidal Category" (SMC). Being a SMC enables the possibility
for compiling linearly-typed functions in Haskell directly to the 'YulCat', that is believed to greatly enhance the
ergonomics of programming in 'YulCat'.

YulCat is designed to be a category. The objects in this category are instances of @ABIType@.

The classification objects in the YulCat symmetrical monoidal category:

  * 'YulObj'
  * 'YulVal'
  * 'YulNum'

-}

module YulDSL.Core.YulCat
  ( YulObj (yul_prod_objs), YulO1, YulO2, YulO3, YulO4, YulO5
  , YulNum
  , Pure (MkPure)
  , YulCat (..), AnyYulCat (..), (>.>), (<.<)
  , MPOrd (..), IfThenElse (..)
  , digestYulCat,
  ) where

-- base
import           Data.Char             (ord)
import           GHC.Integer           (xorInteger)
import           Text.Printf           (printf)
-- constraints
import           Data.Constraint       (Dict (Dict))
-- bytestring
import qualified Data.ByteString.Char8 as B
-- eth-abi
import           Ethereum.ContractABI


{- * Objects in the yul category -}

-- | All objects in the yul category is simply a 'YulObj'.
class (ABITypeable a, ABITypeCodec a, Show a) => YulObj a where
  -- | Possible breakdown of the product object type.
  yul_prod_objs :: forall b c. a ~ (b, c) => Dict (YulObj b, YulObj c)
  yul_prod_objs = error "yul_prod_objs should only be implemented by the product of YulObj"

{- ** Enumerate the objects for both core and extended ABI types -}

instance YulObj ADDR
instance YulObj BOOL
instance (KnownBool s, ValidINTn n) => YulObj (INTx s n)
instance YulObj (NP '[])
instance (YulObj x, YulObj (NP xs)) => YulObj (NP (x:xs))
instance YulObj ()
instance (YulObj a1, YulObj a2) => YulObj (a1, a2) where yul_prod_objs = Dict

{- ** Convenient aliases for declaring yul objects -}

type YulO1 a = YulObj a
type YulO2 a b = (YulObj a, YulObj b)
type YulO3 a b c = (YulObj a, YulObj b, YulObj c)
type YulO4 a b c d = (YulObj a, YulObj b, YulObj c, YulObj d)
type YulO5 a b c d e = (YulObj a, YulObj b, YulObj c, YulObj d, YulObj e)

{- ** Number types -}

-- | Number-type objects in the category.
class (Num a, YulObj a) => YulNum a

-- | Integer types.
instance (KnownBool s, ValidINTn n) => YulNum (INTx s n)

-- | Data kinds for pure morphisms in the yul category.
data Pure = MkPure

{- * The Cat -}

-- | A GADT-style DSL of Yul that constructs morphisms between objects (YulObj) of the "Yul Category".
--
--  Note: - The inhabitants of this are actually morphisms of the Yul category. "Cat" is just a nice sounding moniker,
--  while the actual category is "Yul Category".
data YulCat (eff :: k) a b where
  -- Type-level Operations (Zero Runtime Cost)
  -- | Convert between coercible Yul objects.
  YulCoerce :: forall eff a b. (YulO2 a b, ABITypeCoercible a b) => YulCat eff a b
  -- | Split the head and tail of a n-ary product where n >= 1.
  YulSplit :: forall eff as. YulO1 (NP as) => YulCat eff (NP as) (Head as, NP (Tail as))

  -- SMC Primitives
  --  Category
  YulId   :: forall eff a.     YulO2 a a   => YulCat eff a a
  YulComp :: forall eff a b c. YulO3 a b c => YulCat eff c b %1 -> YulCat eff a c %1 -> YulCat eff a b
  --  Monoidal
  YulProd :: forall eff a b c d. YulO4 a b c d => YulCat eff a b %1 -> YulCat eff c d %1 -> YulCat eff (a, c) (b, d)
  YulSwap :: forall eff a b.     YulO2 a b     => YulCat eff (a, b) (b, a)
  --  Cartesian
  YulFork :: forall eff a b c. YulO3 a b c => YulCat eff a b %1 -> YulCat eff a c %1 -> YulCat eff a (b, c)
  YulExl  :: forall eff a b.   YulO2 a b   => YulCat eff (a, b) a
  YulExr  :: forall eff a b.   YulO2 a b   => YulCat eff (a, b) b
  YulDis  :: forall eff a.     YulO1 a     => YulCat eff a ()
  YulDup  :: forall eff a.     YulO1 a     => YulCat eff a (a, a)

  -- Control Flow Primitives
  --
  -- | Call a yul internal function by reference its id.
  YulJump  :: forall eff a b. YulO2 a b => String -> YulCat eff a b %1 -> YulCat eff a b
  -- | Call a external function.
  -- YulCall  :: forall a b r. YulO3 a b r => YulCat r (FUNC a b) %1 -> YulCat a b
  -- | If-then-else.
  YulITE   :: forall eff a. YulO1 a => YulCat eff (BOOL, (a, a)) a

  -- YulVal Primitives
  --
  -- | Embed a constant value.
  YulEmbed :: forall eff a r. YulO2 a r => a -> YulCat eff r a
  -- * Boolean Operations
  YulNot :: YulCat eff BOOL BOOL
  YulAnd :: YulCat eff (BOOL, BOOL) BOOL
  YulOr  :: YulCat eff (BOOL, BOOL) BOOL
  -- * Num Types
  YulNumAdd :: forall eff a. YulNum a => YulCat eff (a, a) a
  YulNumMul :: forall eff a. YulNum a => YulCat eff (a, a) a
  YulNumAbs :: forall eff a. YulNum a => YulCat eff a a
  YulNumSig :: forall eff a. YulNum a => YulCat eff a a
  YulNumNeg :: forall eff a. YulNum a => YulCat eff a a
  -- * Number comparison with a three-way boolean-switches (LT, EQ, GT).
  YulNumCmp :: forall eff a. YulNum a => (BOOL, BOOL, BOOL) -> YulCat eff (a, a) BOOL

  -- * Contract ABI Serialization
  -- YulAbiEnc :: YulObj a => YulCat a BYTES
  -- YulAbiDec :: YulObj a => YulCat BYTES (Maybe a)

  -- Storage Primitives
  --
  YulSGet :: forall eff a. (YulO1 a, ABIWordValue a) => YulCat eff ADDR a
  YulSPut :: forall eff a. (YulO1 a, ABIWordValue a) => YulCat eff (ADDR, a) ()

-- | Existential wrapper of the 'YulCat'.
data AnyYulCat = forall eff a b. YulO2 a b => MkAnyYulCat (YulCat eff a b)

-- | Left to right composition of 'YulCat'.
(>.>) :: forall eff a b c. YulO3 a b c => YulCat eff a b %1 -> YulCat eff b c %1 -> YulCat eff a c
m >.> n = n `YulComp` m

-- | Right-to-left composition of 'YulCat'.
(<.<) :: forall eff a b c. YulO3 a b c => YulCat eff b c %1 -> YulCat eff a b %1 -> YulCat eff a c
(<.<) = YulComp

-- Same precedence as (>>>) (<<<);
-- see https://hackage.haskell.org/package/base-4.20.0.1/docs/Control-Category.html
infixr 1 >.>, <.<

-- | It's not as scary as it sounds. It produces a fingerprint for the morphism.
digestYulCat :: YulCat eff a b -> String
digestYulCat = printf "%x" . digest_c8 . B.pack . show
  where c8 _ []     = 0
        c8 n [a]    = (2 ^ n) * toInteger(ord a)
        c8 n (a:as) =  (2 ^ n) * toInteger(ord a) + c8 (n + 8) as
        digest_c8 bs = go_digest_c8 (B.splitAt 8 bs)
        go_digest_c8 (b, bs') = c8 (0 :: Integer) (B.unpack b) `xorInteger`
                                if B.length bs' == 0 then 0 else digest_c8 bs'

{- * NP Helpers -}

{- ** UncurryingNP instances -}

-- (x)
instance forall x r eff.
         ( LiftFunction x (YulCat eff r) (YulCat eff r) Many ~ YulCat eff r x
         , YulO2 x r
         ) => UncurryingNP (x) '[] x (YulCat eff r) (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  uncurryingNP x _ = x

-- (x -> ...xs -> b)
instance forall x xs b g r eff.
         ( YulO5 x (NP xs) b (NP (x:xs)) r
         , UncurryNP'Fst g ~ xs
         , UncurryNP'Snd g ~ b
         , UncurryingNP g xs b (YulCat eff r) (YulCat eff r) (YulCat eff r) (YulCat eff r) Many
         ) => UncurryingNP (x -> g) (x:xs) b (YulCat eff r) (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  uncurryingNP f xxs = uncurryingNP @g @xs @b @(YulCat eff r) @(YulCat eff r) @(YulCat eff r) @(YulCat eff r) @Many
                       (f x) xs
    where xxs' = xxs >.> YulSplit
          x   = xxs' >.> YulExl
          xs  = xxs' >.> YulExr

{- ** CurryingNP instances -}

instance forall b r eff.
         ( YulO2 b r
         , LiftFunction b (YulCat eff r) (YulCat eff r) Many ~ YulCat eff r b
         ) => CurryingNP '[] b (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  curryingNP cb = cb (YulDis >.> YulCoerce)

instance forall x xs b r eff.
         ( YulO5 x (NP xs) b (NP (x:xs)) r
         , CurryingNP xs b (YulCat eff r) (YulCat eff r) (YulCat eff r) Many
         ) => CurryingNP (x:xs) b (YulCat eff r) (YulCat eff r) (YulCat eff r) Many where
  curryingNP cb x = curryingNP @xs @b @(YulCat eff r) @(YulCat eff r)
                    (\xs -> cb (YulFork x xs >.> YulCoerce))

------------------------------------------------------------------------------------------------------------------------
-- Show Instance For Unique String Representation Of Cats
------------------------------------------------------------------------------------------------------------------------

-- | Bespoke show instance for YulCat.
--
--   Note:
--   * It is deliberately done so for compactness of the string representation of the 'YulCat'.
--   * It is meant also for strong equality checking of 'YulCat' used in yul object building.
instance Show (YulCat eff a b) where
  show (YulCoerce)         = "coerce" <> abi_type_name @a <> abi_type_name @b
  show (YulId)             = "id"
  show (YulSplit)          = "▿" <> abi_type_name @a
  show (YulComp cb ac)     = "(" <> show ac <> ");(" <> show cb <> ")"
  show (YulProd ab cd)     = "×(" <> show ab <> ")(" <> show cd <> ")"
  show (YulSwap)           = "σ" <> abi_type_name @a <> abi_type_name @b
  show (YulFork ab ac)     = "▵(" <> show ab <> ")(" <> show ac <> ")"
  show (YulExl)            = "π₁" <> abi_type_name @a
  show (YulExr)            = "π₂" <> abi_type_name @a
  show (YulDis)            = "ε" <> abi_type_name @a
  show (YulDup)            = "δ" <> abi_type_name @a
  show (YulEmbed x)        = "{" <> show x <>  "}"
  show (YulJump cid _)     = "jump " <> cid
  -- show (YulCall c)         = "call " <> show c
  show (YulITE)            = "?" <> abi_type_name @a
  show (YulNot)            = "not"
  show (YulAnd)            = "and"
  show (YulOr)             = "or"
  show (YulNumAdd)         = "add" <> abi_type_name @a
  show (YulNumMul)         = "mul" <> abi_type_name @a
  show (YulNumSig)         = "sig" <> abi_type_name @a
  show (YulNumAbs)         = "abs" <> abi_type_name @a
  show (YulNumNeg)         = "neg" <> abi_type_name @a
  show (YulNumCmp (i,j,k)) = "cmp" <> s i <> s j <> s k where s x = if x == true then "t" else "f"
  show (YulSGet)           = "sget" <> abi_type_name @a
  show (YulSPut)           = "sput" <> abi_type_name @a
--  show _                   = error "Show YulCat TODO"

instance Show AnyYulCat where
  show (MkAnyYulCat c) = show c

------------------------------------------------------------------------------------------------------------------------
-- Useful Type Classes For Custom Prelude
------------------------------------------------------------------------------------------------------------------------

instance (YulO2 a r, YulNum a) => Num (YulCat eff r a) where
  a + b = YulNumAdd <.< YulProd a b <.< YulDup
  a * b = YulNumMul <.< YulProd a b <.< YulDup
  abs = YulComp YulNumAbs
  signum = YulComp YulNumSig
  fromInteger = YulEmbed . fromInteger
  negate a = YulNumNeg <.< a

-- | Multi-parameter ordering typeclass where boolean type is @b@
class MPOrd a b | a -> b where
  ( <?) :: forall w. a %w -> a %w -> b
  (<=?) :: forall w. a %w -> a %w -> b
  ( >?) :: forall w. a %w -> a %w -> b
  (>=?) :: forall w. a %w -> a %w -> b
  (==?) :: forall w. a %w -> a %w -> b
  (/=?) :: forall w. a %w -> a %w -> b
  infixr 4 <?, <=?, >?, >=?, ==?, /=?

instance (YulO2 a r, YulNum a) => MPOrd (YulCat eff r a) (YulCat eff r BOOL) where
  a  <? b = YulNumCmp (true , false, false) <.< YulProd a b <.< YulDup
  a <=? b = YulNumCmp (true , true , false) <.< YulProd a b <.< YulDup
  a  >? b = YulNumCmp (false, false, true ) <.< YulProd a b <.< YulDup
  a >=? b = YulNumCmp (false, true , true ) <.< YulProd a b <.< YulDup
  a ==? b = YulNumCmp (false, true , false) <.< YulProd a b <.< YulDup
  a /=? b = YulNumCmp (true , false, true ) <.< YulProd a b <.< YulDup

-- | IfThenElse for enabling rebindable syntax.
class IfThenElse a b where
  ifThenElse :: forall w. a %w -> b %w -> b %w -> b

instance YulO2 a r => IfThenElse (YulCat eff r BOOL) (YulCat eff r a) where
  ifThenElse c a b = YulITE <.< YulFork c (YulFork a b)

{- INTERNAL FUNCTIONs -}

-- | A 'abi_type_name variant, enclosing name with "@()".
abi_type_name :: forall a. ABITypeable a => String
abi_type_name = "@" ++ abiTypeCompactName @a
