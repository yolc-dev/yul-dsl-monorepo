{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  (P'P ,  keccak256'l
  , extendType'l
  , lfn'

  , YulCat (..)
  -- * YulCat Stringify Functions
  , YulCatObj
  , YulO1

  -- ABI type names
  , ABITypeable(..)
  , U256
  , REF
  ) where
import Prelude (undefined)
import Prelude.Linear
import Control.Category.Linear             (P, decode, encode)
import Control.Category.Constrained (Cartesian (..), Category (..), Monoidal (..), ProdObj (..))
import Data.Kind                    (Type)

data U256
data REF a



class ABITypeable a where
  abiTypeInfo :: String
  abiTypeInfo = ""

  abiFromCoreType :: a -> a
  abiFromCoreType x = x

instance ABITypeable a => ABITypeable (REF a) where

instance ABITypeable () where

instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where

instance ABITypeable U256 where




class (ABITypeable a, ABITypeable a) => YulCatObj a where
  -- | Possible breakdown of the product object of the category.

type YulO1 a = YulCatObj a
type YulO2 a b = (YulCatObj a, YulCatObj b)


instance YulCatObj ()
instance (YulCatObj a1, YulCatObj a2) => YulCatObj (a1, a2)

instance YulCatObj U256

-- REF
instance YulCatObj a => YulCatObj (REF a)


------------------------------------------------------------------------------------------------------------------------
-- The Cat
------------------------------------------------------------------------------------------------------------------------

-- | Use kind signature for the 'YulCat' to introduce the terminology in a lexical-orderly way.
type YulCat ::  Type -> Type -> Type

data YulCat a b where
  YulExtendType :: forall b. (YulO2 U256 b) => YulCat U256 b
  YulComp :: forall a b c.  YulCat c b %1-> YulCat a c %1-> YulCat a b
  YulJmpB :: forall a b. ( YulO2 a b) =>  YulCat a b



yulCatCompactShow :: YulCat a b -> String
yulCatCompactShow = go
  where
    go :: YulCat a' b' -> String
    go (YulExtendType @b) = "Te" <> abiTypeInfo @b
    go (YulComp cb ac)    = "(" <> go ac <> ");(" <> go cb <> ")"
    go YulJmpB            = "Jb "


--
instance ProdObj YulCatObj where
  prodobj = undefined
  objprod = undefined
  objunit = undefined

instance Category YulCat where
  type Obj YulCat = YulCatObj
  id  = undefined
  (∘) = YulComp

instance Monoidal YulCat where
  (×)     = undefined
  unitor  = undefined
  unitor' = undefined
  assoc   = undefined
  assoc'  = undefined
  swap    = undefined


--

lfn' :: forall b xs.
  ( YulO2 U256 (REF b)
  , '[U256] ~ xs   -- crash stops after removing this line
  ) =>
  (forall r. YulO1 r => P'P r (U256 ) ⊸ P'P r (REF b)) ->
  String
lfn' f = yulCatCompactShow (decode f)


type P'P =  P YulCat



------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a r.
  (YulO1 a, YulO1 r) =>
  P'P r U256 ⊸ P'P r a
extendType'l = encode YulExtendType

keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r U256
keccak256'l = encode YulJmpB
