{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  (P'P ,  keccak256'l
  , extendType'l
  , lfn'

  , YulCat (..)
  -- * YulCat Stringify Functions
  , YulCatObj
  , YulO1, YulO2, YulO3

  -- ABI type names
  , ABITypeable(..)
  , ADDR
  , U256
  , B32
  , REF
  , NP
  ) where
import Prelude (undefined)
import Prelude.Linear
import Control.Category.Linear             (P, decode, encode)
import Control.Category.Constrained (Cartesian (..), Category (..), Monoidal (..), ProdObj (..))
import Data.Kind                    (Type)

-- base
-- template-haskell
-- constraints
--

-- base
import Data.SimpleNP
import Data.Proxy                        (Proxy (Proxy))
-- base
import Data.TupleN
--

-- base
import GHC.TypeLits
--


-- | A storage or memory reference to type @a@ at the solidity conventional "(slot, offset)".
newtype REF a = REF Integer



instance ABITypeable a => ABITypeable (REF a) where

-- ^ ABI typeable unit.
instance ABITypeable () where

-- ^ ABI typeable for solo tuple.
instance ABITypeable a => ABITypeable (Solo a) where

-- | ABI typeable tuple.
instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where

-- cereal


class ABITypeable a where
  abiTypeInfo :: String
  abiTypeInfo = ""

  abiFromCoreType :: a -> a
  abiFromCoreType x = x

data ADDR

instance ABITypeable ADDR where
  abiTypeInfo = "a"

-- eth-abi


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
data U256



instance ABITypeable U256 where
  abiTypeInfo = "i"


type B32 = U256

-- cereal
--
--


instance ABITypeable (NP '[]) where
  abiTypeInfo = []

instance ( ABITypeable x) => ABITypeable (NP (x : '[])) where
  abiTypeInfo = abiTypeInfo @x


-- | All objects in the yul category is simply a 'YulCatObj'.
class (ABITypeable a, ABITypeable a) => YulCatObj a where
  -- | Possible breakdown of the product object of the category.

type YulO1 a = YulCatObj a
type YulO2 a b = (YulCatObj a, YulO1 b)
type YulO3 a b c = (YulCatObj a, YulO2 b c)

--
-- Enumerate known YulCat objects:
--

-- NP
instance YulCatObj (NP '[])
instance (YulCatObj x) => YulCatObj (NP '[x])

-- TupleN (3..15)
instance YulCatObj ()
instance (YulCatObj a1, YulCatObj a2) => YulCatObj (a1, a2)

-- Value Types
instance YulCatObj U256
instance YulCatObj ADDR

-- REF
instance YulCatObj a => YulCatObj (REF a)


------------------------------------------------------------------------------------------------------------------------
-- The Cat
------------------------------------------------------------------------------------------------------------------------

-- | Use kind signature for the 'YulCat' to introduce the terminology in a lexical-orderly way.
type YulCat ::  Type -> Type -> Type

data YulCat a b where
  YulExtendType :: forall b. (YulO2 B32 b) => YulCat B32 b
  YulComp :: forall a b c.  YulCat c b %1-> YulCat a c %1-> YulCat a b
  YulJmpB :: forall a b. ( YulO2 a b) =>  YulCat a b



yulCatCompactShow :: YulCat a b -> String
yulCatCompactShow = go
  where
    go :: YulCat a' b' -> String
    go (YulExtendType   @b)    = "Te" <> abiTypeInfo @b
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    go (YulJmpB  )        = "Jb "


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
  ( YulO2 (NP '[ADDR]) (REF b)
  , '[ADDR] ~ xs   -- crash stops after removing this line
  ) =>
  (forall r. YulO1 r => P'P r (NP '[ADDR]) ⊸ P'P r (REF b)) ->
  String
lfn' f = yulCatCompactShow (decode f)


type P'P =  P YulCat



------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a r.
  (YulO3 a B32 r) =>
  P'P r B32 ⊸ P'P r a
extendType'l = encode YulExtendType

keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r B32
keccak256'l = encode YulJmpB
