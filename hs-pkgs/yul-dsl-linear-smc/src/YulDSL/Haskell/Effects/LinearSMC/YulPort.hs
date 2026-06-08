{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  (P'P ,  keccak256'l
  , extendType'l
  , lfn'

  , YulCat (..)
  -- * YulCat Stringify Functions
  , YulCatObj
  , YulO1, YulO2, YulO3

  , Nat
  -- ABI type names
  , ABITypeable(..)
  , ADDR
  , U256
  , B32
  , module Data.SimpleNP
  ,  module Data.TupleN
  , REF
  , ValidSlot
  ) where
import Prelude ()
import Prelude.Linear
import Control.Category.Linear             (P, decode, encode)
import Ethereum.ContractABI.ABICoreType
import Prelude (undefined)
import Control.Category.Constrained (Cartesian (..), Category (..), Monoidal (..), ProdObj (..))
import Data.Kind                    (Type)

-- base
import GHC.TypeLits
    ( Nat
    , type (<=)
    )
-- template-haskell
-- constraints
--

-- base
import Data.SimpleNP
import Data.Proxy                        (Proxy (Proxy))
import GHC.TypeLits                      (type (+), type (<=), type (<=?))
-- base
import Data.TupleN
--

-- base
import GHC.TypeLits
--


-- | A storage or memory reference to type @a@ at the solidity conventional "(slot, offset)".
newtype REF a = REF Integer

instance Show (REF a) where show (REF x) = show x

-- | Each slot uses 32 bytes
type ValidSlot n = (KnownNat n, n <= (2 ^ 248))

instance ABITypeable a => ABITypeable (REF a) where
  type instance ABITypeDerivedOf (REF a) = B32

-- ^ ABI typeable unit.
instance ABITypeable () where
  type instance ABITypeDerivedOf () = NP '[]

-- ^ ABI typeable for solo tuple.
instance ABITypeable a => ABITypeable (Solo a) where
  type instance ABITypeDerivedOf (Solo a) = NP '[a]

-- | ABI typeable tuple.
instance (ABITypeable a1, ABITypeable a2) => ABITypeable (a1, a2) where
  type instance ABITypeDerivedOf (a1, a2) = NP '[a1, a2]

-- cereal


class ABITypeable a where
  type ABITypeDerivedOf a

  abiTypeInfo :: String
  abiFromCoreType :: a -> a
  abiFromCoreType x = x

data ADDR

instance ABITypeable ADDR where
  type instance ABITypeDerivedOf ADDR = ADDR
  abiTypeInfo = "a"

-- eth-abi


-- | ABI integer value types, where @s@ is for signess and @n@ is byte-size of the value.
data U256



instance ABITypeable U256 where
  type instance ABITypeDerivedOf U256 = U256
  abiTypeInfo = "i"


data B32

instance ABITypeable B32 where
  type instance ABITypeDerivedOf B32 = B32
  abiTypeInfo = "b"

-- cereal
--
--


instance ABITypeable (NP '[]) where
  type instance ABITypeDerivedOf (NP '[]) = NP '[]
  abiTypeInfo = []

instance ( ABITypeable x, ABITypeable (NP xs)
         ) => ABITypeable (NP (x : xs)) where
  type instance ABITypeDerivedOf (NP (x : xs)) = NP (x : xs)
  abiTypeInfo = abiTypeInfo @x <> abiTypeInfo @(NP xs)


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
instance (YulCatObj x, YulCatObj (NP xs)) => YulCatObj (NP (x:xs))

-- TupleN (3..15)
instance YulCatObj ()
instance (YulCatObj a1, YulCatObj a2) => YulCatObj (a1, a2)

-- Value Types
instance YulCatObj U256
instance YulCatObj ADDR
instance YulCatObj B32

-- REF
instance YulCatObj a => YulCatObj (REF a)


------------------------------------------------------------------------------------------------------------------------
-- The Cat
------------------------------------------------------------------------------------------------------------------------

-- | Use kind signature for the 'YulCat' to introduce the terminology in a lexical-orderly way.
type YulCat ::  Type -> Type -> Type

data YulCat a b where
  YulExtendType :: forall a b. (YulO2 (ABITypeDerivedOf b) b) => YulCat (ABITypeDerivedOf b) b
  YulComp :: forall a b c.  YulCat c b %1-> YulCat a c %1-> YulCat a b
  YulJmpB :: forall a b. ( YulO2 a b) =>  YulCat a b



yulCatCompactShow :: YulCat a b -> String
yulCatCompactShow = go
  where
    go :: YulCat a' b' -> String
    go (YulExtendType  @a @b)    = "Te" <> abiTypeInfo @b
    go (YulComp cb ac)             = "(" <> go ac <> ");(" <> go cb <> ")"
    go (YulJmpB  @a @b )        = "Jb "


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
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'P r (ABITypeDerivedOf a) ⊸ P'P r a
extendType'l = encode YulExtendType

keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r B32
keccak256'l = encode YulJmpB
