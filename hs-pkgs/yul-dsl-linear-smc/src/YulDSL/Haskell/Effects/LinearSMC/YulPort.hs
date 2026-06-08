{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  (P'P ,  keccak256'l
  , extendType'l
  , lfn'

  , YulCat (..)
  -- * YulCat Stringify Functions
  , YulCatObj
  , YulO1, YulO2, YulO3
  ) where
import Prelude.Linear
import Control.Category.Linear             (P, decode, encode)
import YulDSL.Core
import Prelude (undefined)
import Control.Category.Constrained (Cartesian (..), Category (..), Monoidal (..), ProdObj (..))
import Data.Kind                    (Type)




-- | All objects in the yul category is simply a 'YulCatObj'.
class (ABITypeable a, ABITypeCodec a) => YulCatObj a where
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
instance ValidINTx s n => YulCatObj (INTx s n)
instance YulCatObj ADDR
instance ValidINTn n => YulCatObj (BYTESn n)

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
    go (YulExtendType  @a @b)    = "Te" <> abiTypeCompactName @b
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
  ( YulO2 (NP '[ADDR]) b
  , '[ADDR] ~ xs   -- crash stops after removing this line
  ) =>
  (forall r. YulO1 r => P'P r (NP '[ADDR]) ⊸ P'P r b) ->
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
