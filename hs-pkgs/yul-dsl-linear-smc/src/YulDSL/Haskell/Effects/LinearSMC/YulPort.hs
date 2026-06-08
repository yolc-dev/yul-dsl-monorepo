{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}
module YulDSL.Haskell.Effects.LinearSMC.YulPort
  (P'P ,  encodeP'x, decodeP'x, keccak256'l
  , extendType'l
  , lfn'
  ) where
import Prelude.Linear
import Control.Category.Linear             (P, decode, encode)

import YulDSL.Core

import YulDSL.Core.YulCat


import Prelude (undefined)
-- base
-- constraints
import Data.Constraint              (Dict (Dict))
-- linear-smc
import Control.Category.Constrained (Cartesian (..), Category (..), Monoidal (..), ProdObj (..))
--
import YulDSL.Core.YulCat           (YulCat (..), YulCatObj )

-- | Instance for linear-smc 'ProdObj' for the objects in the category.
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
lfn' f = yulCatCompactShow (decodeP'x f)


type P'P =  P YulCat


encodeP'x :: forall a b r.
  YulO3 r a b =>
  YulCat a b ->
  (P'P r a ⊸ P'P r b)
encodeP'x = encode

decodeP'x :: forall  b.
  YulO2 (NP '[ADDR]) b =>
  (forall r. YulO1 r => P'P r (NP '[ADDR]) ⊸ P'P r b) ->
  YulCat (NP '[ADDR]) b
decodeP'x = decode

------------------------------------------------------------------------------------------------------------------------

extendType'l :: forall a r.
  (YulO3 a (ABITypeDerivedOf a) r) =>
  P'P r (ABITypeDerivedOf a) ⊸ P'P r a
extendType'l = encodeP'x YulExtendType

keccak256'l :: forall a r. YulO2 r a => P'P r a ⊸ P'P r B32
keccak256'l = encodeP'x YulJmpB

