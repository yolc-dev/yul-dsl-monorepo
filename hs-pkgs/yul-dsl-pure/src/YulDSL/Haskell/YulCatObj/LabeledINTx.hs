{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
module YulDSL.Haskell.YulCatObj.LabeledINTx where
-- base
import GHC.TypeLits             (type (<=))
--
import YulDSL.Core
--
import Control.PatternMatchable


class ValidINTn n => IsLabledINTx l n | l -> n where
  fromLabelToINTx :: l -> INTx False n
  allINTxLabels :: [l]

data LabledINTx l n = IsLabledINTx l n => MkLabledINTx { unLableINTx :: INTx False n }

type LabeledU256 l = LabledINTx l 32

instance IsLabledINTx l n => ABITypeable (LabledINTx l n) where
  type instance ABITypeDerivedOf (LabledINTx l n) = INTx False n
  abiDefault = MkLabledINTx abiDefault
  abiToCoreType (MkLabledINTx x) = x
  abiFromCoreType = MkLabledINTx

instance IsLabledINTx l n => ABITypeCodec (LabledINTx l n)
instance (Show l, IsLabledINTx l n) => Show (LabledINTx l n) where show = show . unLableINTx
instance (Show l, IsLabledINTx l n) => YulCatObj (LabledINTx l n)

instance (YulO1 r, IsLabledINTx l n, n <= 32) =>
         PatternMatchable (YulCat eff r) (LabledINTx l n) l YulCatObj Many where
  match pats f =
    YulApply <.<
      yulSwitch
        (\pats' -> pats' >.> YulReduceType >.> yulSafeCast)
        ((\l -> (intxUpCast (fromLabelToINTx l), const (f l))) <$> allINTxLabels)
        (const yulRevert)
      `YulFork`
      pats
  couldBe l = YulEmb (fromLabelToINTx l) >.> YulExtendType
