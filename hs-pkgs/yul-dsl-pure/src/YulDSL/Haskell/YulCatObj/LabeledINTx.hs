{-# LANGUAGE AllowAmbiguousTypes #-}
module YulDSL.Haskell.YulCatObj.LabeledINTx where
-- base
import Data.List                (unfoldr)
--
import YulDSL.Core
--
import Control.PatternMatchable


class ValidINTn n => IsLabledINTx l n | l -> n where
  minLabel :: l

  succLabel :: l -> (INTx False n, Maybe l)

  fromLabelToINTx :: l -> INTx False n
  fromLabelToINTx = fst . succLabel

  allINTxLabels :: [l]
  allINTxLabels = unfoldr ((\l -> (l, snd (succLabel l))) <$>) (Just minLabel)

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

instance (YulO1 r, IsLabledINTx l n) =>
         PatternMatchable (YulCat eff r) (LabledINTx l n) l YulCatObj Many where
  match pats f =
    YulApply <.<
      yulSwitch
        (\pats' -> pats' >.> YulReduceType >.> yulSafeCast)
        ((\l -> (withValidINTn @n (intxUpCast (fromLabelToINTx l)), const (f l))) <$> allINTxLabels)
        (const yulRevert)
      `YulFork`
      pats
  couldBe l = YulEmb (fromLabelToINTx l) >.> YulExtendType
