{-|

Copyright   : (c) 2023-2024 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Description

This module provides an evaluator for YulDSL.

-}

module YulDSL.Eval where
-- base
import Data.Function            ((&))
import Data.Maybe               (fromJust)
import GHC.Stack                (HasCallStack)
-- containers
import Data.Map                 qualified as M
-- mtl
import Control.Monad.State.Lazy (State, evalState, gets, modify')
-- eth-abi
import Ethereum.ContractABI
--
import YulDSL.Core.YulBuiltIn   (yulB_eval)
import YulDSL.Core.YulCat
import YulDSL.Core.YulCatObj


-- Data type for the state monad.
newtype EvalData = MkEvalData
  { store_map :: M.Map B32 WORD
  }
  deriving Show

-- Initial evaluation state.
initEvalState :: EvalData
initEvalState = MkEvalData
  { store_map = M.empty
  }

-- | Evaluate yul category morphism with a value from Hask.
evalYulCat :: YulO2 a b => YulCat eff a b -> a -> b
evalYulCat s_ a_ = evalState (go s_ a_) initEvalState
  where
    go :: (HasCallStack, YulO2 a b) => YulCat eff a b -> a -> State EvalData b
    -- type-level conversions
    go YulReduceType a = pure $ fromJust . abiDecode . abiEncode $ a
    go YulExtendType a = pure $ fromJust . abiDecode . abiEncode $ a
    go YulCoerceType a = pure $ fromJust . abiDecode . abiEncode $ a
    go (YulUnsafeCoerceEffect c) a = go c a
    -- category
    go YulId  a = pure a
    go (YulComp n m) a = go m a >>= go n
    -- monoidal category
    go (YulProd m n) (a, b) = do
      a' <- go m a
      b' <- go n b
      pure (a', b')
    go YulSwap (a, b) = pure (b, a)
    -- cartesian category
    go (YulFork m n) a = do
      b <- go m a
      c <- go n a
      pure (b, c)
    go YulExl  (a, _) = pure a
    go YulExr  (_, b) = pure b
    go YulDis _ = pure () -- FIXME: there may be semantic difference with YulGen when it comes effect order.
    go YulDup a = pure (a, a)
    -- Cartesian Closed
    go YulApply (f, a) = go (f a) a
    go (YulCurry ab2c) a =  pure (\b -> YulEmb (a, b) >.> ab2c)
    -- co-cartesian category
    go (YulEmb b) _ = pure b
    -- control flow
    go (YulITE ct cf) (BOOL t, a) = if t then go ct a else go cf a
    go (YulSwitch cs cdef) a = pure (\i -> filter ((i ==) . fst) cs & \case
                                        [] ->  YulEmb a >.> cdef   -- default case
                                        [(_, c)] -> YulEmb a >.> c -- matching case
                                        _ -> error "too many switch cases"
                                    )
    go (YulJmpU (_, f)) a = go f a
    go (YulJmpB p) a = pure (yulB_eval p a)
    go (YulCall _) _    = error "YulCall not supported" -- FIXME
    -- storage primitives
    go YulSGet r = gets $ \s -> fromJust (fromWord =<< M.lookup r (store_map s))
    go YulSPut (r, a) = modify' $ \s -> s { store_map = M.insert r (toWord a) (store_map s) }

-- | Evaluate a known named yul category morphism with NP-typed inputs.
evalFn :: forall fn efc xs b.
  ( YulO2 (NP xs) b
  , KnownNamedYulCat fn efc (NP xs) b
  ) =>
  fn -> NP xs -> b
evalFn fn = withKnownNamedYulCat fn (evalYulCat . snd)
