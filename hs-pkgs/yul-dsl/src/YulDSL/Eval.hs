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


newtype EvalData = MkEvalData { store_map :: M.Map B32 WORD
                              }
                 deriving Show

type EvalState = State EvalData

initEvalState :: EvalData
initEvalState = MkEvalData { store_map = M.empty
                           }

evalYulCat' :: (HasCallStack, YulO2 a b) => YulCat eff a b -> a -> EvalState b
-- type-level conversions
evalYulCat' YulReduceType a = pure $ fromJust . abiDecode . abiEncode $ a
evalYulCat' YulExtendType a = pure $ fromJust . abiDecode . abiEncode $ a
evalYulCat' YulCoerceType a = pure $ fromJust . abiDecode . abiEncode $ a
-- category
evalYulCat' YulId     a = pure a
evalYulCat' (YulComp n m) a = evalYulCat' m a >>= evalYulCat' n
-- monoidal category
evalYulCat' (YulProd m n) (a, b) = do
  a' <- evalYulCat' m a
  b' <- evalYulCat' n b
  pure (a', b')
evalYulCat' YulSwap (a, b) = pure (b, a)
-- cartesian category
evalYulCat' (YulFork m n) a = do
  b <- evalYulCat' m a
  c <- evalYulCat' n a
  pure (b, c)
evalYulCat' YulExl  (a, _)  = pure a
evalYulCat' YulExr  (_, b)  = pure b
evalYulCat' YulDis _ = pure () -- FIXME: there may be semantic difference with YulGen, a is always evaluated even if eff may not affect the world.
evalYulCat' YulDup a = pure (a, a)
-- control flow
evalYulCat' (YulJmpU (_, f)) a = evalYulCat' f a
evalYulCat' (YulJmpB p) a = pure (yulB_eval p a)
evalYulCat' (YulCall _) _    = error "YulCall not supported" -- FIXME
evalYulCat' (YulITE ct cf) (BOOL t, a) = if t then evalYulCat' ct a else evalYulCat' cf a
-- value primitives
evalYulCat' (YulEmb b)  _ = pure b
evalYulCat' YulSGet r = gets $ \s -> fromJust (fromWord =<< M.lookup r (store_map s))
evalYulCat' YulSPut (r, a) = modify' $ \s -> s { store_map = M.insert r (toWord a) (store_map s) }
evalYulCat' (YulUnsafeCoerceEffect c) a = evalYulCat' c a

evalYulCat :: YulO2 a b => YulCat eff a b -> a -> b
evalYulCat s a = evalState (evalYulCat' s a) initEvalState

evalFn :: forall fn efc xs b.
          ( YulO2 (NP xs) b
          , KnownNamedYulCat fn efc (NP xs) b
          )
       => fn -> NP xs -> b
evalFn fn = withKnownNamedYulCat fn (evalYulCat . snd)
