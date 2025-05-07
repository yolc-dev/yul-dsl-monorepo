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
import Control.Monad            (void)
import Data.Function            ((&))
import Data.Functor             ((<&>))
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
evalYulCat s_ a_ = evalState (go s_ (pure a_)) initEvalState
  where
    go :: (HasCallStack, YulO2 a b) => YulCat eff a b -> State EvalData a -> State EvalData b
    -- type-level conversions
    go YulReduceType ma = ma <&> (fromJust . abiDecode . abiEncode)
    go YulExtendType ma = ma <&> (fromJust . abiDecode . abiEncode)
    go YulCoerceType ma = ma <&> (fromJust . abiDecode . abiEncode)
    go (YulUnsafeCoerceEffect c) ma = go c ma
    -- category
    go YulId  ma        = ma
    go (YulComp n m) ma = go n (go m ma)
    -- -- monoidal category
    go (YulProd m n) mab = do
      (a, b) <- mab
      a' <- go m (pure a)
      b' <- go n (pure b)
      pure (a', b')
    go YulSwap mab = mab >>= \(a, b) -> pure (b, a)
    -- -- cartesian category
    go (YulFork m n) ma = do
      b <- go m ma
      c <- go n ma
      pure (b, c)
    go YulExl mab = mab >>= \(a, _) -> pure a
    go YulExr mab = mab >>= \(_, b) -> pure b
    go YulDis ma  = void ma
    go YulDup ma  = ma >>= \a -> pure (a, a)
    -- -- Cartesian Closed
    go YulApply mfa = mfa >>= \(a2b, a) -> go (a2b a) (pure a)
    go (YulCurry ab2c) ma = ma >>= \a -> pure \b -> YulEmb a `YulFork` YulEmb b >.> ab2c
    -- -- co-cartesian category: create "new" objects
    go YulAbsurd  _ = error "absurd"
    go (YulEmb b) ma = ma >> pure b
    go (YulMapHask g) mr = mr >>= \r -> pure \a -> YulEmb r >.> g (YulEmb a)
    -- -- control flow
    go (YulITE ct cf) mba = mba >>= \(BOOL t, a) -> if t then go ct (pure a) else go cf (pure a)
    go (YulSwitch cf cs cdef) a = do
      cid <- go cf a
      filter ((cid ==) . fst) cs & \case
        [] ->  go cdef a   -- default case
        [(_, c)] -> go c a -- matching case
        _ -> error "too many switch cases"
    go (YulJmpU (_, f)) ma = ma >>= go f . pure
    go (YulJmpB p) ma = ma >>= \a -> pure (yulB_eval p a)
    go (YulCall _) _ = error "YulCall not supported" -- FIXME
    -- -- storage primitives
    go YulSGet ma = ma >>= \a -> gets $ \s -> fromJust (fromWord =<< M.lookup a (store_map s))
    go YulSPut mav = mav >>= \(a, v) -> modify' $ \s -> s { store_map = M.insert a (toWord v) (store_map s) }

-- | Evaluate a known named yul category morphism with NP-typed inputs.
evalFn :: forall fn efc xs b.
  ( YulO2 (NP xs) b
  , KnownNamedYulCat fn efc (NP xs) b
  ) =>
  fn -> NP xs -> b
evalFn fn = withKnownNamedYulCat fn (evalYulCat . snd)
