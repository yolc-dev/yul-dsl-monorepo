{-# LANGUAGE OrPatterns #-}
{-|
Copyright   : (c) 2025 Miao, ZhiCheng
License     : MIT
Maintainer  : hellwolf@yolc.dev
Stability   : experimental

= Yolc Demo

-}

module Demo where
-- import Control.LinearlyVersionedMonad.LVM qualified as LVM
import Prelude                            (Show)
import Prelude.YulDSL

{- |

= What Is Yolc?

== Yolc embeds itself in Haskell

* What Is Haskell?

- "Enjoy long-term maintainable software you can rely on"
- Statically typed.
- Purely functional.
- Type inference.
- etc.

To learn more:

- https://learnyouahaskell.com/
- https://joyful.com/Haskell+map
- https://haskell-links.org/

-}

{- |

* A small example of Haskell data type:

-}

type Unit = U256
type Price = U256
type DateTime = U32

-- Use "Algebraic Data Type (ADT)" to represent possible values.
data Order
  -- Market buy or sell order.
  = MarketBuyOrder Unit DateTime
  | MarketSellOrder Unit DateTime
  -- A buy limit order will be executed only at the limit price or lower.
  | BuyLimitOrder Unit Price DateTime
  -- A sell limit order will be executed only at the limit price or higher.
  | SellLimitOrder Unit Price DateTime
  deriving Show

-- Pattern matching:

isLimitedOrder :: Order -> Bool
isLimitedOrder (BuyLimitOrder {}; SellLimitOrder {}) = True
isLimitedOrder _ = False

marketPrice :: [Order] -> Price
marketPrice = undefined -- Can you find an algorithm for this?

{- |

* Why Haskell For Ethereum?

(It's about the type, type, type...)

- Expressive type system: hard problem made simple.
- Type-level safety: built for production.
  - We will see some examples about type-level safety, later.

-}

----------------------------------------------------------------------------------------------------

{- |

= What Is Yolc?

== Yolc doesn't rebuild wheel

* Yolc works with Solidity/Yul

(rember solc?)

Let's print some Yul code:

-}

mul_uint256 :: PureFn (U256 -> U256 -> U256)
mul_uint256 = $fn \x y -> x * y

-- A Yolc function working with optional value (Maybe value):
add_maybe_int96 :: PureFn (Maybe I96 -> I96 -> I96)
add_maybe_int96 = $fn
  \a b -> match a \case
    Just a' -> a' + b
    Nothing -> 0

add_maybe_int96' :: PureFn (Maybe I96 -> I96 -> Maybe I96)
add_maybe_int96' = $fn
  \a b -> (\a' -> a' + b) <$$> a

shmapGetTest :: StaticFn (ADDR -> U256)
shmapGetTest = $lfn $ ylvm'pv
  \acc -> LVM.do
    let smap = makeSMap "shmapGetTest" :: SMap (ADDR -> U256)
    sgetM $ smap #-> acc

{- |

* Yolc works with foundry

Let's see an example of "Counter" contract and its tests.

-}

----------------------------------------------------------------------------------------------------

{- |

= What Is Yolc?

== Safety Feature: Yolc and Data Versioning

- Data fetched (storage read or contract call) can be out-dated.
- Using out-dated data can be fatal:
  - Re-entrancy error is one of them.

Let's see it in action in a tiny ERC20 example.

-}

----------------------------------------------------------------------------------------------------

{- |

= What's Next

== When is it ready?

- Still WIP.
  - More feature completion by the time of presenting at ETHCC!
- Dogfooding:
  - Building small utility contracts for Superfluid.
  - Prototype Superfluid Protocol V3 with a ZKSolvency protocol upgrade.

== Follow My Work of Yolc of at Superfluid

- Visit https://yolc.dev/, where you can find how to:
  - Follow on X @yolc_dev
  - Join matrix channel: https://matrix.to/#/#yolc:matrix.org
  - Follow github: https://github.com/yolc-dev/
- Visit @Superfluid_HQ on X
  - I am looking for a zk engineer to work with for the Superfluid protocol v3!

-}

----------------------------------------------------------------------------------------------------

{- |

- Thank you! Questions?

-}
