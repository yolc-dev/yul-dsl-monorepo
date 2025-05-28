module YulDSL.Haskell.LibLinearSMC
  ( -- * Re-export Base and Linear-base Preludes

    -- ** Basic data types
    Prelude.Char
  , module Data.Bool.Linear
  , module Data.Maybe.Linear
  , module Data.Either.Linear

    -- ** Tuples
  , fst
  , snd
  , curry
  , uncurry

    -- ** Basic type classes
    -- , module Data.Ord.Linear
  , Prelude.Enum (..)
  , Prelude.Bounded (..)

    -- ** Numbers
  , Prelude.Int
  , Prelude.Integer
  , Prelude.Float
  , Prelude.Double
  , Prelude.Rational
  , Prelude.Word
  , Prelude.Real (..)
  , Prelude.Integral (..)
  , Prelude.Floating (..)
  , Prelude.Fractional (..)
  , Prelude.RealFrac (..)
  , Prelude.RealFloat (..)
  -- , Prelude.Num vs. Data.Num.Linear
  -- , Prelude.Linear.fromInteger
  , module Data.Num.Linear

    -- ** Functions on strings

  , module Data.String

    -- *** Numeric functions
  , Prelude.subtract
  , Prelude.even
  , Prelude.odd
  , Prelude.gcd
  , Prelude.lcm
  , (Prelude.^)
  , (Prelude.^^)
  , Prelude.fromIntegral
  , Prelude.realToFrac

    -- ** Miscellaneous functions
  , id
  , const
  , (.)
  , flip
  , ($)
  , (&)
  , Prelude.until
  , Prelude.error
  , Prelude.errorWithoutStackTrace
  , Prelude.undefined
  , seq
  , ($!), type (~)

    -- ** Doing non-linear operations inside linear functions
    -- $
  , Prelude.Linear.Consumable (..)
  , Prelude.Linear.Dupable (..)
  , Prelude.Linear.Movable (..)
  , Prelude.Linear.lseq
  , Prelude.Linear.dup
  , Prelude.Linear.forget

    -- * Re-export library for pure yul functions
  , module YulDSL.Haskell.LibPure

    -- * Re-export library for building linear-smc yul effects
  , module YulDSL.Haskell.Effects.LinearSMC

    -- * YLVM Utilities
  , yaddress, ycaller, ychainid

    -- * Yul Port Utilities
  , keccak256'l
  ) where
-- base curated
import Data.String
import Prelude qualified
-- linear-base curated
import Data.Bool.Linear
import Data.Either.Linear
import Data.Maybe.Linear
import Data.Num.Linear
import Prelude.Linear
    ( const
    , curry
    , flip
    , fst
    , id
    , seq
    , snd
    , type (~)
    , uncurry
    , ($!)
    , ($)
    , (&)
    , (.)
    )
import Prelude.Linear qualified
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (lvm)
import Control.LinearlyVersionedMonad.LVM qualified as LVM
--
import Data.Num.Linear.YulDSL             ()
import YulDSL.Haskell.Effects.LinearSMC


keccak256'l :: forall a eff r. YulO2 r a => P'x eff r a ⊸ P'x eff r B32
keccak256'l = encodeP'x (YulJmpB (MkYulBuiltIn @"__keccak_c_" @a @B32))

--
-- Block and Transaction Properties
--

yaddress :: forall r v. (KnownNat v, YulO1 r) => YLVM v v r (Ur (Uv r ADDR))
yaddress = embed () LVM.>>= ymakev . encodeP'x (YulJmpB (MkYulBuiltIn @"__address"))

ycaller :: forall r v. (KnownNat v, YulO1 r) => YLVM v v r (Ur (Uv r ADDR))
ycaller = embed () LVM.>>= ymakev . encodeP'x (YulJmpB (MkYulBuiltIn @"__caller"))

ychainid :: forall r v. (KnownNat v, YulO1 r) => YLVM v v r (Ur (Uv r U256))
ychainid = embed () LVM.>>= ymakev . encodeP'x (YulJmpB (MkYulBuiltIn @"__chainid"))
