{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE UndecidableInstances   #-}
{-|

Copyright   : (c) 2023-2025 Miao, ZhiCheng
License     : LGPL-3
Maintainer  : hellwolf@yolc.dev
Stability   : experimental
-}
module YulDSL.Haskell.Effects.LinearSMC.LinearFn
  ( -- * Build Linear Yul Functions
    lfn'
    -- * Call External Smart Contract Functions
  ) where
-- base
import GHC.TypeLits                                  (KnownNat, type (+), type (<=))
-- template-haskell
import Language.Haskell.TH                           qualified as TH
-- linear-base
import Prelude.Linear
-- yul-dsl
import YulDSL.Core
-- yul-dsl-pure
import YulDSL.Haskell.LibPure
-- (linearly-versioned-monoad)
import Control.LinearlyVersionedMonad                qualified as LVM
--
import YulDSL.Haskell.Effects.LinearSMC.LinearYulCat
import YulDSL.Haskell.Effects.LinearSMC.YulMonad
import YulDSL.Haskell.Effects.LinearSMC.YulPort

------------------------------------------------------------------------------------------------------------------------
-- Linear Non-Pure Effects
------------------------------------------------------------------------------------------------------------------------

data StaticFn f where
  MkStaticFn :: forall (eff :: LinearEffectKind) f xs b.
                ( ClassifiedYulCatEffect eff, AssertStaticEffect eff
                , EquivalentNPOfFunction f xs b
                ) => NamedYulCat eff (NP xs) b ⊸ StaticFn f

instance EquivalentNPOfFunction f xs b => ClassifiedYulCat (StaticFn f) StaticEffect (NP xs) b where
  withClassifiedYulCat (MkStaticFn f) g = g f

data OmniFn f where
  MkOmniFn :: forall (eff :: LinearEffectKind) f xs b.
              ( ClassifiedYulCatEffect eff, AssertOmniEffect eff
              , EquivalentNPOfFunction f xs b
              ) => NamedYulCat eff (NP xs) b ⊸ OmniFn f

instance EquivalentNPOfFunction f xs b => ClassifiedYulCat (OmniFn f) OmniEffect (NP xs) b where
  withClassifiedYulCat (MkOmniFn f) g = g f

------------------------------------------------------------------------------------------------------------------------
-- Constructible Linear Functions
------------------------------------------------------------------------------------------------------------------------

-- | Create classified linear kind of yul functions.
class ConstructibleLinearFn fn (ie :: PortEffect) (oe :: PortEffect) where
  -- | Define a `YulCat` morphism from a yul port diagram.
  lfn' :: forall f xs b.
    ( YulO2 (NP xs) b
    , EquivalentNPOfFunction f xs b
    ) =>
    String ->
    (forall r. YulO1 r => P'x ie r (NP xs) ⊸ P'x oe r b) ->
    fn f

instance ConstructibleLinearFn PureFn PurePort PurePort where
  lfn' cid f = MkPureFn (cid, decode'l f)

instance ConstructibleLinearFn StaticFn (VersionedPort 0) (VersionedPort 0) where
  lfn' cid f = MkStaticFn (cid, decode'l f)

instance ConstructibleLinearFn StaticFn PurePort (VersionedPort 0) where
  lfn' cid f = MkStaticFn (cid, decode'l f)


