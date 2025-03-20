{-|

Copyright   : (c) 2024-2025 Miao, ZhiCheng
License     : MIT

Maintainer  : hellwolf@yolc.dev
Stability   : experimental
Portability : GHC2024

The template haskell utilities for List, TupleN and NP types.

-}
module Data.TupleN.TH
  ( tupleNFromVarsTWith, tupleNFromVarsT
  , promotedListFromVarsT
  ) where
-- template-haskell
import Language.Haskell.TH qualified as TH


tupleNFromVarsTWith :: TH.Quote m => (m TH.Type -> m TH.Type) -> [TH.Name] -> m TH.Type
tupleNFromVarsTWith f as = foldl' TH.appT (TH.tupleT (length as)) (fmap (f . TH.varT) as)

tupleNFromVarsT :: TH.Quote m => [TH.Name] -> m TH.Type
tupleNFromVarsT = tupleNFromVarsTWith id

promotedListFromVarsT :: TH.Quote m => [TH.Name] -> m TH.Type
promotedListFromVarsT = foldr (TH.appT . TH.appT TH.promotedConsT . TH.varT) TH.promotedNilT
