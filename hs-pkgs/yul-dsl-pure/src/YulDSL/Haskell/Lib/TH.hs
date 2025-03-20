module YulDSL.Haskell.Lib.TH
  ( locId
  ) where
-- template-haskell
import Language.Haskell.TH qualified as TH


-- | Automatically generate a source location based id using template haskell.
locId :: TH.Q TH.Exp
locId = do
  loc <- TH.location
  let modname = TH.loc_module loc
      -- normalize module name: replace "."
      modname' = fmap (\x -> if x `elem` "." then '_' else x) modname
      (s1, s2) = TH.loc_start loc
  TH.litE (TH.StringL (modname' ++ "_" ++ show s1 ++ "_" ++ show s2))
