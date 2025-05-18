module YolSuite.ReplUtils
  ( module YulDSL.CodeGens.GraphVizGen
  , printCat, printFn
  , module YulDSL.CodeGens.YulGen
  , previewFn, previewFnVerbose
  ) where
-- text
import Data.Text.Lazy              qualified as T
-- yul-dsl
import YulDSL.CodeGens.YulGen
import YulDSL.Core
--
import YolSuite.YOLC.Builder       qualified as YOLCBuilder
import YulDSL.CodeGens.GraphVizGen


-- | Generate yul code of a morphism and print it to the screen.
printCat :: YulO2 a b => YulCat eff a b -> IO ()
printCat cat = do
  config <- YOLCBuilder.getCodeGenConfig
  putStr $ T.unpack $ compileCat config cat

-- | Generate yul code of a function and print it to the screen.
printFn :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP xs) b
  , YulO2 (NP xs) b
  ) =>
  fn -> IO ()
printFn fn = do
  config <- YOLCBuilder.getCodeGenConfig
  putStr $ T.unpack $ withKnownNamedYulCat fn (compileFn config)

-- | Preview a function in a display window.
previewFn :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP xs) b
  , YulO2 (NP xs) b
  ) =>
  fn -> IO ()
previewFn fn = withKnownNamedYulCat fn (previewYulCat . snd)

-- | Preview a function in a display window.
previewFnVerbose :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP xs) b
  , YulO2 (NP xs) b
  ) =>
  fn -> IO ()
previewFnVerbose fn = withKnownNamedYulCat fn (previewYulCatVerbose . snd)
