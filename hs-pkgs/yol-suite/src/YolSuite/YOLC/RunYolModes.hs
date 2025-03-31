module YolSuite.YOLC.RunYolModes where
-- text
import Data.Text.Lazy         qualified as T
-- yul-dsl
import YulDSL.CodeGens.YulGen qualified as YulCodeGen
import YulDSL.Core
--
import YolSuite.YOLC.Builder  qualified as YOLCBuilder
import YolSuite.YOLC.Manifest (Manifest)

-- | Result from the RunYol.
type RunYolResult = Either T.Text T.Text

-- yul modes

yulFnMode :: forall fn efc xs b.
  ( ClassifiedYulCat fn efc (NP xs) b
  , YulO2 (NP xs) b
  ) =>
  fn -> IO RunYolResult
yulFnMode fn = do
  config <- YOLCBuilder.getCodeGenConfig
  withClassifiedYulCat fn (pure . Right . YulCodeGen.compileFn config)

yulObjectMode :: YulObject -> IO RunYolResult
yulObjectMode obj = do
  config <- YOLCBuilder.getCodeGenConfig
  pure . Right . YulCodeGen.compileYulObject config $ obj

yulProjectMode :: Manifest -> IO RunYolResult
yulProjectMode = YOLCBuilder.buildManifest

-- show modes

showFnMode :: Show fn => fn -> IO RunYolResult
showFnMode = pure . Right . T.pack . show

showObjectMode :: YulObject -> IO RunYolResult
showObjectMode = pure . Right . T.pack . show

showProjectMode :: Manifest -> IO RunYolResult
showProjectMode = pure . Right . T.pack . show

-- lisp modes

lispFnMode :: forall fn efc xs b.
  ( ClassifiedYulCat fn efc (NP xs) b
  , YulO2 (NP xs) b
  ) =>
  fn -> IO RunYolResult
lispFnMode fn = withClassifiedYulCat fn (pure . Right . yulCatToUntypedLisp . snd)
