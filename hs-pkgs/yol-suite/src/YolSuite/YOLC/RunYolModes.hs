module YolSuite.YOLC.RunYolModes where
-- text
import Data.Text.Lazy           qualified as T
-- yul-dsl
import YulDSL.CodeGens.ShowGens qualified as CodeGens
import YulDSL.CodeGens.YulGen   qualified as CodeGens
import YulDSL.Core
--
import YolSuite.YOLC.Builder    qualified as YOLCBuilder
import YolSuite.YOLC.Manifest   (Manifest)

-- | Result from the RunYol.
type RunYolResult = Either T.Text T.Text

-- yul modes

yulFnMode :: forall fn efc xs b.
  ( KnownNamedYulCat fn efc (NP xs) b
  , YulO2 (NP xs) b
  ) =>
  fn -> IO RunYolResult
yulFnMode fn = do
  config <- YOLCBuilder.getCodeGenConfig
  withKnownNamedYulCat fn (pure . Right . CodeGens.compileFn config)

yulObjectMode :: YulObject -> IO RunYolResult
yulObjectMode obj = do
  config <- YOLCBuilder.getCodeGenConfig
  pure . Right . CodeGens.compileYulObject config $ obj

yulProjectMode :: Manifest -> IO RunYolResult
yulProjectMode = YOLCBuilder.buildManifest

-- show modes

showFnMode ::
  ( KnownNamedYulCat fn efc (NP xs) b
  , Show fn
  ) => fn -> IO RunYolResult
showFnMode = pure . Right . T.pack . show

showObjectMode :: YulObject -> IO RunYolResult
showObjectMode = pure . Right . T.pack . show

showProjectMode :: Manifest -> IO RunYolResult
showProjectMode = pure . Right . T.pack . show

-- show compact modes

showCompactFnMode ::
  KnownNamedYulCat fn efc (NP xs) b =>
  fn -> IO RunYolResult
showCompactFnMode fn = withKnownNamedYulCat fn (pure . Right . T.pack . CodeGens.yulCatCompactShow . snd)

-- lisp modes

showLispFnMode :: forall fn efc xs b.
  KnownNamedYulCat fn efc (NP xs) b =>
  fn -> IO RunYolResult
showLispFnMode fn = withKnownNamedYulCat fn (pure . Right . CodeGens.yulCatToUntypedLisp . snd)
