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

yulFnMode :: forall eff f. YulO2 (NP (UncurryNP'Fst f)) (UncurryNP'Snd f)
            => Fn eff f -> IO RunYolResult
yulFnMode = pure . Right . YulCodeGen.compileFn . unFn

yulObjectMode :: YulObject -> IO RunYolResult
yulObjectMode = pure . Right . YulCodeGen.compileYulObject

yulProjectMode :: Manifest -> IO RunYolResult
yulProjectMode = YOLCBuilder.buildManifest

-- show modes

showFnMode :: Show a => a -> IO RunYolResult
showFnMode = pure . Right . T.pack . show

showObjectMode :: Show a => a -> IO RunYolResult
showObjectMode = showFnMode

showProjectMode :: Show a => a -> IO RunYolResult
showProjectMode = showFnMode
