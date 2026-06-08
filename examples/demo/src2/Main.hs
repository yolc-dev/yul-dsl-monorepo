import Counter                   (getCounterRef, object)
import YolSuite.YOLC.RunYolModes

main :: IO ()
main = print =<< show <$>
  showObjectMode object
