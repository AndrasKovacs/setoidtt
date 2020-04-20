
import qualified Data.Array.FI as FI

main :: IO ()
main = do
  let foo = FI.fromList [0..100000::Int]
  print $ FI.foldr (+) 0 foo
