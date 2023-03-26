import Data.Buffer
import System.File.Buffer

main : IO ()
main = do
    Right b <- createBufferFromFile "./test.idr"
        | Left err => putStrLn "oopsie woopsie: \{show err}"
    putStrLn "yay"
