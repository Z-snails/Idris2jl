main : IO ()
main = do
    printLn $ fastUnpack "hello world"
    printLn $ fastPack ['a', 'b', 'c', 'd']
    printLn $ fastConcat ["hello", "from", "julia", "from", "idris", "2"]
