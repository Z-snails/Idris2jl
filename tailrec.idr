isEven, isOdd : Nat -> Bool

isEven Z = True
isEven (S k) = isOdd k

isOdd Z = False
isOdd (S k) = isEven k


main : IO ()
main = printLn $ isEven 101
