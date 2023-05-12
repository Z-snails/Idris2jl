tailLoop : Nat -> IO ()
tailLoop Z = pure ()
tailLoop (S k) = tailLoop k

main : IO ()
main = tailLoop 10