-- Taken from GHC's nofib benchmarks

nsoln : Nat -> Nat
nsoln nq = length (gen nq)
  where
    safe : Nat -> Nat -> List Nat -> Bool
    safe x d [] = True
    safe x d (q :: l) = 
        x /= q
        && x /= q + d
        && x /= (q `minus` d)
        && safe x (S d) l

    gen : Nat -> List (List Nat)
    gen Z = [[]]
    gen (S k) = [ (q :: b) | b <- gen k, q <- [1..nq], safe q 1 b]

main : IO ()
main = do
    print $ nsoln 8
