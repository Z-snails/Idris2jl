data Tree : Type -> Type where
    Tip : a -> Tree a
    Bin : Tree a -> a -> Tree a -> Tree a

printTree : Show a => Tree a -> String -> String
printTree (Tip x) ind = ind ++ show x
printTree (Bin l m r) ind =
    ind ++ show m ++ "\n"
        ++ printTree l (ind ++ "  ") ++ "\n"
        ++ printTree r (ind ++ "  ")

tree : Tree Int
tree = Bin (Bin (Tip 1) 2 (Tip 3)) 4 (Tip 5)

main : IO ()
main = putStrLn $ printTree tree ""
