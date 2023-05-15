module Compiler.Julia.TailRec

import Core.CompileExpr
import Core.Name
import Core.Context
import Libraries.Data.Graph
import Libraries.Data.SortedSet
import Libraries.Data.SortedMap
import Data.List1

public export
data CallGroup : Type where
    Single :
        (rec : Bool) ->
        (def : (Name, FC, NamedDef)) ->
        CallGroup
    Group :
        (canTail : SortedSet Name) ->
        (defs : List1 (Name, FC, NamedDef)) ->
        CallGroup

tailCalls : NamedCExp -> SortedSet Name -> SortedSet Name
tailCalls (NmLet fc x y z) acc = tailCalls z acc
tailCalls (NmApp fc (NmRef _ n) xs) acc = insert n acc
tailCalls (NmConCase fc sc xs x) acc =
    maybe id tailCalls x
        $ foldl (\acc, (MkNConAlt _ _ _ _ e) => tailCalls e acc) acc xs
tailCalls (NmConstCase fc sc xs x) acc =
    maybe id tailCalls x
        $ foldl (\acc, (MkNConstAlt _ e) => tailCalls e acc) acc xs
tailCalls _ acc = acc

tailCallsDef : NamedDef -> SortedSet Name
tailCallsDef (MkNmFun args x) = tailCalls x empty
tailCallsDef (MkNmCon tag arity nt) = empty
tailCallsDef (MkNmForeign ccs fargs x) = empty
tailCallsDef (MkNmError x) = empty

export
mkCallGroups : List (Name, FC, NamedDef) -> Maybe (List CallGroup)
mkCallGroups xs =
    let defs = SortedMap.fromList xs
        ns = SortedMap.fromList $ map (\(n, _, def) => (n, tailCallsDef def)) xs
        groups = tarjan ns
        selfRec = \n => case lookup n ns of
            Just cs => contains n cs
            Nothing => False
        getDef = \n => (n,) <$> lookup n defs
     in traverse (\xs => case xs of
        n ::: [] => Single (selfRec n) <$> getDef n
        _ => Group (SortedSet.fromList $ forget xs) <$> traverse getDef xs) groups
