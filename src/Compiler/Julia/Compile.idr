module Compiler.Julia.Compile

import Compiler.Julia.Syntax
import Compiler.Julia.TailRec
import Compiler.Julia.Utils
import Control.Monad.State
import Core.CompileExpr
import Core.Context
import Core.Core
import Core.TT
import Data.List1
import Data.String
import Data.These
import Data.Vect
import Libraries.Data.NameMap
import Libraries.Data.SortedSet
import Libraries.Data.StringMap
import Libraries.Data.StringTrie

call : String -> List JExpr -> JExpr
call fn as = App (Var $ Raw fn) as

requiresLet : NamedCExp -> Bool
requiresLet (NmLocal {}) = False
requiresLet (NmRef {}) = False
requiresLet (NmPrimVal {}) = False
requiresLet _ = True

typeOf : Constant -> PrimType
typeOf (I i) = IntType
typeOf (I8 i) = Int8Type
typeOf (I16 i) = Int16Type
typeOf (I32 i) = Int32Type
typeOf (I64 i) = Int64Type
typeOf (BI i) = IntegerType
typeOf (B8 m) = Bits8Type
typeOf (B16 m) = Bits16Type
typeOf (B32 m) = Bits32Type
typeOf (B64 m) = Bits64Type
typeOf (Str str) = StringType
typeOf (Ch c) = CharType
typeOf (Db dbl) = DoubleType
typeOf (PrT pty) = pty
typeOf WorldVal = WorldType

isCompare : PrimFn ar -> Bool
isCompare (LT {}) = True
isCompare (LTE {}) = True
isCompare (EQ {}) = True
isCompare (GTE {}) = True
isCompare (GT {}) = True
isCompare f = False

mkName : (ns : Namespace) -> (n : String) -> Name
mkName ns n = NS ns $ UN $ Basic n

jPrelude, ioRef, ioArray : Namespace
jPrelude = mkNamespace "Julia.Prelude"
ioRef = mkNamespace "Data.IORef"
ioArray = mkNamespace "Data.IOArray.Prims"

argError : String
argError = "unexpected argument count"

tailArgs : JName
tailArgs = Idr $ MN "args" 0

externs : NameMap (List JExpr -> Either String JExpr)
externs = fromList
    [ (mkName jPrelude "val", \as => pure $ call "Val" as)

    , (mkName ioRef "prim__newIORef", \case
        [_, val, w] => pure $ call "Mut" [val]
        _ => Left argError)
    , (mkName ioRef "prim__readIORef", \case
        [_, mut, w] => pure $ Field mut "val"
        _ => Left argError)
    , (mkName ioRef "prim__writeIORef", \case
        [_, mut, val, w] => pure $ call "Idris.writeIORef" [mut, val]
        _ => Left argError)

    , (mkName ioArray "prim__newArray", \case
        [_, n, val, w] => pure $ call "Idris.newArray" [n, val]
        _ => Left argError)
    , (mkName ioArray "prim__arrayGet", \case
        [_, arr, idx, w] => pure $ call "Idris.arrayGet" [arr, idx]
        _ => Left argError)
    , (mkName ioArray "prim__arraySet", \case
        [_, arr, idx, val, w] => pure $ call "Idris.arraySet!" [arr, idx, val]
        _ => Left argError)
    ]

parameters (canTail : Name -> Bool)
    expr : (tailPos : Bool) -> NamedCExp -> StateT Int (Either (FC, String)) JExpr
    mkConCase : (tailPos : Bool) -> FC -> JExpr -> List NamedConAlt -> Maybe NamedCExp -> StateT Int (Either (FC, String)) JExpr
    mkConstCase : (tailPos : Bool) -> FC -> JExpr -> List NamedConstAlt -> Maybe NamedCExp -> StateT Int (Either (FC, String)) JExpr

    expr _ (NmLocal fc n) = pure $ Var $ Idr n
    expr _ (NmRef fc n) = pure $ Var $ Idr n
    expr _ (NmLam fc n y) = pure $ Lam n !(expr False y)
    expr tp (NmLet fc n y z) = pure $ mkLet (n, Nothing, !(expr False y)) !(expr tp z)
    expr tp (NmApp fc f@(NmRef _ n) xs) =
        if canTail n
            then pure $ Sequence
                $ Assign (PVar tailArgs Nothing) (Tuple !(traverse (expr False) xs))
                ::: [Macro "goto" [Var $ Lbl n]]
            else pure $ App !(expr False f) !(traverse (expr False) xs)
    expr _ (NmApp fc x xs) = pure $ App !(expr False x) !(traverse (expr False) xs)
    -- expr _ (NmCon fc n NIL tag []) = pure $ Var "nothing"
    -- expr _ (NmCon fc n CONS tag xs@[_, _]) = pure $ call "Cons" !(traverse (expr False) xs)
    expr _ (NmCon fc n inf tag xs) = pure $ App (Var $ Idr n) !(traverse (expr False) xs)
    expr _ (NmOp fc f xs) = if isCompare f
        then pure $ call "Int" [PrimOp f !(traverse (expr False) xs)]
        else pure $ PrimOp f !(traverse (expr False) xs)
    expr _ (NmExtPrim fc p xs) = case lookup p externs of
        Just fn => lift $ mapFst (fc,) $ fn !(traverse (expr False) xs)
        Nothing => lift $ Left (fc, "Unknown primitive: \{show p}")
    expr _ (NmForce fc lz x) = pure $ call "force" [!(expr False x)]
    expr _ (NmDelay fc lz x) = pure $ Macro "delay" [!(expr False x)]
    expr _ (NmConCase fc sc xs def) = if requiresLet sc
        then do
            v <- MN "sc" <$> state (\x => (x + 1, x))
            pure $ mkLet
                (v, Nothing, !(expr False sc))
                !(mkConCase False fc (Var $ Idr v) xs def)
        else mkConCase False fc !(expr False sc) xs def
    expr _ (NmConstCase fc sc xs def) = if requiresLet sc
        then do
            v <- MN "sc" <$> state (\x => (x + 1, x))
            pure $ mkLet
                (v, Nothing, !(expr False sc))
                !(mkConstCase False fc (Var $ Idr v) xs def)
        else mkConstCase False fc !(expr False sc) xs def
    expr _ (NmPrimVal fc cst) = pure $ Lit cst
    expr _ (NmErased fc) = pure $ Var "nothing"
    expr _ (NmCrash fc str) = pure $ Throw (call "Idris.Error" [Lit (Str str)])

    bindAll : JExpr -> Nat -> List Name -> JExpr -> JExpr
    bindAll sc k [] e = e
    bindAll sc k (n :: ns) e = mkLet (n, Nothing, Field sc "v\{show k}") (bindAll sc (S k) ns e)

    mkConCase _ fc sc [] Nothing = pure $ Macro {ns=Just "Idris"} "unreachable" [Lit (Str (show fc))]
    mkConCase tp fc sc [] (Just def) = expr tp def
    mkConCase tp fc sc (MkNConAlt n inf _ as e :: xs) def =
        let f = \e => case (inf, as) of
                -- (NIL, []) => IfExpr (call "isnothing" [sc]) e
                -- (CONS, [fst, snd]) => IfExpr (call "notnothing" [sc])
                --     (Let ((PVar fst Nothing, Field sc "fst") ::: [(PVar snd Nothing, Field sc "snd")]) e)
                _ => IfExpr (sc `IsA` (VarTy $ Idr n))
                    (bindAll sc 0 as e)
        in pure $ f !(expr tp e) !(mkConCase tp fc sc xs def)

    mkConstCase _ fc sc [] Nothing = pure $ Macro {ns=Just "Idris"} "unreachable" [Lit (Str (show fc))]
    mkConstCase tp fc sc [] (Just def) = expr tp def
    mkConstCase tp fc sc (MkNConstAlt v e :: xs) def =
        pure $ IfExpr (PrimOp (EQ (typeOf v)) [sc, Lit v])
            !(expr tp e)
            !(mkConstCase tp fc sc xs def)

juliaType : CFType -> Maybe JType
juliaType CFUnit = Just $ VarTy "Nothing"
juliaType CFInt = Just $ PrimTy IntType
juliaType CFInteger = Just $ PrimTy IntegerType
juliaType CFInt8 = Just $ PrimTy Int8Type
juliaType CFInt16 = Just $ PrimTy Int16Type
juliaType CFInt32 = Just $ PrimTy Int32Type
juliaType CFInt64 = Just $ PrimTy Int64Type
juliaType CFUnsigned8 = Just $ PrimTy Bits8Type
juliaType CFUnsigned16 = Just $ PrimTy Bits16Type
juliaType CFUnsigned32 = Just $ PrimTy Bits32Type
juliaType CFUnsigned64 = Just $ PrimTy Bits64Type
juliaType CFString = Just $ PrimTy StringType
juliaType CFDouble = Just $ PrimTy DoubleType
juliaType CFChar = Just $ PrimTy CharType
juliaType CFPtr = Just voidPtr
juliaType CFGCPtr = Just voidPtr
juliaType CFBuffer = Nothing
juliaType CFForeignObj = Nothing
juliaType CFWorld = Just $ VarTy "Nothing"
juliaType (CFFun x y) = Just $ VarTy "Function"
juliaType (CFIORes x) = juliaType x
juliaType (CFStruct str xs) = Nothing
juliaType (CFUser n xs) = Nothing

cType : CFType -> Either String JType
cType CFUnit = pure $ VarTy "Cvoid"
cType CFInt = pure $ VarTy "Cint"
cType CFInteger = Left "unsupported type in julia foreign function interface: Integer"
cType CFInt8 = pure $ PrimTy Int8Type
cType CFInt16 = pure $ PrimTy Int16Type
cType CFInt32 = pure $ PrimTy Int32Type
cType CFInt64 = pure $ PrimTy Int64Type
cType CFUnsigned8 = pure $ PrimTy Bits8Type
cType CFUnsigned16 = pure $ PrimTy Bits16Type
cType CFUnsigned32 = pure $ PrimTy Bits32Type
cType CFUnsigned64 = pure $ PrimTy Bits64Type
cType CFString = pure $ VarTy "Cstring"
cType CFDouble = pure $ VarTy "double"
cType CFChar = pure $ PrimTy CharType
cType CFPtr = pure voidPtr
cType CFGCPtr = pure voidPtr
cType CFBuffer = pure $ VarTy "Buffer"
cType CFForeignObj = pure voidPtr
cType CFWorld = pure $ VarTy "Nothing"
cType (CFFun x y) = pure voidPtr
cType (CFIORes x) = cType x
cType (CFStruct str xs) = Left "unsupported type in julia foreign function interface: struct"
cType (CFUser n xs) = Left "unsupported type in julia foreign function interface: user type"

parseImport : FC -> String -> Either Error String
parseImport fc imp = case stripPrefix "import " imp of
    Just x => pure x
    Nothing => Left $ GenericMsg fc "malformed import specifier, expected `import <lib>`"

juliaParseCC : List String -> Maybe (String, List1 String) -> Maybe (String, List1 String)
juliaParseCC [] acc = acc
juliaParseCC (cc :: ccs) old = case (try cc, old) of
    (cc@(Just ("julia", opts)), _) => cc -- stop with first julia
    (new@(Just _), Nothing) => juliaParseCC ccs new -- replace no specifier with any
    _ => juliaParseCC ccs old -- don't replace C with later C
    where
    try : String -> Maybe (String, List1 String)
    try str =
        let Nothing = stripPrefix "julia:" str
                | Just opts => Just ("julia", trim <$> split (== ';') opts)
            Nothing = stripPrefix "C:" str
                | Just opts => Just ("C", trim <$> split (== ',') opts)
            in Nothing

knownForeign : Name -> InlineOk -> List String -> Maybe (Fun, List String)
knownForeign n inl [] = Nothing
knownForeign n inl (cc :: ccs) = try (trim cc) <|> knownForeign n inl ccs
    where
    callSupport : InlineOk -> List (Maybe JType) -> String -> Fun
    callSupport inl tys fn =
        let as = enumerate tys
         in MkFun (Idr n) inl
                ((\(i, ty) => (Idr $ MN "arg" $ cast i, ty)) <$> as)
                Nothing
                (call fn ((\(i, _) => Var $ Idr $ MN "arg" $ cast i) <$> as)) []

    try : String -> Maybe (Fun, List String)
    try "scheme:blodwen-new-buffer" =
        Just (callSupport inl [Just intType] "Buffer", [])
    try "scheme:blodwen-buffer-size" =
        Just (callSupport inl [Nothing] "Base.length", [])
    try "C:idris2_isNull, libidris2_support, idris_support.h" =
        Just (callSupport YesInline [Just voidPtr] "Idris.isNull", [])
    try "C:idris2_getNull, libidris2_support, idris_support.h" =
        Just (callSupport YesInline [] "Idris.getNull", [])
    try "scheme:blodwen-thread" =
        Just (callSupport inl [Nothing] "Idris.fork", [])
    try "scheme:string-concat" =
        Just (callSupport inl [Nothing] "Idris.fastConcat", [])
    try "scheme:string-pack" =
        Just (callSupport inl [Nothing] "Idris.fastPack", [])
    try "scheme:string-unpack" =
        Just (callSupport inl [Nothing] "Idris.fastUnpack", [])
    try _ = Nothing

foreign : FC -> Name  -> InlineOk -> List String -> List CFType -> CFType -> Either Error (Fun, List String)
foreign fc n inl ccs args ret = do
    let args = (\(i, x) => (MN "v" (cast i), x)) <$> enumerate args
    let Nothing = knownForeign n inl ccs
        | Just x => pure x
    case juliaParseCC ccs Nothing of
        Just ("julia", opts) =>  do
            let (imps, expr) = unsnoc opts
            imps <- traverse (parseImport fc) imps
            pure (Fun.untyped (Idr n) inl (Idr . fst <$> args) Nothing (App (Embed expr) (Var . Idr . fst <$> args)), imps)

        Just ("C", opts) => do
            fun <- case opts of
                    fun ::: [] => Right $ Var $ Raw fun
                    fun ::: lib :: _ => Right $ Field (call "joinpath" [Macro "__DIR__" [], Lit $ Str lib]) fun
            cargs <- traverse (\(v, ty) => pure $ Annot (Var $ Idr v) !(mapFst (GenericMsg fc) (cType ty)))
                $ filter (\(_, ty) => case ty of {CFWorld => False; _ => True}) args
            let call = Macro "ccall" [App fun cargs `Annot` !(mapFst (GenericMsg fc) (cType ret))]
                call = case ret of
                    CFString => Compile.call "Idris.from_Cstring" [call]
                    _ => call
            pure (MkFun (Idr n) inl (map (\(i, ty) => (Idr i, juliaType ty)) args) Nothing call [], [])

        _ => Left $ NoForeignCC fc ccs

mkGenericMsg : Either (FC, String) a -> Either Error a
mkGenericMsg (Right x) = Right x
mkGenericMsg (Left (fc, err)) = Left $ GenericMsg fc err

inlineable : Ref Ctxt Defs => Name -> Core InlineOk
inlineable n = case !(lookupCtxtExact n $ gamma !(get Ctxt)) of
    Just def => if Inline `elem` def.flags
        then pure YesInline
        else pure NotInline
    Nothing => pure NotInline

singleDef : Ref Ctxt Defs => (canTail : Name -> Bool) -> (Name, FC, NamedDef) -> Core (Maybe Stmt, List String)
singleDef canTail (n, _, MkNmFun args x) = pure (Just $ JFun $ Fun.untyped (Idr n) !(inlineable n) (map Idr args) Nothing
    !(liftEither $ mkGenericMsg $ evalStateT 0 (expr canTail True x)), [])
singleDef _ (n, _, MkNmCon tag arity nt) = pure (Nothing, [])
singleDef _ (n, fc, MkNmForeign ccs fargs ret) = mapFst (Just . JFun) <$> liftEither (foreign fc n !(inlineable n) ccs fargs ret)
singleDef _ (n, _, MkNmError x) = pure (Just $ JFun $ Fun.untyped (Idr n) !(inlineable n) [] (Just $ Idr $ UN Underscore)
    !(liftEither $ mkGenericMsg $ evalStateT 0 (expr (const False) True x)), [])

export
data GroupNum : Type where

export
group : Ref Ctxt Defs => Ref GroupNum Nat => CallGroup -> Core (List Stmt, List String)
group (Single False def) = do
    (ms, imps) <- singleDef (const False) def
    pure (maybe [] pure ms, imps)
group (Single True d@(n, fc, (MkNmFun args x))) = do
    (Just (JFun fun), imps) <- singleDef (== n) d
        | _ => unreachable (__LOC__)
    let assignArgs = Assign (PVar tailArgs Nothing) $ Tuple $ map (Var . Idr) args
        lbl = Macro "label" [Var $ Lbl n]
        readArgs = Assign (PTuple (map (\a => PVar (Idr a) Nothing) args)) (Var tailArgs)
        fun =
            { body := Sequence $ assignArgs ::: [lbl, readArgs, fun.body]
            } fun
    pure $ ([JFun fun], imps)
group (Single True _) = unreachable (__LOC__)
group (Group tail defs) = do
    num <- get GroupNum
    put GroupNum (S num)
    let groupName = Idr $ MN "rec_group" (cast num)
    let funName = Idr $ MN "rec_fun" 0

    let canTail = \n => contains n tail

    -- Compile each function individually
    (funs, imps) <- unzip <$> traverse (\def => do
        (Just (JFun fun), imps) <- singleDef canTail def
            | _ => unreachable (__LOC__)
        pure (fun, imps)) (forget defs)

    -- Generate the sequence of `@goto`s at the start of the group
    let gotoTable : JExpr = Sequence $ snoc
            (map (\(fn, _, _) => And
                (isEqual (Var funName) (Quote $ Var $ Lbl fn))
                (Macro "goto" [Var $ Lbl fn])) defs)
            (Throw $ call "Idris.Error" [Lit $ Str "invalid function in recursive group"])

    -- Combine all definitions, with their respective `@label`
    let impls : List JExpr =
            funs >>= \f =>
                let body = Syntax.Let (singleton (PTuple ((\(a, mty) => PVar a mty) <$> f.args), Var tailArgs)) f.body
                 in [ Macro "label" [Var $ asLabel f.name]
                    , body
                    ]

    -- Combine it all into the worker function
    let groupFun = Syntax.MkFun
            { name = groupName
            , inline = NotInline
            , args = [(underscore, Just $ AppTy "Val" [VarTy funName])]
            , varargs = Just tailArgs
            , body = Sequence (gotoTable ::: impls)
            , whereBlock = [(funName, Nothing)]
            }

    -- Generate the proxy functions, which call the worker function
    let proxys = mapMaybe (mkProxy groupName) (forget defs)

    pure (JFun groupFun :: map JFun proxys, concat imps)
  where
    mkProxy : JName -> (Name, FC, NamedDef) -> Maybe Fun
    mkProxy grp (fn, _, (MkNmFun args x)) =
        Just $ Fun.untyped (Idr fn) NotInline (map Idr args) Nothing
            (App (Var grp) $ call "Val" [Quote $ Var $ Lbl fn] :: map (Var . Idr) args)
    mkProxy grp (fn, _, _) = Nothing

moduleTrie : List (Name, FC, NamedDef) -> StringTrie (List Stmt)
moduleTrie ns = foldl (\acc, (n, _, def) =>
    let (mod, un) = splitNS n
        stmt = case def of
            MkNmCon _ ar _ => JStruct $ Struct.untyped un (map (("v" ++) . show) (0..=ar))
            _ => Declare un
        in insertWith (reverse $ unsafeUnfoldNamespace mod) ((stmt ::) . fromMaybe []) acc) empty ns

toModules : StringTrie (List Stmt) -> List Stmt -> List Stmt
toModules trie acc =
    let
        acc : List Stmt := maybe acc
            ((++ acc) . map (\(mod, trie) => Module mod (toModules trie [])) . toList)
            $ fromThat trie.node -- add modules
        acc : List Stmt := maybe acc
            (++ acc) $ fromThis trie.node -- add functions
        in acc

export
declare : List (Name, FC, NamedDef) -> List Stmt
declare ns = toModules (moduleTrie ns) []
