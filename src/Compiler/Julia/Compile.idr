module Compiler.Julia.Compile

import Compiler.Julia.Syntax
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
import Libraries.Data.StringMap
import Libraries.Data.StringTrie

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

expr : NamedCExp -> StateT Int (Either (FC, String)) JExpr
mkConCase : FC -> JExpr -> List NamedConAlt -> Maybe NamedCExp -> StateT Int (Either (FC, String)) JExpr
mkConstCase : FC -> JExpr -> List NamedConstAlt -> Maybe NamedCExp -> StateT Int (Either (FC, String)) JExpr

expr (NmLocal fc n) = pure $ Var n
expr (NmRef fc n) = pure $ Var n
expr (NmLam fc n y) = pure $ Lam n !(expr y)
expr (NmLet fc n y z) = pure $ mkLet (n, Nothing, !(expr y)) !(expr z)
expr (NmApp fc x xs) = pure $ App !(expr x) !(traverse expr xs)
expr (NmCon fc n x tag xs) = pure $ App (Var n) !(traverse expr xs)
expr (NmOp fc f xs) = if isCompare f
    then pure $ App (JName "Int") [PrimOp f !(traverse expr xs)]
    else pure $ PrimOp f !(traverse expr xs)
expr (NmExtPrim fc p xs) = lift $ Left (fc, "not yet implemented")
expr (NmForce fc lz x) = pure $ App (JName "force") [!(expr x)]
expr (NmDelay fc lz x) = pure $ Macro "delay" [!(expr x)]
expr (NmConCase fc sc xs def) = if requiresLet sc
    then do
        v <- MN "sc" <$> state (\x => (x + 1, x))
        pure $ Let (singleton (v, Nothing, !(expr sc))) !(mkConCase fc (Var v) xs def)
    else mkConCase fc !(expr sc) xs def
expr (NmConstCase fc sc xs def) = if requiresLet sc
    then do
        v <- MN "sc" <$> state (\x => (x + 1, x))
        pure $ Let (singleton (v, Nothing, !(expr sc))) !(mkConstCase fc (Var v) xs def)
    else mkConstCase fc !(expr sc) xs def
expr (NmPrimVal fc cst) = pure $ Lit cst
expr (NmErased fc) = pure NothingVal
expr (NmCrash fc str) = pure $ Throw (App (JName "IdrError") [Lit (Str str)])

bindAll : JExpr -> Nat -> List Name -> JExpr -> JExpr
bindAll sc k [] e = e
bindAll sc k (n :: ns) e = mkLet (n, Nothing, Field sc "v\{show k}") (bindAll sc (S k) ns e)

mkConCase fc sc [] Nothing = pure $ Macro "unreachable" [Lit (Str (show fc))]
mkConCase fc sc [] (Just def) = expr def
mkConCase fc sc (MkNConAlt n _ _ as e :: xs) def =
    pure $ IfExpr (sc `IsA` (VarTy n))
        (bindAll sc 0 as !(expr e))
        !(mkConCase fc sc xs def)

mkConstCase fc sc [] Nothing = pure $ Macro "unreachable" [Lit (Str (show fc))]
mkConstCase fc sc [] (Just def) = expr def
mkConstCase fc sc (MkNConstAlt v e :: xs) def =
    pure $ IfExpr (PrimOp (EQ (typeOf v)) [sc, Lit v])
        !(expr e)
        !(mkConstCase fc sc xs def)

juliaType : CFType -> Maybe JType
juliaType CFUnit = Just NothingTy
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
juliaType CFWorld = Just NothingTy
juliaType (CFFun x y) = Just $ CType "Function"
juliaType (CFIORes x) = juliaType x
juliaType (CFStruct str xs) = Nothing
juliaType (CFUser n xs) = Nothing

cType : CFType -> Either String JType
cType CFUnit = pure $ CType "Cvoid"
cType CFInt = pure $ CType "Cint"
cType CFInteger = Left "unsupported type in julia foreign function interface: Integer"
cType CFInt8 = pure $ PrimTy Int8Type
cType CFInt16 = pure $ PrimTy Int16Type
cType CFInt32 = pure $ PrimTy Int32Type
cType CFInt64 = pure $ PrimTy Int64Type
cType CFUnsigned8 = pure $ PrimTy Bits8Type
cType CFUnsigned16 = pure $ PrimTy Bits16Type
cType CFUnsigned32 = pure $ PrimTy Bits32Type
cType CFUnsigned64 = pure $ PrimTy Bits64Type
cType CFString = pure $ CType "Cstring"
cType CFDouble = pure $ CType "double"
cType CFChar = pure $ PrimTy CharType
cType CFPtr = pure voidPtr
cType CFGCPtr = pure voidPtr
cType CFBuffer = pure $ CType "Buffer"
cType CFForeignObj = pure voidPtr
cType CFWorld = pure NothingTy
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
    try : String -> Maybe (Fun, List String)
    try "scheme:blodwen-new-buffer" = Just (MkFun n inl [(MN "len" 0, Just intType)] Nothing $ App (JName "Buffer") [Var $ MN "len" 0], [])
    try "scheme:blodwen-buffer-size" = Just (Fun.untyped n inl [MN "buf" 0] Nothing $ App (JName "length") [Var $ MN "buf" 0], [])
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
            pure (Fun.untyped n inl (fst <$> args) Nothing (App (Embed expr) (Var . fst <$> args)), imps)

        Just ("C", opts) => do
            fun <- case opts of
                    fun ::: [] => Right $ JName fun
                    fun ::: lib :: _ => Right $ Field (App (JName "joinpath") [Macro "__DIR__" [], Lit $ Str lib]) fun
            cargs <- traverse (\(v, ty) => pure $ Annot (Var v) !(mapFst (GenericMsg fc) (cType ty)))
                $ filter (\(_, ty) => case ty of {CFWorld => False; _ => True}) args
            let call = Macro "ccall" [App fun cargs `Annot` !(mapFst (GenericMsg fc) (cType ret))]
                call = case ret of
                    CFString => App (JName "idris_from_Cstring") [call]
                    _ => call
            pure (MkFun n inl (map (\(i, ty) => (i, juliaType ty)) args) Nothing call, [])

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

export
def : Ref Ctxt Defs => (Name, FC, NamedDef) -> Core (Maybe Stmt, List String)
def (n, _, MkNmFun args x) = pure (Just $ JFun $ Fun.untyped n !(inlineable n) args Nothing
    !(liftEither $ mkGenericMsg $ evalStateT 0 (expr x)), [])
def (n, _, MkNmCon tag arity nt) = pure (Nothing, [])
def (n, fc, MkNmForeign ccs fargs ret) = mapFst (Just . JFun) <$> liftEither (foreign fc n !(inlineable n) ccs fargs ret)
def (n, _, MkNmError x) = pure (Just $ JFun $ Fun.untyped n !(inlineable n) [] (Just $ UN Underscore)
    !(liftEither $ mkGenericMsg $ evalStateT 0 (expr x)), [])

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
