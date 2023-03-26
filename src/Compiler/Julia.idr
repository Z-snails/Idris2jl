module Compiler.Julia

import Core.TT
import Core.Core
import Core.CompileExpr
import Core.Context
import Core.Options
import Compiler.CompileExpr
import Compiler.Common
import Compiler.Generated
import Control.Monad.State
import Data.List
import Data.List1
import Data.String
import Data.These
import Data.Vect
import Libraries.Utils.Path
import Libraries.Data.String.Builder
import Libraries.Data.StringTrie
import Libraries.Data.StringMap
import Idris.Syntax
import Idris.Version
import System.File

-- Utils
rangeNonInclusive : Integral a => Ord a => a -> a -> List a
rangeNonInclusive low hi = if low < hi
    then low :: rangeNonInclusive (low + 1) hi
    else []

infix 0 ..=

%inline
(..=) : Integral a => Ord a => a -> a -> List a
(..=) = rangeNonInclusive

enumerate : List a -> List (Nat, a)
enumerate xs = enum 0 xs
  where
    enum : Nat -> List a -> List (Nat, a)
    enum i [] = []
    enum i (x :: xs) = (i, x) :: enum (S i) xs

stripPrefix : String -> String -> Maybe String
stripPrefix pre x = if pre `isPrefixOf` x
    then Just $ substr (length pre) (length x) x
    else Nothing

liftEither : Either Error a -> Core a
liftEither (Right x) = pure x
liftEither (Left err) = coreFail err

-- Types

data JType : Type where
    PrimTy : PrimType -> JType
    NothingTy : JType
    VarTy : Name -> JType
    CType : String -> JType

%name JType ty

voidPtr : JType
voidPtr = CType "Ptr{Cvoid}"

intType : JType
intType = PrimTy IntType

record Struct where
    constructor MkStruct
    name : Name
    args : List (String, Maybe JType)

namespace Struct
    public export
    untyped : Name -> List String -> Struct
    untyped name args = MkStruct { name, args = map (, Nothing) args }

data JExpr : Type where
    -- variables
    Var : Name -> JExpr
    JName : String -> JExpr

    -- types
    Annot : JExpr -> JType -> JExpr
    IsA : JExpr -> JType -> JExpr
    Ty : JType -> JExpr

    -- control flow
    App : JExpr -> List JExpr -> JExpr
    Macro : String -> List JExpr -> JExpr
    Lam : Name -> JExpr -> JExpr
    Let : List1 (Name, Maybe JType, JExpr) -> JExpr -> JExpr
    Throw : JExpr -> JExpr
    IfExpr : (cond : JExpr) -> (on_true : JExpr) -> (on_false : JExpr) -> JExpr

    -- primitives
    Lit : Constant -> JExpr
    PrimOp : PrimFn ar -> Vect ar JExpr -> JExpr

    -- misc
    NothingVal : JExpr
    Field : JExpr -> String -> JExpr
    Embed : String -> JExpr

public export
mkLet : (Name, Maybe JType, JExpr) -> JExpr -> JExpr
mkLet x (Let ys e) = Let (x ::: forget ys) e
mkLet x e = Let (singleton x) e

record Fun where
    constructor MkFun
    name : Name
    inline : InlineOk
    args : List (Name, Maybe JType)
    varargs : Maybe Name
    body : JExpr

namespace Fun
    public export
    untyped : Name -> InlineOk -> List Name -> Maybe Name -> JExpr -> Fun
    untyped n inl ns va x = MkFun n inl (map (, Nothing) ns) va x

public export
data Stmt : Type where
    JStruct : Struct -> Stmt
    JFun : Fun -> Stmt
    Declare : Name -> Stmt
    Module : String -> List Stmt -> Stmt

-- From NamedCExp

namespace Compile
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

isFloating : PrimType -> Bool
isFloating DoubleType = True
isFloating _ = False

-- Pretty printing
namespace Print
    escape : String -> String
    escape = fastConcat . map escapeChar . fastUnpack
    where
        allowedChars : List Char
        allowedChars = []
        escapeChar : Char -> String
        escapeChar c = if isAlphaNum c || (c `elem` allowedChars)
            then cast c
            else "_u\{show $ ord c}"

    export
    name : Name -> Builder
    name (NS mi n) = fromString (showNSWithSep "." mi) ++ "." ++ name n
    name (UN (Basic str)) = fromString (escape str)
    name (UN (Field str)) = "f_" ++ fromString (escape str)
    name (UN Underscore) = "_"
    name (MN str i) = "_" ++ fromString str ++ "_" ++ showB i
    name (PV n i) = "pv_" ++ showB i ++ "_" ++ name n
    name (DN str n) = name n
    name (Nested (x, y) n) = "n_" ++ showB x ++ "_" ++ showB y ++ "_" ++ name n
    name (CaseBlock str i) = "cb_" ++ fromString str ++ "_" ++ showB i
    name (WithBlock str i) = "wb_" ++ fromString str ++ "_" ++ showB i
    name (Resolved i) = assert_total $ idris_crash "unreachable"

    primType : PrimType -> Builder
    primType IntType = "Int"
    primType Int8Type = "Int8"
    primType Int16Type = "Int16"
    primType Int32Type = "Int32"
    primType Int64Type = "Int64"
    primType IntegerType = "BigInt"
    primType Bits8Type = "UInt8"
    primType Bits16Type = "UInt16"
    primType Bits32Type = "UInt32"
    primType Bits64Type = "UInt64"
    primType StringType = "String"
    primType CharType = "Char"
    primType DoubleType = "Float64"
    primType WorldType = "Nothing"

    jtype : JType -> Builder
    jtype (PrimTy pty) = primType pty
    jtype NothingTy = "Nothing"
    jtype (VarTy n) = name n
    jtype (CType x) = fromString x

    args : (sep : String) -> (a -> Builder) -> List (a, Maybe JType) -> Builder
    args sep f xs =
        sepBy sep (map (\(x, mty) =>
            f x ++ maybe "" (("::" ++) . jtype) mty) xs)

    paren : Bool -> Builder -> Builder
    paren True x = "(" ++ x ++ ")"
    paren False x = x

    export
    app : Builder -> List Builder -> Builder
    app fn xs = fn ++ "(" ++ sepBy ", " xs ++ ")"

    -- Defined below
    jexpr : (needsAtom : Bool) -> JExpr -> Builder

    jbinop : Bool -> Builder -> Vect 2 JExpr -> Builder
    jbinop p op [x, y] = paren p $ jexpr True x ++ " " ++ op ++ " " ++ jexpr True y

    jconst : Constant -> Builder
    jconst (I i) = "Int(" ++ showB i ++ ")"
    jconst (I8 i) = "Int8(" ++ showB i ++ ")"
    jconst (I16 i) = "Int16(" ++ showB i ++ ")"
    jconst (I32 i) = "Int32(" ++ showB i ++ ")"
    jconst (I64 i) = "Int64(" ++ showB i ++ ")"
    jconst (BI i) = "big\"" ++ showB i ++ "\""
    jconst (B8 m) = "UInt8(" ++ showB m ++ ")"
    jconst (B16 m) = "UInt16(" ++ showB m ++ ")"
    jconst (B32 m) = "UInt32(" ++ showB m ++ ")"
    jconst (B64 m) = "UInt64(" ++ showB m ++ ")"
    jconst (Str str) = showB str
    jconst (Ch c) = showB c
    jconst (Db x) = "Int(" ++ showB x ++ ")"
    jconst (PrT pty) = "nothing"
    jconst WorldVal = "nothing"

    jprimop : Bool -> PrimFn ar -> Vect ar JExpr -> Builder

    jexpr p (Var n) = name n
    jexpr p (JName str) = fromString str
    jexpr p (Annot x ty) = jexpr True x ++ "::" ++ jtype ty
    jexpr p (IsA x ty) = app "isa" [jexpr False x, jtype ty]
    jexpr p (Ty ty) = jtype ty
    jexpr p (App x xs) = app (jexpr True x) (map (jexpr False) xs)
    jexpr p (Macro str xs) = app ("@" ++ fromString str) (map (jexpr False) xs)
    jexpr p (Lam n x) = paren p $ name n ++ " -> " ++ jexpr False x
    jexpr p (Let xs x) = paren p $
        "let " ++
        concat (map (\(n, mty, x) =>
            name n ++ maybe "" (("::" ++) . jtype) mty ++ " = " ++ jexpr False x ++ "; ") xs) ++
        jexpr False x ++
        " end"
    jexpr p (Throw x) = app "error" [jexpr False x]
    jexpr p (IfExpr cond on_true on_false) = paren p $
        jexpr True cond ++ " ? " ++
        jexpr True on_true ++ " : " ++
        jexpr True on_false
    jexpr p (Lit cst) = jconst cst
    jexpr p (PrimOp f xs) = jprimop p f xs
    jexpr p NothingVal = "nothing"
    jexpr p (Field x str) = jexpr True x ++ "." ++ fromString str
    jexpr p (Embed x) = paren True $ fromString x

    jprimop p (Add ty) xs = jbinop p "+" xs
    jprimop p (Sub ty) xs = jbinop p "-" xs
    jprimop p (Mul ty) xs = jbinop p "*" xs
    jprimop p (Div ty) [x, y] = if isFloating ty
        then jbinop p "/" [x, y]
        else "div(" ++ jexpr False x ++ ", " ++ jexpr True y ++ ")"
    jprimop p (Mod ty) xs = jbinop p "%" xs
    jprimop p (Neg ty) [x] = "(-" ++ jexpr True x ++ ")"
    jprimop p (ShiftL ty) xs = jbinop p "<<" xs
    jprimop p (ShiftR ty) xs = jbinop p ">>" xs
    jprimop p (BAnd ty) xs = jbinop p "&" xs
    jprimop p (BOr ty) xs = jbinop p "|" xs
    jprimop p (BXOr ty) [x, y] = app "xor" [jexpr False x, jexpr False y]
    jprimop p (LT ty) xs = jbinop p "<" xs
    jprimop p (LTE ty) xs = jbinop p "<=" xs
    jprimop p (EQ ty) xs = jbinop p "==" xs
    jprimop p (GTE ty) xs = jbinop p ">=" xs
    jprimop p (GT ty) xs = jbinop p ">" xs
    jprimop p StrLength [x] = app "length" [jexpr False x]
    jprimop p StrHead [x] = jexpr True x ++ "[1]"
    jprimop p StrTail [x] = app "SubString" [jexpr False x, "2"]
    jprimop p StrIndex [x, i] = app "idris_StrIndex" [jexpr False x, jexpr False i]
    jprimop p StrCons xs = jbinop p "*" xs
    jprimop p StrAppend xs = jbinop p "*" xs
    jprimop p StrReverse [x] = app "reverse" [jexpr False x]
    jprimop p StrSubstr [start, len, x] = app "idris_StrSubstr" [jexpr False start, jexpr False len, jexpr False x]
    jprimop p DoubleExp [x] = app "exp" [jexpr False x]
    jprimop p DoubleLog [x] = app "log" [jexpr False x]
    jprimop p DoublePow xs = jbinop p "^" xs
    jprimop p DoubleSin [x] = app "sin" [jexpr False x]
    jprimop p DoubleCos [x] = app "cos" [jexpr False x]
    jprimop p DoubleTan [x] = app "tan" [jexpr False x]
    jprimop p DoubleASin [x] = app "asin" [jexpr False x]
    jprimop p DoubleACos [x] = app "acos" [jexpr False x]
    jprimop p DoubleATan [x] = app "atan" [jexpr False x]
    jprimop p DoubleSqrt [x] = app "sqrt" [jexpr False x]
    jprimop p DoubleFloor [x] = app "floor" [jexpr False x]
    jprimop p DoubleCeiling [x] = app "ceil" [jexpr False x]
    jprimop p (Cast _ to) [x] = app "idris_cast" [primType to, jexpr False x]
    jprimop p BelieveMe [_, _, x] = app "believe_me" [jexpr False x]
    jprimop p Crash [_, msg] = app "idris_crash" [jexpr False msg]

    export
    jstmt : Stmt -> Builder
    jstmt (JStruct x) =
        "# " ++ showB x.name ++ "\n"
        ++ "struct " ++ name x.name ++ " "
        ++ args "; " fromString x.args
        ++ if isNil x.args then "end" else " end"
    jstmt (JFun x) =
        "# " ++ showB x.name ++ "\n"
        ++ case x.inline of {YesInline => "@inline "; NotInline => ""}
        ++ name x.name
        ++ "(" ++ args ", " name x.args
        ++ maybe "" (\va =>
            (if isNil x.args then "" else ", ")
            ++ name va ++ "...") x.varargs ++ ") = "
        ++ jexpr False x.body 
    jstmt (Declare fn) = "function " ++ name fn ++ " end # " ++ showB fn
    jstmt (Module n ss) =
        "module " ++ fromString n ++ "\n"
        ++ sepBy "\n" (map jstmt ss) ++ "\n"
        ++ "end # module " ++ fromString n

header : String
header = """
#!/bin/env julia
# \{generatedString "julia"}

function believe_me(x)
    return x
end

struct Unreachable <: Exception
    location::String
end

macro unreachable(location)
    :(throw(Unreachable($(esc(location)))))
end

# From Integer
idris_cast(::Type{to}, x::Integer) where { to <: Integer } = unsafe_trunc(to, x)
idris_cast(::Type{String}, x::Integer) = string(x)
idris_cast(::Type{Float64}, x::Integer) = Float64(x)

# From Float
idris_cast(::Type{to}, x::AbstractFloat) where { to <: Integer } = unsafe_trunc(to, x)
idris_cast(::Type{String}, x::AbstractFloat) = string(x)

# From Char
idris_cast(::Type{String}, x::Char) = string(x)

# From String
idris_cast(::Type{to}, x::String) where { to <: Integer } = parse(to, x)
idris_cast(::Type{Float64}, x::String) = parse(Float64, x)

mutable struct Delay
    @atomic gen::Union{Function,Nothing}
    val::Union{Any,Nothing}
end

macro delay(x)
    :(Delay(() -> $(esc(x)), nothing))
end

function force(x::Delay)
    if isnothing(x.gen)
        return x.val
    else
        @atomic x.val = x.gen()
        x.gen = nothing
        return x.val
    end
end

function idris_crash(msg::String)
    print(msg)
    exit(1)
end

struct Buffer
    ptr::Ptr{Cvoid}
end

Base.cconvert(::Type{Ptr{Cvoid}}, x::Buffer) = x.ptr

"""

mainName : Name
mainName = MN "main" 0

footer : Builder
footer = sepBy "\n"
    [ app (name mainName) []
    ] ++ "\n"

copySupportSO : Ref Ctxt Defs => Core ()
copySupportSO = do
    dirs <- getDirs
    (path, support) <- findSupport ["libidris2_support.so", "libidris2_support.dylib", "libidris2_support.dll"] $
        dirs.prefix_dir </> "idris2-\{showVersion False version}" </> "lib"
    Right () <- coreLift $ copyFile path (execBuildDir dirs </> support)
        | Left err => throw $ InternalError "unable to copy support library: \{show err}"
    pure ()
  where
    findSupport : (libs : List String) -> String -> Core (String, String)
    findSupport [] dir = throw $ InternalError "unable to locate any support library"
    findSupport (l :: ls) dir = do
        let path = dir </> l
        if !(coreLift $ exists path)
            then pure (path, l)
            else findSupport ls dir

getImport : String -> Builder
getImport str = "import " ++ fromString str

compile : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String -> ClosedTerm -> String -> Core (Maybe String)
compile _ _ outDir tmpDir tm exe = do
    let outFile = outDir </> exe
    cdata <- getCompileData False Cases tm
    let decls = declare cdata.namedDefs
    (ds, imps) <- unzip <$> traverse def ((mainName, EmptyFC, MkNmFun [] (forget cdata.mainExpr)) :: cdata.namedDefs)
    let ds = build $ sepBy "\n"
            [ fromString header
            , sepBy "\n" $ getImport <$> nub (join imps)
            , sepBy "\n" $ jstmt <$> decls
            , sepBy "\n" $ mapMaybe (map jstmt) ds
            , footer
            ]
    writeFile outFile ds

    let rwx = [Read, Write, Execute]
    coreLift_ $ chmod outFile (MkPermissions rwx rwx rwx)

    copySupportSO

    pure (Just outFile)

interpret : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
interpret _ _ _ _ = throw $ Fatal $ GenericMsg EmptyFC "interpret not yet implemented"

export
julia : Codegen
julia = MkCG compile interpret Nothing Nothing
