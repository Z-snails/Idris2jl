module Compiler.Julia.Printer

import Core.CompileExpr
import Core.Name
import Core.TT
import Compiler.Julia.Syntax
import Data.List
import Data.List1
import Data.Vect
import Libraries.Data.String.Builder

escape : String -> String
escape = fastConcat . map escapeChar . fastUnpack
where
    allowedChars : List Char
    allowedChars = []
    escapeChar : Char -> String
    escapeChar c = if isAlphaNum c || (c `elem` allowedChars)
        then cast c
        else "_u\{show $ ord c}"

parameters {default False isLabel : Bool}
    export
    name : Name -> Builder
    name (NS mi n) =
        let sep = if isLabel then "_" else "."
         in fromString (showNSWithSep sep mi) ++ fromString sep ++ name n
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

jname : JName -> Builder
jname (Idr n) = name n
jname (Lbl n) = name {isLabel = True} n
jname (Raw str) = fromString str

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
jtype (VarTy n) = jname n
jtype (AppTy f xs) = jname f ++ "{" ++ sepBy "," (map jtype xs) ++ "}"

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

isFloating : PrimType -> Bool
isFloating DoubleType = True
isFloating _ = False

-- Defined below
jexpr : (needsAtom : Bool) -> JExpr -> Builder

jbinop : Bool -> Builder -> Vect 2 JExpr -> Builder
jbinop p op [x, y] = paren p $ jexpr True x ++ " " ++ op ++ " " ++ jexpr True y

isPrintable : Char -> Bool
isPrintable c = '!' <= c && c <= '~'

escapeChar : Char -> (isString : Bool) -> Builder
escapeChar '$' _ = "\\$"
escapeChar '\'' False = "\\'"
escapeChar '"' True = "\\\""
escapeChar '\\' _ = "\\\\"
escapeChar c _ = if isPrintable c
    then fromString $ cast c
    else "\\U" ++ showHex (ord c) True
  where
    hex : Int -> Char
    hex x = if x < 10
        then chr $ x + ord '0'
        else chr $ x - 10 + ord 'a'

    showHex : Int -> (firstChar : Bool) -> Builder
    showHex 0 False = ""
    showHex 0 True = "0"
    showHex x _ = showHex (x `div` 16) False ++ fromString (cast $ hex (x `mod` 16))

escapeString : String -> Builder
escapeString x = concat (map (flip escapeChar True) $ unpack x)

jconst : Constant -> Builder
jconst (I i) = "Int(" ++ showB i ++ ")"
jconst (I8 i) = "Int8(" ++ showB i ++ ")"
jconst (I16 i) = "Int16(" ++ showB i ++ ")"
jconst (I32 i) = "Int32(" ++ showB i ++ ")"
jconst (I64 i) = "Int64(" ++ showB i ++ ")"
jconst (BI i) = "Idris.flex\"" ++ showB i ++ "\""
jconst (B8 m) = "UInt8(" ++ showB m ++ ")"
jconst (B16 m) = "UInt16(" ++ showB m ++ ")"
jconst (B32 m) = "UInt32(" ++ showB m ++ ")"
jconst (B64 m) = "UInt64(" ++ showB m ++ ")"
jconst (Str str) = "\"" ++ escapeString str ++ "\""
jconst (Ch c) = "'" ++ escapeChar c False ++ "'"
jconst (Db x) = "Int(" ++ showB x ++ ")"
jconst (PrT pty) = "nothing"
jconst WorldVal = "nothing"

tuple : List Builder -> Builder
tuple [] = "()"
tuple [x] = "(" ++ x ++ ",)"
tuple xs = "(" ++ sepBy ", " xs ++ ")"

pattern : Pattern -> Builder
pattern (PVar x mty) = jname x ++ maybe "" (\ty => "::" ++ jtype ty) mty
pattern (PTuple xs) = tuple $ map pattern xs

jprimop : Bool -> PrimFn ar -> Vect ar JExpr -> Builder

jexpr p (Var n) = jname n
jexpr p (Annot x ty) = jexpr True x ++ "::" ++ jtype ty
jexpr p (IsA x ty) = app "isa" [jexpr False x, jtype ty]
jexpr p (Ty ty) = jtype ty
jexpr p (App x xs) = app (jexpr True x) (map (jexpr False) xs)
jexpr p (Macro {ns} str xs) =
    let m = case ns of
            Nothing => "@" ++ fromString str
            Just ns => fromString ns ++ ".@" ++ fromString str
     in app m (map (jexpr False) xs)
jexpr p (Lam n x) = paren p $ name n ++ " -> " ++ jexpr False x
jexpr p (Let xs x) = paren p $
    "let " ++
    concat (map (\(pat, x) =>
        pattern pat ++ " = " ++ jexpr False x ++ "; ") xs) ++
    jexpr False x ++
    " end"
jexpr p (Throw x) = app "error" [jexpr False x]
jexpr p (IfExpr cond on_true on_false) = paren p $
    jexpr True cond ++ " ? " ++
    jexpr True on_true ++ " : " ++
    jexpr True on_false
jexpr p (Sequence es) = "(" ++ sepBy "; " (jexpr False <$> forget es) ++ ")"
jexpr p (And x y) = paren p $ jexpr True x ++ " && " ++ jexpr True y
jexpr p (Lit cst) = jconst cst
jexpr p (PrimOp f xs) = jprimop p f xs
jexpr p (Tuple xs) = tuple $ map (jexpr False) xs
jexpr p (Field x str) = jexpr True x ++ "." ++ fromString str
jexpr p (Embed x) = paren True $ fromString x
jexpr p (Assign pat val) = paren p $ pattern pat ++ " = " ++ jexpr False val
jexpr p (Quote q) = ":" ++ jexpr True q

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
jprimop p (Cast _ to) [x] = app "Idris.cast" [primType to, jexpr False x]
jprimop p BelieveMe [_, _, x] = app "Idris.believe_me" [jexpr False x]
jprimop p Crash [_, msg] = app "Idris.crash" [jexpr False msg]

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
    ++ jname x.name
    ++ "(" ++ args ", " jname x.args
    ++ maybe "" (\va =>
        (if isNil x.args then "" else ", ")
        ++ jname va ++ "...") x.varargs ++ ")"
    ++ (if isNil x.whereBlock then "" else mkWhereBlock x.whereBlock)
    ++ " = "
    ++ jexpr False x.body
  where
    mkWhereBlock : List (JName, Maybe JType) -> Builder
    mkWhereBlock xs =
        " where {"
        ++ sepBy "," (map (\(n, mty) =>
            maybe (jname n) (\ty => jname n ++ "<:" ++ jtype ty) mty) xs)
        ++ "}"
jstmt (Declare fn) = "function " ++ name fn ++ " end # " ++ showB fn
jstmt (Module n ss) =
    "module " ++ fromString n ++ "\n"
    ++ sepBy "\n" (map jstmt ss) ++ "\n"
    ++ "end # module " ++ fromString n
