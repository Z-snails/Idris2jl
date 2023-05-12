module Compiler.Julia.Syntax

import Core.TT
import Core.CompileExpr
import Data.List1
import Data.Vect

public export
data JName : Type where
    Idr : Name -> JName
    Raw : String -> JName

public export
data JType : Type where
    PrimTy : PrimType -> JType
    VarTy : JName -> JType

%name JType ty

export
voidPtr : JType
voidPtr = VarTy $ Raw "Ptr{Cvoid}"

export
intType : JType
intType = PrimTy IntType

public export
record Struct where
    constructor MkStruct
    name : Name
    args : List (String, Maybe JType)

namespace Struct
    public export
    untyped : Name -> List String -> Struct
    untyped name args = MkStruct { name, args = map (, Nothing) args }

public export
data Pattern : Type where
    PVar : JName -> Pattern
    PTuple : List Pattern -> Pattern

public export
data JExpr : Type where
    -- variables
    Var : JName -> JExpr

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
    Sequence : List1 JExpr -> JExpr

    -- primitives
    Lit : Constant -> JExpr
    PrimOp : PrimFn ar -> Vect ar JExpr -> JExpr
    Tuple : List JExpr -> JExpr

    -- misc
    Field : JExpr -> String -> JExpr
    Embed : String -> JExpr

public export
mkLet : (Name, Maybe JType, JExpr) -> JExpr -> JExpr
mkLet x (Let ys e) = Let (x ::: forget ys) e
mkLet x e = Let (singleton x) e

public export
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
