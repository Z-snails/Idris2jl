module Compiler.Julia.Syntax

import Core.TT
import Core.CompileExpr
import Data.List1
import Data.Vect

public export
data JName : Type where
    Idr : Name -> JName
    Lbl : Name -> JName
    Raw : String -> JName

export
FromString JName where
    fromString = Raw

export
Show JName where
    show (Idr n) = show n
    show (Lbl n) = show n
    show (Raw n) = n

export
underscore : JName
underscore = Idr $ UN Underscore

export
asLabel : JName -> JName
asLabel (Idr n) = Lbl n
asLabel n = n

public export
data JType : Type where
    PrimTy : PrimType -> JType
    VarTy : JName -> JType
    AppTy : JName -> List JType -> JType

%name JType ty

export
voidPtr : JType
voidPtr = AppTy "Ptr" [VarTy "Cvoid"]

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
    PVar : JName -> Maybe JType -> Pattern
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
    Let : List1 (Pattern, JExpr) -> JExpr -> JExpr
    Throw : JExpr -> JExpr
    IfExpr : (cond : JExpr) -> (on_true : JExpr) -> (on_false : JExpr) -> JExpr
    Sequence : List1 JExpr -> JExpr
    And : JExpr -> JExpr -> JExpr

    -- primitives
    Lit : Constant -> JExpr
    PrimOp : PrimFn ar -> Vect ar JExpr -> JExpr
    Tuple : List JExpr -> JExpr

    -- misc
    Field : JExpr -> String -> JExpr
    Embed : String -> JExpr
    Assign : Pattern -> JExpr -> JExpr
    Quote : JExpr -> JExpr

public export
mkLet : (Name, Maybe JType, JExpr) -> JExpr -> JExpr
mkLet (n, mty, e) (Let ys sc) = Let ((PVar (Idr n) mty, e) ::: forget ys) sc
mkLet (n, mty, e) sc = Let (singleton (PVar (Idr n) mty, e)) sc

export
isEqual : JExpr -> JExpr -> JExpr
isEqual x y = PrimOp (EQ IntType) [x, y]

public export
record Fun where
    constructor MkFun
    name : JName
    inline : InlineOk
    args : List (JName, Maybe JType)
    varargs : Maybe JName
    body : JExpr
    whereBlock : List (JName, Maybe JType)

namespace Fun
    public export
    untyped : JName -> InlineOk -> List JName -> Maybe JName -> JExpr -> Fun
    untyped n inl ns va x = MkFun n inl (map (, Nothing) ns) va x []

public export
data Stmt : Type where
    JStruct : Struct -> Stmt
    JFun : Fun -> Stmt
    Declare : Name -> Stmt
    Module : String -> List Stmt -> Stmt
