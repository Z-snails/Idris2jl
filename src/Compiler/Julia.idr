module Compiler.Julia

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.Name
import Compiler.Common
import Compiler.Generated
import Libraries.Utils.Path
import Libraries.Data.String.Builder
import Data.Vect
import Idris.Syntax
import Idris.Version
import System
import System.File
import Compiler.Julia.Compile
import Compiler.Julia.Printer
import Compiler.Julia.Syntax
import Compiler.Julia.Utils

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
idris_cast(::Type{to}, x::Integer) where { to <: AbstractFloat } = convert(to, x)

# From Float
idris_cast(::Type{to}, x::AbstractFloat) where { to <: Integer } = unsafe_trunc(to, x)
idris_cast(::Type{String}, x::AbstractFloat) = string(x)

# From Char
idris_cast(::Type{String}, x::Char) = string(x)
idris_cast(::Type{to}, x::Char) where { to <: Integer } = convert(to, x)

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
    if isnothing(@atomic x.gen)
        return x.val
    else
        x.val = x.gen()
        @atomic x.gen = nothing
        return x.val
    end
end

function idris_crash(msg::String)
    print(stderr, msg)
    exit(1)
end

struct Buffer
    ptr::Ptr{Cvoid}
end

Base.cconvert(::Type{Ptr{Cvoid}}, x::Buffer) = x.ptr

@inline notnothing(x) = !isnothing(x)

struct Cons
    fst
    snd
end

function idris_fastUnpack(x::AbstractString)
    acc = nothing
    for c in Iterators.reverse(x)
        acc = Cons(c, acc)
    end
    return acc
end

function idris_listPrint(::Type{T}, xs::Union{Cons,Nothing}) where {T}
    xs::Union{Cons,Nothing} = xs
    if isnothing(xs)
        return ""
    else
        io = IOBuffer()
        while !isnothing(xs)
            print(io, xs.fst::T)
            xs = xs.snd::Union{Cons,Nothing}
        end
        return String(take!(io))
    end
end

@inline function idris_fastPack(xs::Union{Cons,Nothing})
    return idris_listPrint(Char, xs)
end

@inline function idris_fastConcat(xs::Union{Cons,Nothing})
    return idris_listPrint(String, xs)
end

@inline idris_isNull(x::Ptr) = x == C_NULL
@inline idris_getNull() = Ptr{Cvoid}(C_NULL)

function idris_fork(k)
    return Base.Threads.@spawn $k()
end

idris_wait(thread) = (wait(thread); nothing)

mutable struct Mut
    val
end

@inline idris_writeIORef(mut::Mut, val) = (mut.val = val; nothing)

idris_newArray(n, val) = fill!(Vector{Any}(undef, n), val)
@inline idris_arrayGet(arr, idx) = arr[idx + 1]
@inline idris_arraySet(arr, idx, val) = (arr[idx + 1] = val; nothing)

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

renameMain : Name -> Name
renameMain (NS mi n) = NS (renameMainNS mi) (renameMain n)
  where
    renameMainNS : Namespace -> Namespace
    renameMainNS = unsafeFoldNamespace . map (\n => if n == "Main" then "_Main" else n) . unsafeUnfoldNamespace

renameMain (UN un) = UN un
renameMain (MN str i) = MN str i
renameMain (PV n i) = PV (renameMain n) i
renameMain (DN str n) = DN str (renameMain n)
renameMain (Nested x n) = Nested x (renameMain n)
renameMain (CaseBlock str i) = CaseBlock str i
renameMain (WithBlock str i) = WithBlock str i
renameMain (Resolved i) = Resolved i

renameMainExp : NamedCExp -> NamedCExp
renameMainExp (NmLocal fc n1) = NmLocal fc n1 -- locals have not namespaces
renameMainExp (NmRef fc n1) = NmRef fc (renameMain n1)
renameMainExp (NmLam fc x y) = NmLam fc x (renameMainExp y)
renameMainExp (NmLet fc x y z) = NmLet fc x (renameMainExp y) (renameMainExp z)
renameMainExp (NmApp fc x xs) = NmApp fc (renameMainExp x) (renameMainExp <$> xs)
renameMainExp (NmCon fc n1 x tag xs) = NmCon fc (renameMain n1) x tag (renameMainExp <$> xs)
renameMainExp (NmOp fc f xs) = NmOp fc f (renameMainExp <$> xs)
renameMainExp (NmExtPrim fc p xs) = NmExtPrim fc p (renameMainExp <$> xs)
    -- ^ primitive name should be preserved, as this isn't lowered to julia
renameMainExp (NmForce fc lz x) = NmForce fc lz (renameMainExp x)
renameMainExp (NmDelay fc lz x) = NmDelay fc lz (renameMainExp x)
renameMainExp (NmConCase fc sc xs x) =
    NmConCase fc (renameMainExp sc)
        (map (\(MkNConAlt n i tag args exp) => MkNConAlt (renameMain n) i tag args (renameMainExp exp)) xs)
        (renameMainExp <$> x)
renameMainExp (NmConstCase fc sc xs x) = 
    NmConstCase fc (renameMainExp sc)
        (map (\(MkNConstAlt val exp) => MkNConstAlt val (renameMainExp exp)) xs)
        (renameMainExp <$> x)
renameMainExp e@(NmPrimVal {}) = e
renameMainExp e@(NmErased {}) = e
renameMainExp e@(NmCrash {}) = e

renameMainDef : (Name, FC, NamedDef) -> (Name, FC, NamedDef)
renameMainDef (n, fc, def) = (renameMain n, fc, renameMainDef' def)
  where
    renameMainDef' : NamedDef -> NamedDef
    renameMainDef' (MkNmFun args x) = MkNmFun args (renameMainExp x)
    renameMainDef' (MkNmCon tag arity nt) = MkNmCon tag arity nt
    renameMainDef' (MkNmForeign ccs fargs ret) = MkNmForeign ccs fargs ret
    renameMainDef' (MkNmError x) = MkNmError (renameMainExp x)

compile : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String -> ClosedTerm -> String -> Core (Maybe String)
compile _ _ outDir tmpDir tm exe = do
    let outFile = outDir </> exe
    cdata <- getCompileData False Cases tm
    let ndefs = renameMainDef <$> cdata.namedDefs
    let mainExpr = renameMainExp $ forget cdata.mainExpr
    let decls = declare ndefs
    (ds, imps) <- unzip <$> traverse Compile.def ((mainName, EmptyFC, MkNmFun [] mainExpr) :: ndefs)
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

locateJulia : Ref Ctxt Defs => Core (Maybe String)
locateJulia = do
    ds <- getDirectives (Other "julia")
    pure $ findMap (stripPrefix "julia=") ds

interpret : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
interpret c s tmpDir tm = do
    Just out <- compile c s tmpDir tmpDir tm "__tmp_execute"
        | Nothing => throw $ InternalError "error compiling code"
    Just jl <- locateJulia
        | Nothing => coreLift_ $ system [out]
    coreLift_ $ run [jl, out]

export
julia : Codegen
julia = MkCG compile interpret Nothing Nothing
