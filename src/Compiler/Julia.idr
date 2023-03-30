module Compiler.Julia

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.Name
import Compiler.Common
import Compiler.Generated
import Libraries.Utils.Path
import Libraries.Data.String.Builder
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
    if isnothing(x.gen)
        return x.val
    else
        @atomic x.val = x.gen()
        x.gen = nothing
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

function idris_wait(thread)
    wait(thread)
    return
end

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
    (ds, imps) <- unzip <$> traverse Compile.def ((mainName, EmptyFC, MkNmFun [] (forget cdata.mainExpr)) :: cdata.namedDefs)
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
