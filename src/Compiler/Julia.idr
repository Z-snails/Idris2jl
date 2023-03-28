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

interpret : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
interpret _ _ _ _ = throw $ Fatal $ GenericMsg EmptyFC "interpret not yet implemented"

export
julia : Codegen
julia = MkCG compile interpret Nothing Nothing
