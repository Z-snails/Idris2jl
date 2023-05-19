module Compiler.Julia

import Core.CompileExpr
import Core.Context
import Core.Core
import Core.Directory
import Core.Name
import Compiler.Common
import Libraries.Utils.Path
import Libraries.Data.String.Builder
import Data.List
import Data.Vect
import Idris.Syntax
import Idris.Version
import System
import System.File
import System.Directory
import Compiler.Julia.Compile
import Compiler.Julia.Header
import Compiler.Julia.Printer
import Compiler.Julia.Syntax
import Compiler.Julia.TailRec
import Compiler.Julia.Utils

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

portable : Ref Ctxt Defs => Core Bool
portable = do
    ds <- getDirectives (Other "julia")
    pure $ "portable" `elem` ds

copyDataFiles : Ref Ctxt Defs => (outDir : String) -> (exe : String) -> Core String
copyDataFiles outDir exe = do
    let files = ["support.jl", "flexnum.jl"]
        appDirRel = exe ++ "_app"
        appDir = outDir </> appDirRel
    Right () <- coreLift $ createDir appDir
        | Left e => throw (FileErr appDir e)
    for_ files $ \f => do
        src <- findDataFile "julia/Idris/src/\{f}"
        let dest = appDir </> f
        Right () <- coreLift $ copyFile src (appDir </> f)
            | Left (e, _) => throw (FileErr dest e)
        pure ()
    pure "module Idris include(\"./\{appDirRel}/support.jl\") end"

includeDataFiles : Ref Ctxt Defs => Core String
includeDataFiles = do
    incl <- findDataFile "julia/Idris"
    pure "Base.push!(Base.LOAD_PATH, \"\{incl}\")\nimport Idris"

compile : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String -> ClosedTerm -> String -> Core (Maybe String)
compile _ _ outDir tmpDir tm exe = do
    let outFile = outDir </> exe

    -- Compiling functions
    cdata <- getCompileData False Cases tm
    let ndefs = renameMainDef <$> cdata.namedDefs
        mainExpr = renameMainExp $ forget cdata.mainExpr
        decls = declare ndefs
        Just gs = mkCallGroups ((mainName, EmptyFC, MkNmFun [] mainExpr) :: ndefs)
            | Nothing => unreachable (__LOC__)
    _ <- newRef GroupNum 0
    (fs, imps) <- unzip <$> traverse Compile.group gs

    -- Support files
    support <- if !portable
        then copyDataFiles outDir exe
        else includeDataFiles

    let ds = build $ sepBy "\n"
            [ fromString header
            , fromString support
            , sepBy "\n" $ getImport <$> nub (join imps)
            , sepBy "\n" $ jstmt <$> decls
            , sepBy "\n" $ fs >>= map jstmt
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
    Just out <- compile c s tmpDir tmpDir tm "_tmp_julia"
        | Nothing => throw $ InternalError "error compiling code"
    Just jl <- locateJulia
        | Nothing => coreLift_ $ system [out]
    coreLift_ $ run [jl, out]

export
julia : Codegen
julia = MkCG compile interpret Nothing Nothing
