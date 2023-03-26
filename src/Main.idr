module Main

import Compiler.Julia
import Idris.Driver
import Compiler.Common

main : IO ()
main = mainWithCodegens [("julia", julia)]
