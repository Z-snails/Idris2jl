module Compiler.Julia.Header

import Compiler.Generated

export
header : String
header = """
#!/bin/env julia
# \{generatedString "julia"}
"""
