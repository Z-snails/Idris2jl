# Idris2 Julia backend

Julia is a dynamically typed JIT-compiled language, which aims to emit efficient machine code via LLVM infrastructure.

Compiling Idris 2 to it has 2 main goals:

1. Performance - especially for numeric intesive code
2. Access Julia's many libraries - espcially data science

## Performance

TODO

### Simd

TODO (see `test/src/Simd/AsciiValidator.idr`)

## Libraries/FFI

The julia ffi allows calling any julia code, as well as importing libraries. (see `test/src/Simd/AsciiValidator.idr`)
