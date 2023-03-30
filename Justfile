idris2jl := `pwd` / "build/exec/idris2jl"

test:
    cd tests && IDRIS2JL={{idris2jl}} nu run.nu
