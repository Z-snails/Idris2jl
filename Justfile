idris2jl := `pwd` / "build/exec/idris2jl"

build:
    pack build idris2jl.ipkg

test:
    cd tests && nu run.nu {{idris2jl}}

bench:
    cd bench && nu run.nu {{idris2jl}}
