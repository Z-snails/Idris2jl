let idris2jl = $env.IDRIS2JL

for test in (ls | where type == "dir" | get name) {
    cd $test
    sh run $idris2jl
    if (open --raw output) != (open --raw expected) {
        print $"error running test ($test)"
        diff --color=auto output expected
        exit 1
    }
}
