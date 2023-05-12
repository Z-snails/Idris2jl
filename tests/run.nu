def main [idris2jl: path] {
    for test in (ls | where type == "dir" | get name) {
        cd $test
        sh run $idris2jl
        if (open --raw output) != (open --raw expected) {
            print $"error running test ($test)"
            diff --color=auto output expected
            exit 1
        }
    }
}
