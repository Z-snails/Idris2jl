def main [idris2: path] {
    ["julia" "chez"] | each {|cg|
        ^$idris2 --cg $cg -o $cg bench.idr
        let time = (timeit { ^$"./build/exec/($cg)" })
        { codegen: $cg, time: $time }
    }
}
