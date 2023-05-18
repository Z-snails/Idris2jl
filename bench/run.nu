#!/bin/env nu

let benches = ["bernouilli.idr"]
let cgs = ["julia" "chez" "racket"]

def main [
    idris2: path
    output = "stdout"
] {
    let results = ($benches | each {|bench|
        let res = ($cgs | each {|cg|
            let out = ($bench | str replace -s ".idr" $"_($cg)")
            print $"($idris2) --cg ($cg) -o ($out) ($bench)"
            ^$idris2 --cg $cg -o $out $bench
            let time = (timeit { ^$"./build/exec/($out)" })
            { codegen: $cg, time: $time }
        })
        { name: $bench, times: $res }
    })
    match $output {
        "stdout" => {
            for bench in $results {
                print --no-newline "===== " $bench.name " =====" (char newline)
                for time in $bench.times {
                    print --no-newline "  " $time.codegen " took: " $time.time (char newline)
                }
            }
        }
        _ => {
            let span = (metadata $output).span
            error make { msg: "output must be one of \"stdout\" or \"json\"", label: { text: "here", start: $span.start, end: $span.end } }
        }
    }
}
