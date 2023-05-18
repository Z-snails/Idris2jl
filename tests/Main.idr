module Main

import Test.Golden

basic : IO TestPool
basic = testsInDir "basic" (const True) "basics" [] Nothing

main : IO ()
main = runner
    [ !basic
    ]
