macro tailcall(f, args...)
    return :($(esc(:args)) = ($args); @goto $(esc(f)))
end

function isOdd_isEven(f::Symbol, args::Vararg)
    args = args
    if f === :isOdd
        @goto isOdd
    elseif f === :isEven
        @goto isEven
    else
        error("oops")
    end

    @label isOdd
    let
        x = args[1]
        return x == 0 ? false : (args = (x - 1,); @goto isEven)
    end

    @label isEven
    let
        x = args[1]
        return x == 0 ? true : (args = (x - 1,); @goto isOdd)
    end
end

isOdd(x) = isOdd_isEven(:isOdd, x)
isEven(x) = isOdd_isEven(:isEven, x)

module _Main
function foo end
end

_Main.foo
