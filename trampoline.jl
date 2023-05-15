macro tailcall(f, args...)
    return :($(esc(:args)) = ($args); @goto $(esc(f)))
end

function isOdd_isEven(::Val{f}, args::Vararg) where {f}
    args = args
    f === :isOdd && @goto(isOdd)
    f === :isEven && @goto isEven
    error("unknown function")

    @label isOdd
    let
        (x,) = args
        return x == 0 ? false : (args = (x - 1,); @goto isEven)
    end

    @label isEven
    let
        (x,) = args
        return x == 0 ? true : (args = (x - 1,); @goto isOdd)
    end
end

isOdd(x) = isOdd_isEven(Val(:isOdd), x)
isEven(x) = isOdd_isEven(Val(:isEven), x)

function natEq(args...)
    @label natEq
    (x, y) = args
    if x == 0 && y == 0
        return true
    elseif x == 0 || y == 0
        return false
    else
        return (args = (x - 1, y - 1); @goto natEq)
    end
end
