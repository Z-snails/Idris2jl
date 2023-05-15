macro tailrec(fns...)
    return :()
end

function foo(::Val{f}, args...) where {f}
    @goto f
    @label foo_1
    return 1
    @label foo_2
    return 2
end


