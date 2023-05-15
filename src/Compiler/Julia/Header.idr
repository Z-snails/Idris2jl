module Compiler.Julia.Header

import Compiler.Generated

flexnum : String
flexnum = """
module FlexNum
export FlexInt, @flex_str

using Base: BigInt
import Base.==

function is_small(x::BigInt)
    n = x.size
    n == 0 && return true
    abs(n) == 1 && unsafe_load(x.d) < Base.typemax(Int) && return true
    return false
end

unsafe_get_small(x::BigInt) = Base.sign(x.size) * Base.unsafe_trunc(Int, unsafe_load(x.d))

function get_small(x::BigInt)::Union{Int,Nothing}
    n = x.size
    n == 0 && return 0
    abs(n) == 1 && return unsafe_get_small(x)
    return nothing
end

struct FlexInt <: Base.Signed
    int::Int
    big::Union{BigInt,Nothing}
end

@inline FlexInt(x::Int) = FlexInt(x, nothing)
FlexInt(x::BigInt) = FlexInt(0, x)
# FlexNum(x::Base.BigInt) = is_small(x) ? FlexNum(unsafe_get_small(x)) : FlexNum(0, x)

macro flex_str(x)
    val = parse(BigInt, x)
    small = get_small(val)
    if isnothing(small)
        return FlexInt(val)
    else
        return FlexInt(small)
    end
end

@inline is_small(x::FlexInt) = Base.isnothing(x.big)

BigInt(x::FlexInt)::BigInt = is_small(x) ? BigInt(x.int) : x.big

Base.string(n::FlexInt, base::Integer=10, pad::Integer=1) = is_small(n) ? Base.string(n.int, base=base, pad=pad) : Base.string(n.big, base=base, pad=pad)
Base.show(io::IO, x::FlexInt) = Base.print(io, Base.string(x))

macro binop(op)
    return :(
        function $op(x::FlexInt, y::FlexInt)
            is_small(x) && is_small(y) && return FlexInt($op(x.int, y.int))
            is_small(x) && return FlexInt($op(x.int, y.big::BigInt))
            is_small(y) && return FlexInt($op(x.big::BigInt, y.int))
            return FlexInt($op(x.big::BigInt, y.big::BigInt))
        end
    )
end

macro binop_with_overflow(op, overflow)
    return :(
        function $op(x::FlexInt, y::FlexInt)
            is_small(x) && is_small(y) && begin
                    r, f = $overflow(x.int, y.int)
                    if f
                        return FlexInt($op(BigInt(x.int), y.int))
                    else
                        return FlexInt(r)
                    end
                end
            is_small(x) && return FlexInt(x.int + y.big::BigInt)
            is_small(y) && return FlexInt(x.big::BigInt + y.int)
            return FlexInt(x.big::BigInt + y.big::BigInt)

        end
    )
end

macro compare_op(op)
    return :(
        function $op(x::FlexInt, y::FlexInt)
            is_small(x) && is_small(y) && return $op(x.int, y.int)
            is_small(x) && return $op(x.int, y.big)
            is_small(y) && return $op(x.big, y.int)
            return $op(x.big, y.big)
        end
    )
end

@binop_with_overflow(Base.:+, Base.add_with_overflow)
@binop_with_overflow(Base.:-, Base.sub_with_overflow)
@binop_with_overflow(Base.:*, Base.add_with_overflow)
@binop(Base.div)
@compare_op(Base.:<)
@compare_op(Base.:<=)
@compare_op(==) # This is special for some reason
@compare_op(Base.:>=)
@compare_op(Base.:>)

end
"""

export
header : String
header = """
#!/bin/env julia
# \{generatedString "julia"}

function believe_me(x)
    return x
end

struct Unreachable <: Exception
    location::String
end

macro unreachable(location)
    :(throw(Unreachable($(esc(location)))))
end

# From Integer
idris_cast(::Type{to}, x::Integer) where { to <: Integer } = unsafe_trunc(to, x)
idris_cast(::Type{String}, x::Integer) = string(x)
idris_cast(::Type{to}, x::Integer) where { to <: AbstractFloat } = convert(to, x)

# From Float
idris_cast(::Type{to}, x::AbstractFloat) where { to <: Integer } = unsafe_trunc(to, x)
idris_cast(::Type{String}, x::AbstractFloat) = string(x)

# From Char
idris_cast(::Type{String}, x::Char) = string(x)
idris_cast(::Type{to}, x::Char) where { to <: Integer } = convert(to, x)

# From String
idris_cast(::Type{to}, x::String) where { to <: Integer } = parse(to, x)
idris_cast(::Type{Float64}, x::String) = parse(Float64, x)

mutable struct Delay
    @atomic gen::Union{Function,Nothing}
    val::Union{Any,Nothing}
end

macro delay(x)
    :(Delay(() -> $(esc(x)), nothing))
end

function force(x::Delay)
    gen = @atomic x.gen
    if isnothing(gen)
        return x.val
    else
        x.val = gen()
        @atomic x.gen = nothing
        return x.val
    end
end

function idris_crash(msg::String)
    print(stderr, msg)
    exit(1)
end

struct Buffer
    ptr::Ptr{Cvoid}
end

Base.cconvert(::Type{Ptr{Cvoid}}, x::Buffer) = x.ptr

function idris_fastUnpack(x::AbstractString)
    acc = Prelude.Basic.Nil
    for c in Iterators.reverse(x)
        acc = Prelude.Basics._u58_u58(c, acc)
    end
    return acc
end

function idris_listPrint(::Type{T}, xs) where {T}
    if isnothing(xs)
        return ""
    else
        io = IOBuffer()
        while isa(xs, Prelude.Basic._u58_u58)
            print(io, xs.fst::T)
            xs = xs.snd
        end
        return String(take!(io))
    end
end

@inline function idris_fastPack(xs)
    return idris_listPrint(Char, xs)
end

@inline function idris_fastConcat(xs)
    return idris_listPrint(String, xs)
end

@inline idris_isNull(x::Ptr) = x == C_NULL
@inline idris_getNull() = Ptr{Cvoid}(C_NULL)

function idris_fork(k)
    return Base.Threads.@spawn $k()
end

idris_wait(thread) = (wait(thread); nothing)

mutable struct Mut
    val
end

@inline idris_writeIORef(mut::Mut, val) = (mut.val = val; nothing)

idris_newArray(n, val) = fill!(Vector{Any}(undef, n), val)
@inline idris_arrayGet(arr, idx) = arr[idx + 1]
@inline idris_arraySet(arr, idx, val) = (arr[idx + 1] = val; nothing)

\{flexnum}
using .FlexNum
"""
