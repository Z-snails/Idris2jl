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

"""
    FlexNum <: Base.Signed

Arbitrary precision integer type, which switches from machine integers to GMP integers when needed.
"""
struct FlexInt <: Base.Signed
    int::Int
    big::Union{BigInt,Nothing}
end

@inline FlexInt(x::Int) = FlexInt(x, nothing)
@inline FlexInt(x::BigInt) = FlexInt(0, x)

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
Base.convert(::Type{to}, x::FlexInt) where {to<:Integer} = is_small(x) ? Base.convert(to, x.int) : Base.convert(to, x.big)
Base.unsafe_trunc(::Type{to}, x::FlexInt) where {to<:Integer} = is_small(x) ? Base.unsafe_trunc(to, x.int) : Base.unsafe_trunc(to, x.big)

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
