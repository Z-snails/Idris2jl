module Simd

using Base

export Vec
struct Vec{N,T}
    val::NTuple{N,VecElement{T}}
end

export splat
splat(count, x) = Vec(ntuple(_ -> VecElement(x), count))
Base.zero(::Type{Vec{N,T}}) where {N,T} = splat(Val(N), zero(T))
Base.one(::Type{Vec{N,T}}) where {N,T} = splat(Val(N), one(T))

llvm_type(::Type{Int8}) = "i8"
llvm_type(::Type{Int16}) = "i16"
llvm_type(::Type{Int32}) = "i32"
llvm_type(::Type{Int64}) = "i64"
llvm_type(::Type{UInt8}) = "i8"
llvm_type(::Type{UInt16}) = "i16"
llvm_type(::Type{UInt32}) = "i32"
llvm_type(::Type{UInt64}) = "i64"
llvm_type(::Type{Vec{N,T}}) where {N,T} = "<$(repr(N)) x $(llvm_type(T))>"

const WIDTHS = [1, 2, 4, 8, 16, 32, 64]
const TYPES = [Int8, Int16, Int32, Int64, UInt8, UInt16, UInt32, UInt64]

const BIN_OPS = [("add", :+), ("sub", :-), ("mul", :*)]
for (op, name) in BIN_OPS, N in WIDTHS, T in TYPES

    llvm = """
    %res = $(op) $(llvm_type(Vec{N, T})) %0, %1
    ret $(llvm_type(Vec{N, T})) %res
    """

    @eval @inline function $name(x::Vec{$N,$T}, y::Vec{$N,$T})
        return Vec(Base.llvmcall($llvm, NTuple{$N,VecElement{$T}}, Tuple{NTuple{$N,VecElement{$T}},NTuple{$N,VecElement{$T}}}, x.val, y.val))
    end
end

for (_, f) in BIN_OPS
    @eval @inline Base.$f(x::Vec{N,T}, y::T) where {N,T} = $f(x, splat(Val(N), y))
    @eval @inline Base.$f(x::T, y::Vec{N,T}) where {N,T} = $f(splat(Val(N), x), y)
end

export reduce_add
function reduce_add end

export reduce_mul
function reduce_mul end

for N in WIDTHS, T in TYPES, (f, op) in [(:reduce_add, "add"), (:reduce_mul, "mul"), (:reduce_and, "and"), (:reduce_or, "or"), (:reduce_xor, "xor")]
    fun = "llvm.vector.reduce.$op"
    @eval @inline function $f(x::Vec{$N,$T})
        ccall($fun, llvmcall, $T, (Vec{$N,$T},), x)
    end
end

end
