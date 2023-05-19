include("flexnum.jl")
using .FlexNum

function believe_me(x)
    return x
end

struct Error <: Exception
    message::String
end

struct Unreachable <: Exception
    location::String
end

macro unreachable(location)
    :(throw(Unreachable($(esc(location)))))
end

# From Integer
cast(::Type{to}, x::Integer) where {to<:Integer} = unsafe_trunc(to, x)
cast(::Type{String}, x::Integer) = string(x)
cast(::Type{Char}, x::Integer) = Char(x)
cast(::Type{to}, x::Integer) where {to<:AbstractFloat} = convert(to, x)

# From Float
cast(::Type{to}, x::AbstractFloat) where {to<:Integer} = unsafe_trunc(to, x)
cast(::Type{String}, x::AbstractFloat) = string(x)

# From Char
cast(::Type{String}, x::Char) = string(x)
cast(::Type{to}, x::Char) where {to<:Integer} = convert(to, x)

# From String
cast(::Type{to}, x::String) where {to<:Integer} = parse(to, x)
cast(::Type{Float64}, x::String) = parse(Float64, x)

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

function crash(msg::String)
    print(stderr, msg)
    exit(1)
end

struct Buffer
    ptr::Ptr{Cvoid}
end

Base.cconvert(::Type{Ptr{Cvoid}}, x::Buffer) = x.ptr

struct Cons
    fst
    snd
end

iscons(x::Cons) = true
iscons(::Any) = false

function fastUnpack(x::AbstractString)
    acc = nothing
    for c in Iterators.reverse(x)
        acc = Cons(c, acc)
    end
    return acc
end

function listPrint(::Type{T}, xs) where {T}
    if isnothing(xs)
        return ""
    else
        io = IOBuffer()
        while iscons(xs)
            print(io, xs.fst::T)
            xs = xs.snd
        end
        return String(take!(io))
    end
end

@inline function fastPack(xs)
    return listPrint(Char, xs)
end

@inline function fastConcat(xs)
    return listPrint(String, xs)
end

@inline isNull(x::Ptr) = x == C_NULL
@inline getNull() = Ptr{Cvoid}(C_NULL)

function fork(k)
    return Base.Threads.@spawn $k()
end

wait(thread) = (wait(thread); nothing)

mutable struct Mut
    val
end

@inline writeIORef(mut::Mut, val) = (mut.val = val; nothing)

newArray(n, val) = fill!(Vector{Any}(undef, n), val)
@inline arrayGet(arr, idx) = arr[idx+1]
@inline arraySet(arr, idx, val) = (arr[idx+1] = val; nothing)

function from_Cstring(x::Cstring)
    acc = IOBuffer()
    ptr = Ptr{Cchar}(x)
    while ptr[] != 0
        push!(acc, Char(ptr[]))
        ptr += 1
    end
    Base.Libc.free(x)
    return take!(acc)
end
