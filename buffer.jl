struct Buffer
    ptr::Ptr{Cvoid}
end

function Buffer(length::Int)
    length = Cint(length)
    size = sizeof(Cint) + length
    ptr = Base.Libc.malloc(size)
    unsafe_store!(Ptr{Cint}(ptr), length)
    return Buffer(ptr)
end

@inline Base.length(buf::Buffer) = Int(unsafe_load(Ptr{Cint}(buf.ptr)))

@inline function assert_valid_range(buf::Buffer, offset::Integer, len::Integer)
    @assert offset >= 0
    @assert len >= 0
    offset + len <= length(buf) || throw(BoundsError(buf, offset + len))
end

@inline get_data_ptr(buf::Buffer) = Ptr{UInt8}(buf.ptr + sizeof(Cint))

@inline function Base.getindex(buf::Buffer, offset::Integer)
    assert_valid_range(buf, offset, 1)
    return unsafe_load(get_data_ptr(buf), offset + 1)
end

@inline function Base.setindex!(buf::Buffer, val::UInt8, offset::Integer)
    assert_valid_range(buf, offset, 1)
    unsafe_store!(get_data_ptr(buf), val, offset + 1)
end

function buffer_load(::Type{T}, buf::Buffer, offset::Integer) where {T <: Integer}
    assert_valid_range(buf, offset, sizeof(T))
    val = zero(T)
    for i in sizeof(T) - 1:-1:0
        val <<= 8
        val += T(buf[offset + i])
    end
    return val
end

function buffer_store(::Type{T}, buf::Buffer, offset::Integer, val::T) where {T <: Integer}
    assert_valid_range(buf, offset, sizeof(T))
    for i in 0:sizeof(T) - 1
        buf[i] = unsafe_trunc(UInt8, val)
        val >>= 8
    end
end
