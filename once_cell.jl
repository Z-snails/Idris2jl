const SPINS::UInt8 = 10

struct State
    init::UInt8
end

const Uninit::State = State(0)
const Initialising::State = State(1)
const Init::State = State(2)

mutable struct OnceCell{T}
    @atomic state::State
    val::Union{T, Nothing}
end

OnceCell(::Type{T}) where {T} = OnceCell{T}(Uninit, nothing)
OnceCell{T}(val) where {T} = OnceCell{T}(Init, val)
OnceCell(val) = OnceCell{typeof(val)}(val)

@noinline function get_cold(cell::OnceCell{T})::T where {T}
    while (@atomic cell.state) === Initialising end
    return cell.val
end

function get(cell::OnceCell{T})::Union{T,Nothing} where {T}
    state = @atomic cell.state
    if state === Init
        return cell.val
    elseif state == Uninit
        return nothing
    else
        get_cold(cell)
    end
end

function unsafe_get(cell::OnceCell{T})::Union{T,Nothing} where {T}
    return cell.val
end

function write_once!(cell::OnceCell{T}, val::T)::Bool where {T}
    (_, ok) = @atomicreplace cell.state Uninit => Initialising
    if ok
        cell.val = val
        @atomic cell.state = Init
        return true
    else
        return false
    end
end

function get_or_init(cell::OnceCell{T}, f::Function)::T where {T}
    state = @atomic cell.state
    if state === Init
        return cell.val
    elseif state === Uninit
        write_once!(cell, f())
        return cell.val
    else
        return get_cold(cell)
    end
end
