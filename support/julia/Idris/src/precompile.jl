const _INTS = [Int8, Int16, Int32, Int64, UInt8, UInt16, UInt32, UInt64]

const _COMPILE = Dict(
    # FlexNum
    FlexNum.is_small => [(BigInt,), (FlexInt,)],
    FlexNum.unsafe_get_small => (BigInt,),
    FlexNum.get_small => (BigInt,),
    Base.BigInt => (FlexInt,),

    # Idris
    force => (Delay,),
    crash => (String,),
    fastUnpack => (String,),

    # Base
    Base.convert => map(i -> (Type{i}, FlexInt), _INTS),
    Base.unsafe_trunc => map(i -> (Type{i}, FlexInt), _INTS),
)

function _compile(f, spec)
    if isa(spec, Tuple)
        Base.precompile(f, spec)
    else
        for s in spec
            _compile(f, s)
        end
    end
end

for (f, spec) in _COMPILE
    _compile(f, spec)
end
