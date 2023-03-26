module Simd.AsciiValidator

data Val : {0 a : Type} -> (x : a) -> Type where [external]

data Simd : Nat -> Type -> Type where [external]

data IsSimdElt : Type -> Type where
    SimdBool : IsSimdElt Bool
    SimdInt : IsSimdElt Int
    SimdInt8 : IsSimdElt Int8
    SimdInt16 : IsSimdElt Int16
    SimdInt32 : IsSimdElt Int32
    SimdInt64 : IsSimdElt Int64
    SimdBits8 : IsSimdElt Bits8
    SimdBits16 : IsSimdElt Bits16
    SimdBits32 : IsSimdElt Bits32
    SimdBits64 : IsSimdElt Bits64
    SimdDouble : IsSimdElt Double
    SimdBitsPtr : IsSimdElt (Ptr a)
    SimdBitsAnyPtr : IsSimdElt AnyPtr

%inline
%foreign "julia:(_, x) -> Val(x)"
val : (x : a) -> Val x

%inline
%foreign "julia:import SIMD, (_, _, count, val) -> SIMD.Vec(ntuple(_ -> val, count))"
prim__splat : (0 c, a : _) -> Val c -> (val : a) -> Simd c a

%inline
splat : (0 _ : IsSimdElt a) => Val c -> a -> Simd c a
splat c val = prim__splat _ _ c val 

%inline
%foreign "julia:import SIMD, (_, _, x, y) -> x + y"
prim__add : (0 c, a : _) -> Simd c a -> Simd c a -> Simd c a

%inline
add : (0 _ : IsSimdElt a) => Simd c a -> Simd c a -> Simd c a
add x y = prim__add _ _ x y

%inline
%foreign "julia:import SIMD, (_, _, x, y) -> x * y"
prim__mul : (0 c, a : _) -> Simd c a -> Simd c a -> Simd c a

%inline
mul : (0 _ : IsSimdElt a) => Simd c a -> Simd c a -> Simd c a
mul x y = prim__mul _ _ x y

%inline
%foreign "julia:import SIMD, (_, _, x, y) -> x < y"
prim__lanes_lt : (0 c, a : _) -> Simd c a -> Simd c a -> Simd c Bool

lanes_lt : (0 _ : IsSimdElt a) => Simd c a -> Simd c a -> Simd c Bool
lanes_lt x y = prim__lanes_lt _ _ x y
