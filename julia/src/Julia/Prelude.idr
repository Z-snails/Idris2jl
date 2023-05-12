module Julia.Prelude

export
data Val : (x : a) -> Type where [external]

export %extern
val : (x : a) -> Val x
