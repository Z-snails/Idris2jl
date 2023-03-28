module Compiler.Julia.Utils

import Data.String
import Core.Core

export
rangeNonInclusive : Integral a => Ord a => a -> a -> List a
rangeNonInclusive low hi = if low < hi
    then low :: rangeNonInclusive (low + 1) hi
    else []

infix 0 ..=

export %inline
(..=) : Integral a => Ord a => a -> a -> List a
(..=) = rangeNonInclusive

export
enumerate : List a -> List (Nat, a)
enumerate xs = enum 0 xs
  where
    enum : Nat -> List a -> List (Nat, a)
    enum i [] = []
    enum i (x :: xs) = (i, x) :: enum (S i) xs

export
stripPrefix : String -> String -> Maybe String
stripPrefix pre x = if pre `isPrefixOf` x
    then Just $ substr (length pre) (length x) x
    else Nothing

export
liftEither : Either Error a -> Core a
liftEither (Right x) = pure x
liftEither (Left err) = coreFail err
