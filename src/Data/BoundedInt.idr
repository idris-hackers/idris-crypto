module Data.BoundedInt

import Data.Bits

trim : Bits (1 + n) -> Bits n
trim b = truncate b

||| An integer in the range [lower, upper). BoundedInt 0 ~= Fin, but using
||| Integers instead of Peano arithmetic, for efficiency.
BoundedInt : Integer -> Nat -> Type
BoundedInt lower upper =
  (x : Integer ** so (lower <= x && x < toIntegerNat upper))

postulate bounds : (x : Integer)
                   -> so (lower <= x && x < toIntegerNat upper)
                   -> so (lower <= x && 1+2*x < pow 2 upper)

bitsToBI : Bits n -> BoundedInt 0 (pow 2 n)
bitsToBI {n=Z}   _ = (0 ** oh)
bitsToBI {n=S _} b = let (x ** meh) = bitsToBI (trim b)
                     in if (b `and` (intToBits 1)) /= (intToBits 0)
                        then (1 + 2 * x ** flip bounds meh)
                        else (2 * x ** flip bounds meh)

(+) : BoundedInt m n -> BoundedInt o p -> BoundedInt (m + o) ((n + p) - 1)
(+) {n=S n} {p=p} (x ** _) (y ** _) = (x + y ** oh)

(-) : BoundedInt m n -> BoundedInt o p -> BoundedInt (m - toIntegerNat p + 1) (fromInteger (toIntegerNat n - o))
(-) (x ** _) (y ** _) = (x - y ** oh)

BIToInteger : BoundedInt m n -> Integer
BIToInteger (x ** _) = x

offByOne : Vect m (BoundedInt (1 + n) (S p)) -> Vect m (BoundedInt n p)
offByOne = map (\x => x - (1 ** oh))
