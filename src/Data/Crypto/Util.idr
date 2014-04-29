module Data.Crypto.Util

import Data.Bits
import Data.Mod

%default total

trim : Bits (1 + n) -> Bits n
trim b = truncate (shiftRightLogical (intToBits 1) b)

-- bitsToFin : Bits n -> Fin (power 2 n)
-- bitsToFin {n=Z}   _ = fZ
-- bitsToFin {n=S _} b = let x = fS (fS fZ) * (bitsToFin (trim b))
--                       in if (b `and` (intToBits 1)) == (intToBits 0)
--                          then x
--                          else fS x
-- bitsToFin {n=n} bits = fromMaybe (replace ((powerSuccPowerLeft 2 n)) fZ) (integerToFin (bitsToInt bits) (power 2 n))



divCeil : Nat -> Nat -> Nat
divCeil x y = case x `mod` y of
                Z   => x `div` y
                S _ => S (x `div` y)

public
nextPow2 : Nat -> Nat
nextPow2 Z = Z
nextPow2 x = if x == (2 `power` l2x)
             then l2x
             else S l2x
    where
      l2x = log2 x

public
finToBits : Fin n -> Bits (nextPow2 n)
finToBits = intToBits . finToInteger

public
modToBits : Mod n -> Bits (nextPow2 n)
modToBits = intToBits . modToInteger

public
swap : Fin n -> Fin n -> Vect n a -> Vect n a
swap i j v = replaceAt j (index i v) (replaceAt i (index j v) v)

public
Byte : Type
Byte = Bits 8

public
class Serializable a where
  encode : a -> List (Bits n)
  decode : List (Bits n) -> a
