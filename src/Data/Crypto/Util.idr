module Data.Crypto.Util

import Data.Bits
import Data.Fin
import Data.Vect

import Data.Mod

%default total

trim : Bits (1 + n) -> Bits n
trim b = truncate (shiftRightLogical (intToBits 1) b)

-- bitsToFin : Bits n -> Fin (power 2 n)
-- bitsToFin {n=Z}   _ = FZ
-- bitsToFin {n=S _} b = let x = FS (FS FZ) * (bitsToFin (trim b))
--                       in if (b `and` (intToBits 1)) == (intToBits 0)
--                          then x
--                          else FS x
-- bitsToFin {n=n} bits = fromMaybe (replace ((powerSuccPowerLeft 2 n)) FZ) (integerToFin (bitsToInt bits) (power 2 n))



partial
divCeil : Nat -> Nat -> Nat
divCeil x y = case x `mod` y of
                Z   => x `div` y
                S _ => S (x `div` y)

public export
finToBits : Fin n -> Bits (nextPow2 n)
finToBits = intToBits . finToInteger

public export
modToBits : Mod n -> Bits (nextPow2 n)
modToBits = intToBits . modToInteger

public export
rotateLeft : Bits n -> Nat -> Bits n
rotateLeft {n=Z} bits _ = bits
rotateLeft {n=S n} bits rot =
  let norm = modNatNZ rot (S n) (uninhabited . sym)
  in shiftLeft bits (intToBits (cast norm)) `or` shiftRightLogical bits (intToBits (cast ((S n) `minus` norm)))

public export
swap : Fin n -> Fin n -> Vect n a -> Vect n a
swap i j v = replaceAt j (index i v) (replaceAt i (index j v) v)

public export
notZero : Nat -> Type
notZero Z = Void
notZero (S n) = ()

public export
tightmod : Nat -> (m : Nat) -> {default () ok : notZero m} -> Fin m
tightmod _ Z {ok=prf} = void prf
tightmod left (S modulus) = tightmod' left left modulus
  where
    tightmod' : Nat -> Nat -> (n : Nat) -> Fin (S n)
    tightmod' Z center right = fromMaybe FZ (natToFin center (S right))
    tightmod' (S left) center right =
      if lte center right
      then fromMaybe FZ (natToFin center (S right))
      else tightmod' left (center `minus` (S right)) right

public export
Byte : Type
Byte = Bits 8

public export
interface Serializable a where
  encode : a -> List (Bits n)
  decode : List (Bits n) -> a

-- Arrow defined for functions
infixr 3 ***
infixr 3 &&&
public export first : (a -> c) -> (a, b) -> (c, b)
first f = (\(a, b) => (f a, b))
public export second : (b -> d) -> (a, b) -> (a, d)
second f = (\(a, b) => (a, f b))
public export (***) : (a -> c) -> (b -> d) -> (a, b) -> (c, d)
f *** g = (\(a, b) => (f a, g b))
public export (&&&) : (a -> c) -> (a -> d) -> a -> (c, d)
f &&& g = (\a => (f a, g a))

postulate minusPlusIdentity : (m, n : Nat) -> (m `minus` n) + n = m
postulate plusMinusIdentity : (m, n : Nat) -> n + (m `minus` n) = m

public export
partition : Bits (m * n) -> Vect m (Bits n)
partition {m=Z}         _    = []
partition {m=S m} {n=n} bits =
  truncate (replace (plusCommutative n (m*n)) bits)
  :: partition (truncate (shiftRightLogical bits (intToBits (cast n))))
public export
partition' : Bits m -> (List (Bits n), (p : Nat ** Bits p))
partition' {m=m} {n=n}   bits = part m bits
  where part : Nat -> Bits r -> (List (Bits n), (p : Nat ** Bits p))
        part Z bits = ([], (0 ** intToBits 0))
        part {r=r} (S q) bits = if r < n
                                then ([], (r ** bits))
                                else first (Prelude.List.(::) (truncate (replace (sym (minusPlusIdentity r n)) (shiftRightLogical bits (intToBits (cast (r `minus` n)))))))
             (part q (truncate (replace (sym (plusMinusIdentity r n)) bits)))
public export
append : Bits m -> Bits n -> Bits (m + n)
append {m=m} {n=n} a b = shiftLeft (zeroExtend a) (intToBits (cast n)) `or` (rewrite plusCommutative m n in zeroExtend b)
public export
concat : Vect m (Bits n) -> Bits (m * n)
concat {m=Z}         _         = intToBits 0
concat {m=S Z} {n=n} [bits]    = replace (sym (plusZeroRightNeutral n)) bits
concat {m=S _}       (b::rest) = append b (concat rest)
public export repartition : Vect m (Bits n) -> List (Bits q)
repartition = fst . partition' . Data.Crypto.Util.concat -- not at all efficient
