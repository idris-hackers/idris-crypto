module Data.Mod

import Control.Algebra
import Data.Fin

%default total
%access public export

||| Modular arithmetic
data Mod : (n : Nat) -> Type where
  MkMod : (fin : Fin n) -> Mod n

implementation Eq (Mod n) where
  (==) (MkMod x) (MkMod y) = x == y

implementation Cast (Mod n) Nat where
  cast (MkMod x) = cast x

implementation Cast (Mod n) (Fin n) where
  cast (MkMod x) = x

implementation Ord (Mod (S n)) where
  compare (MkMod x) (MkMod y) = compare x y

implementation MinBound (Mod (S n)) where
  minBound = MkMod FZ

implementation MaxBound (Mod (S n)) where
  maxBound = MkMod last

natToMod : Nat -> Mod (S n)
natToMod {n=(S m)} x =
  MkMod (finMod (modNatNZ x (S (S m)) (uninhabited . sym))) where
    finMod : Nat -> Fin (S k)
    finMod Z = FZ
    finMod {k=S k'} (S l) = FS (finMod {k=k'} l)
    finMod _ = FZ
natToMod _ = MkMod FZ

modToInteger : Mod n -> Integer
modToInteger (MkMod x) = finToInteger x

modToNat : Mod n -> Nat
modToNat (MkMod x) = finToNat x

rotate : Fin (S n) -> Fin (S n)
rotate {n=Z} _ = FZ
rotate {n = S m} FZ = FS FZ
rotate {n = S m} (FS g) = if (FS g) == last
                          then FZ
                          else FS (rotate g)

private
modplus : Mod (S n) -> Mod (S n) -> Mod (S n)
modplus (MkMod left) (MkMod right) = MkMod (spin left right)
  where spin : Fin (S n') -> Fin (S n) -> Fin (S n)
        spin FZ right = right
        spin {n' = Z} left right = rotate right
        spin {n' = S m} (FS left) right = rotate (spin left right)

implementation Semigroup (Mod (S n)) where
  (<+>) = modplus

implementation Monoid (Mod (S n)) where
  neutral = MkMod FZ

implementation Group (Mod (S n)) where
  inverse (MkMod FZ) = MkMod FZ
  inverse {n=n} (MkMod m) = natToMod ((S n) `minus` (finToNat m))

implementation Num (Mod (S n)) where
  (+) = modplus
  (*) (MkMod a) (MkMod b) = fromInteger (finToInteger a * finToInteger b)
  fromInteger {n=n} x = if x < 0
                        then inverse (natToMod (modNatNZ (fromInteger (-x)) (S n) (uninhabited . sym)))
                        else natToMod (modNatNZ (fromInteger x) (S n) (uninhabited . sym))

implementation Neg (Mod (S n)) where
  negate = const (MkMod FZ)
  (-) = (<->)
