module Data.Mod

%default total
%access public

||| Modular arithmetic
data Mod : (n : Nat) -> Type where
  MkMod : (fin : Fin n) -> Mod n

instance Eq (Mod n) where
  (==) (MkMod x) (MkMod y) = x == y

instance Cast (Mod n) Nat where
  cast (MkMod x) = cast x

instance Cast (Mod n) (Fin n) where
  cast (MkMod x) = x

instance Ord (Mod (S n)) where
  compare (MkMod x) (MkMod y) = compare x y

instance MinBound (Mod (S n)) where
  minBound = MkMod fZ

instance MaxBound (Mod (S n)) where
  maxBound = MkMod last

natToMod : Nat -> Mod (S n)
natToMod {n=(S m)} x =
  MkMod (finMod (x `mod` (S (S m)))) where
    finMod : Nat -> Fin (S k)
    finMod Z = fZ
    finMod {k=S k} (S k) = fS (finMod k)
    finMod _ = fZ
natToMod _ = MkMod fZ

modToInteger : Mod n -> Integer
modToInteger (MkMod x) = finToInteger x

rotate : Fin (S n) -> Fin (S n)
rotate {n=Z} _ = fZ
rotate {n = S m} fZ = fS fZ
rotate {n = S m} (fS g) = if (fS g) == last
                          then fZ
                          else fS (rotate g)

private
modplus : Mod (S n) -> Mod (S n) -> Mod (S n)
modplus (MkMod left) (MkMod right) = MkMod (spin left right)
  where spin : Fin (S n') -> Fin (S n) -> Fin (S n)
        spin fZ right = right
        spin {n' = Z} left right = rotate right
        spin {n' = S m} (fS left) right = rotate (spin left right)

instance Semigroup (Mod (S n)) where
  (<+>) = modplus

instance Monoid (Mod (S n)) where
  neutral = MkMod fZ

instance Group (Mod (S n)) where
  inverse (MkMod fZ) = MkMod fZ
  inverse {n=n} (MkMod m) = natToMod ((S n) - (finToNat m))

instance Num (Mod (S n)) where
  (+) = modplus
  (-) = (<->)
  (*) (MkMod a) (MkMod b) = fromInteger (finToInteger a * finToInteger b)
  abs = id
  fromInteger {n=n} x = if x < 0
                        then inverse (natToMod (fromInteger (-x) `mod` S n))
                        else natToMod (fromInteger x `mod` S n)

