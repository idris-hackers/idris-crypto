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
  minBound = MkMod FZ

instance MaxBound (Mod (S n)) where
  maxBound = MkMod last

natToMod : Nat -> Mod (S n)
natToMod {n=(S m)} x =
  MkMod (finMod (x `mod` (S (S m)))) where
    finMod : Nat -> Fin (S k)
    finMod Z = FZ
    finMod {k=S k} (S k) = FS (finMod k)
    finMod _ = FZ
natToMod _ = MkMod FZ

modToInteger : Mod n -> Integer
modToInteger (MkMod x) = finToInteger x

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

instance Semigroup (Mod (S n)) where
  (<+>) = modplus

instance Monoid (Mod (S n)) where
  neutral = MkMod FZ

instance Group (Mod (S n)) where
  inverse (MkMod FZ) = MkMod FZ
  inverse {n=n} (MkMod m) = natToMod ((S n) - (finToNat m))

instance Num (Mod (S n)) where
  (+) = modplus
  (-) = (<->)
  (*) (MkMod a) (MkMod b) = fromInteger (finToInteger a * finToInteger b)
  abs = id
  fromInteger {n=n} x = if x < 0
                        then inverse (natToMod (fromInteger (-x) `mod` S n))
                        else natToMod (fromInteger x `mod` S n)

