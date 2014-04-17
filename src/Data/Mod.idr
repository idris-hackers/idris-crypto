module Data.Mod

%default total
%access public

||| Modular arithmetic
abstract
data Mod : (n : Nat) -> Type where
  mZ : Mod (S k)
  mS : Mod k -> Mod (S k)

instance Uninhabited (Mod Z) where
  uninhabited mZ impossible
  uninhabited (mS _) impossible
  
modInjective : (m : Mod k) -> (n : Mod k) -> mS m = mS n -> m = n
modInjective left _ refl = refl

instance Eq (Mod n) where
    (==) mZ mZ = True
    (==) (mS k) (mS k') = k == k'
    (==) _ _ = False

ModZAbsurd : Mod Z -> _|_
ModZAbsurd mZ impossible

ModZElim : Mod Z -> a
ModZElim x = FalseElim (ModZAbsurd x)

modToNat : Mod n -> Nat
modToNat mZ = Z
modToNat (mS k) = S (modToNat k)

modToNatInjective : (mm : Mod k) -> (mn : Mod k) -> (modToNat mm) = (modToNat mn) -> mm = mn
modToNatInjective mZ     mZ     refl = refl
modToNatInjective (mS m) mZ     refl impossible
modToNatInjective mZ     (mS n) refl impossible
modToNatInjective (mS m) (mS n) prf  =
  cong (modToNatInjective m n (succInjective (modToNat m) (modToNat n) prf)) 

instance Cast (Mod n) Nat where
    cast x = modToNat x

natToMod : Nat -> Mod (S n)
natToMod {n=(S m)} x with (x `mod` (S (S m)))
  | Z = mZ
  | (S k) = mS (natToMod k)
natToMod _ = mZ

modToInteger : Mod n -> Integer
modToInteger mZ = 0
modToInteger (mS x) = 1 + modToInteger x

instance Cast (Mod n) Integer where
    cast x = modToInteger x

||| The largest element of some Mod type
last : Mod (S n)
last {n=Z} = mZ
last {n=S _} = mS last

instance MinBound (Mod (S n)) where
  minBound = mZ

instance MaxBound (Mod (S n)) where
  maxBound = last

instance Ord (Mod n) where
  compare mZ mZ = EQ
  compare mZ (mS _) = LT
  compare (mS _) mZ = GT
  compare (mS m) (mS m') = compare m m'

rotate : Mod (S n) -> Mod (S n)
rotate {n=Z} _ = mZ
rotate {n = S m} mZ = mS mZ
rotate {n = S m} (mS g) = if (mS g) == last then mZ
                                            else mS (rotate g)

private
modplus : Mod (S n) -> Mod (S n) -> Mod (S n)
modplus left right = spin left right
  where spin : Mod (S n') -> Mod (S n) -> Mod (S n)
        spin mZ right = right
        spin {n' = Z} left right = rotate right
        spin {n' = S m} (mS left) right = rotate (spin left right)

instance Semigroup (Mod (S n)) where
  (<+>) = modplus

instance Monoid (Mod (S n)) where
  neutral = mZ

instance Group (Mod (S n)) where
  inverse mZ = mZ
  inverse {n=n} m = natToMod ((S n) - (modToNat m))

instance Num (Mod (S n)) where
  (+) = modplus
  (-) = (<->)
  (*) a b = fromInteger (modToInteger a * modToInteger b)
  abs = id
  fromInteger {n=n} x = if x < 0
                        then inverse (natToMod (fromInteger (-x) `mod` S n))
                        else natToMod (fromInteger x `mod` S n)

