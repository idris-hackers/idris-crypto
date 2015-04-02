module Data.Crypto

%default total

public
class Masher m (b : Nat) where
  blockLength : Nat
