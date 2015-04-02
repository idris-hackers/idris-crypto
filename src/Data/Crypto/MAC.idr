module Data.Crypto.MAC

import Data.Bits

%default total

class Signer s (blockLength : Nat) (outputLength : Nat) where
  signMessage : e -> List (Bits blockLength) -> Bits outputLength

class Verifier v (blockLength : Nat) (outputLength : Nat) where
  verifyMessage : v -> List (Bits blockLength) -> Bits n -> Bool

class (Signer m b o, Verifier m b o) => MAC m (b : Nat) (o : Nat) where
  instance Verifier m b o where
    verifyMessage key message digest = digest == signMessage key message
