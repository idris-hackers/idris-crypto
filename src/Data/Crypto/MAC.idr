module Data.Crypto.MAC

import Data.Bits

%default total
%access public export

interface Signer s (blockLength : Nat) (outputLength : Nat) | s where
  signMessage : s -> List (Bits blockLength) -> Bits outputLength

interface Verifier v (blockLength : Nat) (outputLength : Nat) | v where
  verifyMessage : v -> List (Bits blockLength) -> Bits n -> Bool

interface (Signer m b o, Verifier m b o) => MAC m (b : Nat) (o : Nat) | m where
  -- TODO: This default implementation _should_ work.
  -- implementation Verifier m b o where
  --   verifyMessage key message digest = digest == signMessage key message
