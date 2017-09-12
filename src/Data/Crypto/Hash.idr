module Data.Crypto.Hash

import Data.Bits

%default total

interface Hash h where
  blockLength : Nat
  outputLength : Nat
  initialize : Vect m (Bits n) -> List (Bits blockLength)
  initialContext : h
  updateContext : h -> Bits blockLength -> h
  finalize : h -> Bits outputLength

hashMessage : Hash h => h -> Vect m (Bits n) -> Bits outputLength
hashMessage _ message = finalize (foldl updateContext initialContext (initialize message))
