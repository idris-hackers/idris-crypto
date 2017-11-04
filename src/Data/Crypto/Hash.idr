module Data.Crypto.Hash

import Data.Bits
import Data.Vect

%default total
%access public export

-- TODO: Add `maxMessageLength : Maybe Nat`. This would be `Nothing` for MD5 and
--      `Just (expt 2 64)` for the shorter SHS algos. And it should affect the
--       types of `initialize` and `hashMessage`.
interface Hash h (blockLength : Nat) (outputLength : Nat) | h where
  initialize : h -> Vect m (Bits n) -> List (Bits blockLength)
  initialContext : h -> h
  updateContext : h -> Bits blockLength -> h
  finalize : h -> Bits outputLength

hashMessage : Hash h b outputLength => h -> Vect m (Bits n) -> Bits outputLength
hashMessage hash message =
  finalize (foldl updateContext (initialContext hash) (initialize hash message))
