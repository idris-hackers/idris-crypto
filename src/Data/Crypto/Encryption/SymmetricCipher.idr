module Data.Crypto.Encryption.SymmetricCipher

import Data.Bits
import Data.Crypto.Util

%default total
%access public

class SymmetricCipher c where
  bitsPerChunk : Nat
  encryptMessage : c -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)
  decryptMessage : c -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)

encrypt : (SymmetricCipher c, Serializable pt, Serializable ct) => c -> pt -> ct
encrypt cipher = decode . encryptMessage cipher . encode

decrypt : (SymmetricCipher c, Serializable pt, Serializable ct) => c -> pt -> ct
decrypt cipher = decode . decryptMessage cipher . encode
