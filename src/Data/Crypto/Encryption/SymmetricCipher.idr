module Data.Crypto.Encryption.SymmetricCipher

import Data.Bits
import Data.Crypto.Util
import Data.Crypto.Security

%default total
%access public

class SymmetricCipher c where
  bitsPerChunk : Nat
  encryptMessage : c -> List (Bits bitsPerChunk) -> Security (List (Bits bitsPerChunk))
  decryptMessage : c -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)

encrypt : (SymmetricCipher c, Serializable pt, Serializable ct) => c -> pt -> Security ct
encrypt cipher message = pure decode <$> encryptMessage cipher (encode message)

decrypt : (SymmetricCipher c, Serializable ct, Serializable pt) => c -> ct -> pt
decrypt cipher = decode . decryptMessage cipher . encode
