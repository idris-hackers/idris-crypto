module Data.Crypto.Encryption

import Data.Bits
import Data.Crypto.Util

%default total
%access public

class Cipher c where
  bitsPerChunk : Nat

class Cipher e => Encrypter e where
  encryptMessage : e -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)
  
class Cipher d => Decrypter d where
  decryptMessage : d -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)

encrypt : (Encrypter c, Serializable pt, Serializable ct) => c -> pt -> ct
encrypt cipher = decode . encryptMessage cipher . encode

decrypt : (Decrypter c, Serializable pt, Serializable ct) => c -> pt -> ct
decrypt cipher = decode . decryptMessage cipher . encode

class (Encrypter c, Decrypter c) => SymmetricCipher c where

class (Encrypter p, Decrypter v) => AsymmetricCipher p v where
