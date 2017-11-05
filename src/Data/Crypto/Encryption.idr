module Data.Crypto.Encryption

import Data.Bits
import Data.Crypto.Util

%default total
%access public export

interface Cipher c (bitsPerChunk : Nat) | c where

interface Cipher e bitsPerChunk => Encrypter e (bitsPerChunk : Nat) | e where
  encryptMessage : e -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)

interface Cipher d bitsPerChunk => Decrypter d (bitsPerChunk : Nat) | d where
  decryptMessage : d -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)

encrypt : (Encrypter c _, Serializable pt, Serializable ct) => c -> pt -> ct
encrypt cipher = decode . encryptMessage cipher . encode

decrypt : (Decrypter c _, Serializable pt, Serializable ct) => c -> pt -> ct
decrypt cipher = decode . decryptMessage cipher . encode

interface (Encrypter c bitsPerChunk, Decrypter c bitsPerChunk) =>
  SymmetricCipher c (bitsPerChunk : Nat) | c where

interface (Encrypter p pb, Decrypter v vb) =>
  AsymmetricCipher p v (pb : Nat) (vb : Nat) | p, v where
