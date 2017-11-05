module Data.Crypto.Encryption.Stream

import Data.Bits
import Data.Vect

import Data.Crypto.Encryption
import Data.Crypto.Util

%default total
%access public export

interface Cipher k bitsPerChunk => StreamCipher k (bitsPerChunk : Nat) | k where
  generateKeystream : k -> Stream (Bits bitsPerChunk)

-- Stream ciphers are automorphic, so the encryption and decryption algorithms
-- are identical. I don’t know when that would ever be useful, but if it is, you
-- can just use `confound*` to handle whichever way you want.

confoundStream :
  StreamCipher k bitsPerChunk => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
confoundStream key = Stream.zipWith xor (generateKeystream key)
encryptStream :
  StreamCipher k bitsPerChunk => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
encryptStream = confoundStream
decryptStream :
  StreamCipher k bitsPerChunk => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
decryptStream = confoundStream

confoundMessage :
  StreamCipher k bitsPerChunk => k -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)
confoundMessage key message =
  zipWith xor (Stream.take (length message) (generateKeystream key)) message

implementation StreamCipher sc b => Encrypter sc b where
  encryptMessage = confoundMessage

implementation StreamCipher sc b => Decrypter sc b where
  decryptMessage = confoundMessage

implementation (StreamCipher sc b, Encrypter sc b, Decrypter sc b) =>
  SymmetricCipher sc b where

confound : (StreamCipher k _, Serializable i, Serializable o) => k -> i -> o
confound key = decode . confoundMessage key . encode
