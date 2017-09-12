module Data.Crypto.Encryption.Stream

import Data.Bits
import Data.Vect

import Data.Crypto.Encryption
import Data.Crypto.Util

%default total
%access public export

interface Cipher k => StreamCipher k where
  generateKeystream : k -> Stream (Bits bitsPerChunk)

-- Stream ciphers are automorphic, so the encryption and decryption algorithms
-- are identical. I don’t know when that would ever be useful, but if it is, you
-- can just use `confound*` to handle whichever way you want.

confoundStream :
  StreamCipher k => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
confoundStream key = Stream.zipWith xor (generateKeystream key)
encryptStream :
  StreamCipher k => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
encryptStream = confoundStream
decryptStream :
  StreamCipher k => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
decryptStream = confoundStream

confoundMessage :
  StreamCipher k => k -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)
confoundMessage key message =
  zipWith xor (Stream.take (length message) (generateKeystream key)) message

implementation StreamCipher sc => Encrypter sc where
  encryptMessage = confoundMessage

implementation StreamCipher sc => Decrypter sc where
  decryptMessage = confoundMessage

implementation (StreamCipher sc, Encrypter sc, Decrypter sc) => SymmetricCipher sc where

-- TODO this should be solved by #3936
{-
confound : (StreamCipher k, Serializable i, Serializable o) => k -> i -> o
confound key = decode . confoundMessage key . encode
-}