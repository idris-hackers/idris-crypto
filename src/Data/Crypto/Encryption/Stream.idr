module Data.Crypto.Encryption.Stream

import Data.Crypto.Util
import Data.Crypto.Encryption

%default total
%access public

class Cipher k => StreamCipher k where
  generateKeystream : k -> Stream (Bits bitsPerChunk)

-- Stream ciphers are automorphic, so the encryption and decryption algorithms
-- are identical. I don’t know when that would ever be useful, but if it is, you
-- can just use `confound*` to handle whichever way you want.

confoundStream :
  StreamCipher k => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
confoundStream key = Prelude.Stream.zipWith xor (generateKeystream key)
encryptStream :
  StreamCipher k => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
encryptStream = confoundStream
decryptStream :
  StreamCipher k => k -> Stream (Bits bitsPerChunk) -> Stream (Bits bitsPerChunk)
decryptStream = confoundStream

confoundMessage :
  StreamCipher k => k -> List (Bits bitsPerChunk) -> List (Bits bitsPerChunk)
confoundMessage key message =
  toList (Prelude.Vect.zipWith xor
                               (Prelude.Stream.take (length message)
                                                    (generateKeystream key))
                               (fromList message))

instance StreamCipher sc => Encrypter sc where
  encryptMessage = confoundMessage

instance StreamCipher sc => Decrypter sc where
  decryptMessage = confoundMessage

instance (StreamCipher sc, Encrypter sc, Decrypter sc) => SymmetricCipher sc where

confound : (StreamCipher k, Serializable i, Serializable o) => k -> i -> o
confound key = decode . confoundMessage key . encode
