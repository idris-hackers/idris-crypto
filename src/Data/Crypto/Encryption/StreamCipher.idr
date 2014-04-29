module Data.Crypto.Encryption.StreamCipher

import Data.Crypto.Util
import Data.Crypto.Encryption.SymmetricCipher

%default total
%access public

class StreamCipher k where
  bitsPerUnit : Nat
  generateKeystream : k -> Stream (Bits bitsPerUnit)

-- Stream ciphers are automorphic, so the encryption and decryption algorithms
-- are identical. I don’t know when that would ever be useful, but if it is, you
-- can just use `confound*` to handle whichever way you want.

confoundStream :
  StreamCipher k => k -> Stream (Bits bitsPerUnit) -> Stream (Bits bitsPerUnit)
confoundStream key = Prelude.Stream.zipWith xor (generateKeystream key)
encryptStream :
  StreamCipher k => k -> Stream (Bits bitsPerUnit) -> Stream (Bits bitsPerUnit)
encryptStream = confoundStream
decryptStream :
  StreamCipher k => k -> Stream (Bits bitsPerUnit) -> Stream (Bits bitsPerUnit)
decryptStream = confoundStream

confoundMessage :
  StreamCipher k => k -> List (Bits bitsPerUnit) -> List (Bits bitsPerUnit)
confoundMessage key message =
  toList (Prelude.Vect.zipWith xor
                               (Prelude.Stream.take (length message)
                                                    (generateKeystream key))
                               (fromList message))

instance StreamCipher sc => SymmetricCipher sc where
  bitsPerChunk = bitsPerUnit
  encryptMessage = confoundMessage
  decryptMessage = confoundMessage

confound : (StreamCipher k, Serializable i, Serializable o) => k -> i -> o
confound key = decode . confoundMessage key . encode
