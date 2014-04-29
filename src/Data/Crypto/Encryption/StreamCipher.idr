module Data.Crypto.Encryption.StreamCipher

import Data.Crypto.Util

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

confoundMessage : (StreamCipher k, Serializable i, Serializable o) =>
                  k -> i -> o
confoundMessage key message =
  -- NB: Ideally, this would use the native word size, so this should be updated
  --     once we have a way to get that.
  let encodedMsg = encode message
  in decode (toList (Prelude.Vect.zipWith xor
                      (Prelude.Stream.take (length encodedMsg)
                                           (generateKeystream key))
                      (fromList encodedMsg)))
encryptMessage : (StreamCipher k, Serializable m, Serializable c) => k -> m -> c
encryptMessage = confoundMessage
decryptMessage : (StreamCipher k, Serializable c, Serializable m) => k -> c -> m
decryptMessage = confoundMessage
