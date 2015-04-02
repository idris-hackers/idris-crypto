import Data.Bits

class Masher m where
  blockLength : Nat

class Masher h => Hash h where
  outputLength : Nat
  initialContext : Bits blockLength
  updateContext : Bits blockLength -> Bits blockLength -> Bits blockLength
  finalize : Bits blockLength -> Vect (div outputLength blockLength) (Bits blockLength)
  
hashMessage : Hash h => h -> List (Bits blockLength) -> Vect (div outputLength blockLength) (Bits blockLength)
hashMessage hash = finalize . foldl updateContext initialContext

class Masher c => Cipher c where
  encryptMessage : e -> List (Bits blockLength) -> List (Bits blockLength)
  decryptMessage : d -> List (Bits blockLength) -> List (Bits blockLength)

class (Cipher c) => SymmetricCipher c where

class Masher s => Signer s where
  signMessage : e -> List (Bits blockLength) -> List (Bits blockLength)

class Masher v => Verifier v where
  verifyMessage : v -> List (Bits blockLength) -> List (Bits blockLength) -> Bool

class (Signer m, Verifier m) => MAC m where
  instance Verifier m where
    verifyMessage key message digest = digest == signMessage key message

class (Signer s, Verifier v) => Signature s v where
  buildKeyPair : (s, v)

class Cipher pk => PrivateKey pk where

class Cipher pk => PublicKey pk where

instance (Hash h, PrivateKey p) => Masher (h, p) where
  blockLength = blockLength

instance (Hash h, PrivateKey p) => Signer (h, p) where
  signMessage (hash, pk) message = encryptMessage pk (toList (hashMessage hash message))

instance (Hash h, PublicKey p) => Masher (h, p) where
  blockLength = blockLength

instance (Hash h, PublicKey v) => Verifier (h, v) where
  verifyMessage (hash, pk) message signature =
    decryptMessage pk signature == toList (hashMessage hash message)

class (PrivateKey p, PublicKey v) => AsymmetricCipher p v where

instance (AsymmetricCipher p v, Hash h) => Signature (h, p) (h, v) where
  buildKeyPair = buildKeyPair
