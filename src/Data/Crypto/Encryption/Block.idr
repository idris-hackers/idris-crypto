module Data.Crypto.Encryption.Block

import Data.Bits
import Data.Crypto.Util
import Data.Crypto.Encryption

%default total
%access private

||| for a block cypher, you only need to provide functions to encrypt/decrypt a
||| single block.
public export
interface BlockCipher k where
  bitsPerBlock : Nat
  maximumBlocks : Nat
  encryptBlock : k -> Bits bitsPerBlock -> Bits bitsPerBlock
  decryptBlock : k -> Bits bitsPerBlock -> Bits bitsPerBlock
  -- blockTranslation : k -> Iso b b
  -- blockTranslation = MkIso (encryptBlock k) (decryptBlock k)

||| The encryption mode specifies how to apply a block cipher to multiple blocks
public export
interface EncryptionMode (em : Nat -> Type) where
  encryptBlocks : BlockCipher k
                  => k -> em bitsPerBlock -> List (Bits bitsPerBlock)
                  -> List (Bits bitsPerBlock)
  decryptBlocks : BlockCipher k
                  => k -> em bitsPerBlock -> List (Bits bitsPerBlock)
                  -> List (Bits bitsPerBlock)

{-
implementation (BlockCipher bc, EncryptionMode em) =>
         Cipher (bc, em bitsPerBlock) where
  bitsPerChunk = bitsPerBlock

implementation (BlockCipher bc, EncryptionMode em) =>
         Encrypter (bc, em bitsPerBlock) where
  encryptMessage = uncurry encryptBlocks

implementation (BlockCipher bc, EncryptionMode em) =>
         Decrypter (bc, em bitsPerBlock) where
  decryptMessage = uncurry decryptBlocks

implementation (BlockCipher bc, EncryptionMode em) =>
         SymmetricCipher (bc, em bitsPerBlock) where
-}