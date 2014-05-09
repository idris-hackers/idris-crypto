module Data.Crypto.Encryption.BlockCipher

import Data.Bits
import Data.Crypto.Util
import Data.Crypto.Security
import Data.Crypto.Encryption.SymmetricCipher

%default total
%access private

||| for a block cypher, you only need to provide functions to encrypt/decrypt a
||| single block.
public
class BlockCipher k where
  bitsPerBlock : Nat
  maximumBlocks : Nat
  encryptBlock : k -> Bits bitsPerBlock -> Security (Bits bitsPerBlock)
  decryptBlock : k -> Bits bitsPerBlock -> Bits bitsPerBlock
  -- blockTranslation : k -> Iso b b
  -- blockTranslation = MkIso (encryptBlock k) (decryptBlock k)

instance BlockCipher a => BlockCipher (Security a) where
  bitsPerBlock = bitsPerBlock
  maximumBlocks = maximumBlocks
  encryptBlock cipher block = cipher >>= flip encryptBlock block
  decryptBlock (MkSecure _ a) = decryptBlock a
         
||| The encryption mode specifies how to apply a block cipher to multiple blocks
public
class EncryptionMode (em : Nat -> Type) where
  encryptBlocks' : BlockCipher k
                   => k -> em bitsPerBlock -> List (Bits bitsPerBlock)
                   -> (Security (List (Bits bitsPerBlock)), em bitsPerBlock)
  decryptBlocks' : BlockCipher k
                   => k -> em bitsPerBlock -> List (Bits bitsPerBlock)
                   -> (List (Bits bitsPerBlock), em bitsPerBlock)

instance EncryptionMode a => EncryptionMode (\bits => Security (a bits)) where
  encryptBlocks' key (MkSecure level mode) message =
    let (MkSecure level' ciph, iv) = encryptBlocks' key mode message
    in (MkSecure (level <+> level') ciph, pure iv)
  decryptBlocks' key (MkSecure _ mode) ciph = second pure (decryptBlocks' key mode ciph)

public
encryptBlocks : (BlockCipher k, EncryptionMode em)
                => k -> em bitsPerBlock -> List (Bits bitsPerBlock)
                -> (Security (List (Bits bitsPerBlock)), Security (em bitsPerBlock))
encryptBlocks key em blocks =
  second (MkSecure (Insecure ["initialization vector is the result of encryption"])) (encryptBlocks' key em blocks)
public
decryptBlocks : (BlockCipher k, EncryptionMode em)
                => k -> em bitsPerBlock -> List (Bits bitsPerBlock)
                -> (List (Bits bitsPerBlock), Security (em bitsPerBlock))
decryptBlocks key em blocks =
  second (MkSecure (Insecure ["initialization vector is the result of decryption"])) (decryptBlocks' key em blocks)

data ElectronicCookbook : Nat -> Type where
  ECB : ElectronicCookbook n

-- This is ECB (Electronic Cookbook) - no initialization vector
-- ECB should be considered insecure regardless of the cipher used
instance EncryptionMode ElectronicCookbook where
  encryptBlocks' key em blocks =
    ((case (sequence (map (encryptBlock key) blocks), 1 < length blocks) of
         (MkSecure level ciph, True) =>
           MkSecure (level <+> Insecure ["ECB was used on more than one block"])
                    ciph
         (ciph, False) => ciph),
     em)
  decryptBlocks' key em blocks = (map (decryptBlock key) blocks, em)

data CipherBlockChainingMode : Nat -> Type where
  CBC : Bits n -> CipherBlockChainingMode n

instance EncryptionMode CipherBlockChainingMode where
  encryptBlocks' _ em [] = (pure List.Nil, em)
  encryptBlocks' key (CBC iv) (plain::rest) =
    let (MkSecure level ciph) = encryptBlock key (plain `xor` iv)
    in first (scons (MkSecure level ciph)) (encryptBlocks' key (CBC ciph) rest)
  decryptBlocks' _ em [] = ([], em)
  decryptBlocks' key (CBC iv) (ciph::rest) =
    first ((::) (decryptBlock key ciph `xor` iv)) (decryptBlocks' key (CBC ciph) rest)

data PropagatingCipherBlockChainingMode : Nat -> Type where
  PCBC : Bits n -> PropagatingCipherBlockChainingMode n

instance EncryptionMode PropagatingCipherBlockChainingMode where
  encryptBlocks' _ em [] = (pure List.Nil, em)
  encryptBlocks' key (PCBC iv) (plain::rest) =
    let (MkSecure level ciph) = encryptBlock key (plain `xor` iv)
    in first (scons (MkSecure level ciph)) (encryptBlocks' key (PCBC (plain `xor` ciph)) rest)
  decryptBlocks' _ em [] = ([], em)
  decryptBlocks' key (PCBC iv) (ciph::rest) =
    let plain = decryptBlock key ciph `xor` iv
    in first ((::) plain) (decryptBlocks' key (PCBC (plain `xor` ciph)) rest)

data CipherFeedbackMode : Nat -> Type where
  CFB : Bits n -> CipherFeedbackMode n
  
instance EncryptionMode CipherFeedbackMode where
  encryptBlocks' _ em [] = (pure List.Nil, em)
  encryptBlocks' key (CFB iv) (plain::rest) =
    let (MkSecure level ciph) = pure (xor plain) <$> encryptBlock key iv
    in first (scons (MkSecure level ciph)) (encryptBlocks' key (CFB ciph) rest)
  decryptBlocks' _ em [] = ([], em)
  decryptBlocks' key (CFB iv) (ciph::rest) =
    first ((::) (decryptBlock key iv `xor` ciph)) (decryptBlocks' key (CFB ciph) rest)

data OutputFeedbackMode : Nat -> Type where
  OFB : Bits n -> OutputFeedbackMode n

instance EncryptionMode OutputFeedbackMode where
  encryptBlocks' _ em [] = (pure List.Nil, em)
  encryptBlocks' key (OFB iv) (plain::rest) =
    let (MkSecure level newIV) = encryptBlock key iv
    in first (scons (MkSecure level (plain `xor` newIV))) (encryptBlocks' key (OFB newIV) rest)
  decryptBlocks' _ em [] = ([], em)
  decryptBlocks' key (OFB iv) (ciph::rest) =
    let newIV = decryptBlock key iv
    in first ((::) (ciph `xor` newIV)) (decryptBlocks' key (OFB newIV) rest)

instance (BlockCipher bc, EncryptionMode em) =>
         SymmetricCipher (bc, em bitsPerBlock) where
  bitsPerChunk = bitsPerBlock
  encryptMessage c message = fst (uncurry encryptBlocks c message)
  decryptMessage c text = fst (uncurry decryptBlocks c text)
