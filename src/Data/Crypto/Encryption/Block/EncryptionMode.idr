module Data.Crypto.Encryption.Block.EncryptionMode

import Data.Bits
import Data.Crypto.Encryption.Block

%default total
%access public export

data ElectronicCookbook : Nat -> Type where
  ECB : ElectronicCookbook n

-- This is ECB (Electronic Cookbook) - no initialization vector
-- ECB should be considered insecure regardless of the cipher used
implementation EncryptionMode ElectronicCookbook where
  encryptBlocks key _ blocks = map (encryptBlock key) blocks
  decryptBlocks key _ blocks = map (decryptBlock key) blocks

data CipherBlockChainingMode : Nat -> Type where
  CBC : Bits n -> CipherBlockChainingMode n

implementation EncryptionMode CipherBlockChainingMode where
  encryptBlocks _ _ [] = []
  encryptBlocks key (CBC iv) (plain::rest) =
    let ciph = encryptBlock key (plain `xor` iv)
    in ciph :: encryptBlocks key (CBC ciph) rest
  decryptBlocks _ _ [] = []
  decryptBlocks key (CBC iv) (ciph::rest) =
    (decryptBlock key ciph `xor` iv) :: decryptBlocks key (CBC ciph) rest

data PropagatingCipherBlockChainingMode : Nat -> Type where
  PCBC : Bits n -> PropagatingCipherBlockChainingMode n

implementation EncryptionMode PropagatingCipherBlockChainingMode where
  encryptBlocks _ _ [] = []
  encryptBlocks key (PCBC iv) (plain::rest) =
    let ciph = encryptBlock key (plain `xor` iv)
    in ciph :: encryptBlocks key (PCBC (plain `xor` ciph)) rest
  decryptBlocks _ _ [] = []
  decryptBlocks key (PCBC iv) (ciph::rest) =
    let plain = decryptBlock key ciph `xor` iv
    in plain :: decryptBlocks key (PCBC (plain `xor` ciph)) rest

data CipherFeedbackMode : Nat -> Type where
  CFB : Bits n -> CipherFeedbackMode n

implementation EncryptionMode CipherFeedbackMode where
  encryptBlocks _ _ [] = []
  encryptBlocks key (CFB iv) (plain::rest) =
    let ciph = encryptBlock key iv `xor` plain
    in ciph :: encryptBlocks key (PCBC ciph) rest
  decryptBlocks _ _ [] = []
  decryptBlocks key (CFB iv) (ciph::rest) =
    (decryptBlock key iv `xor` ciph) :: decryptBlocks key (PCBC ciph) rest

data OutputFeedbackMode : Nat -> Type where
  OFB : Bits n -> OutputFeedbackMode n

implementation EncryptionMode OutputFeedbackMode where
  encryptBlocks _ _ [] = []
  encryptBlocks key (OFB iv) (plain::rest) =
    let newIV = encryptBlock key iv
    in (plain `xor` newIV) :: encryptBlocks key (OFB newIV) rest
  decryptBlocks _ _ [] = []
  decryptBlocks key (OFB iv) (ciph::rest) =
    let newIV = decryptBlock key iv
    in (ciph `xor` newIV) :: decryptBlocks key (OFB newIV) rest
