module Data.Crypto.Encryption.Block.EncryptionMode

import Data.Bits

import Data.Crypto.Encryption
import Data.Crypto.Encryption.Block
import Data.Crypto.Encryption.Stream
import Data.Crypto.Util

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

-- ||| `OutputFeedbackMode` allows any `BlockCipher` to be treated as a
-- ||| `StreamCipher`.
-- implementation BlockCipher b bitsPerBlock _ => StreamCipher (b, OutputFeedbackMode bitsPerBlock) bitsPerBlock where
--   generateKeystream (b, OFB iv) =
--     let newIV = encryptBlock b iv
--     in newIV :: (generateKeystream (b, OFB newIV))

||| Counter mode takes a nonce, an initial “counter” value, and a function to
||| get the next counter value.
data CounterMode : Nat -> Type where
  CTR : Bits m -> Bits n -> (Bits n -> Bits n) -> CounterMode (m + n)

||| The most common counter mode starts at 0 and moves sequentially through the
||| natural numbers.
incrementalCTR : Bits m -> CounterMode (m + n)
incrementalCTR m = CTR m (intToBits 0) (plus (intToBits 1))

implementation EncryptionMode CounterMode where
  encryptBlocks _ _ [] = []
  encryptBlocks key (CTR nonce counter f) (plain::rest) =
    (plain `xor` encryptBlock key (append nonce counter))
      :: encryptBlocks key (CTR nonce (f counter) f) rest
  decryptBlocks _ _ [] = []
  decryptBlocks key (CTR nonce counter f) (ciph::rest) =
    (ciph `xor` decryptBlock key (append nonce counter))
      :: decryptBlocks key (CTR nonce (f counter) f) rest

-- ||| 'CounterMode' allows any `BlockCipher` to be treated as a `StreamCipher`.
-- implementation BlockCipher b bitsPerBlock _ => StreamCipher (b, CounterMode bitsPerBlock) bitsPerBlock where
--   generateKeystream (b, CTR nonce counter f) =
--     encryptBlock b (append nonce counter)
--       :: generateKeystream (b, CTR nonce (f counter) f)
