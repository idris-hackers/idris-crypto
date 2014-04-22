module Data.Crypto.Encryption.TDEA

import Data.Crypto.Encryption.Classes
import Data.Crypto.Encryption.DEA

%default total
%access private

public
TDEA1Key : Type
TDEA1Key = Vect 3 DEAKey

public
TDEA2Key : Type
TDEA2Key = Vect 2 DEAKey

public
data TripleDataEncryptionAlogrithm : Fin2 -> Type where
  TDEA1 : TDEA1Key -> TripleDataEncryptionAlgorithm 0
  TDEA2 : TDEA2Key -> TripleDataEncryptionAlgorithm 1

instance BlockCipher (TripleDataEncryptionAlgorithm 0) where
  bitsPerBlock = 64
  maximumBlocks = power 2 32
  encryptBlock (TDEA1 key) block =
    encryptBlock (DEA (index 2 key))
                 (decryptBlock (DEA (index 1 key))
                               (encryptBlock (DEA (index 0 key)) block))
  decryptBlock (TDEA1 key) block =
    decryptBlock (DEA (index 0 key))
                 (encryptBlock (DEA (index 1 key))
                               (decryptBlock (DEA (index 2 key)) block))

instance BlockCipher (TripleDataEncryptionAlgorithm 1) where
  bitsPerBlock = 64
  maximumBlocks = power 2 20
  encryptBlock (TDEA2 key) = encryptBlock (TDEA1 (key ++ [index 0 key]))
  decryptBlock (TDEA2 key) = decryptBlock (TDEA1 (key ++ [index 0 key]))
