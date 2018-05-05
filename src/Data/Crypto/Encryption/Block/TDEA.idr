module Data.Crypto.Encryption.TDEA

import Data.Vect

import Data.Crypto.Encryption.Block
import Data.Crypto.Encryption.Block.DEA
import Data.Fin

%default total
%access public export

TDEA1Key : Type
TDEA1Key = Vect 3 DEAKey

TDEA2Key : Type
TDEA2Key = Vect 2 DEAKey

data TripleDataEncryptionAlgorithm : Fin 2 -> Type where
  TDEA1 : TDEA1Key -> TripleDataEncryptionAlgorithm 0
  TDEA2 : TDEA2Key -> TripleDataEncryptionAlgorithm 1

implementation BlockCipher (TripleDataEncryptionAlgorithm 0) 64 (power 2 32) where
  encryptBlock (TDEA1 key) block =
    encryptBlock (DEA (index 2 key))
                 (decryptBlock (DEA (index 1 key))
                               (encryptBlock (DEA (index 0 key)) block))
  decryptBlock (TDEA1 key) block =
    decryptBlock (DEA (index 0 key))
                 (encryptBlock (DEA (index 1 key))
                               (decryptBlock (DEA (index 2 key)) block))

implementation BlockCipher (TripleDataEncryptionAlgorithm 1) 64 (power 2 20) where
  encryptBlock (TDEA2 key) = encryptBlock (TDEA1 (key ++ [index 0 key]))
  decryptBlock (TDEA2 key) = decryptBlock (TDEA1 (key ++ [index 0 key]))
