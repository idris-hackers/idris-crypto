module Data.Crypto.Encryption.Stream.ARC4

import Control.Monad.State
import Data.Fin
import Data.Vect

import Data.Mod
import Data.Crypto.Util
import Data.Crypto.Encryption
import Data.Crypto.Encryption.Stream

%default total
%access private

-- This is off-by-one to make it easy to prove non-zero with (S x) in the code.
-- Hopefully, no one will ever actually need to construct one of these
-- explicitly.
public export
KeySizeMin1 : Type
KeySizeMin1 = Fin 255

public export
ARC4Key : KeySizeMin1 -> Type
ARC4Key n = Vect (S (cast n)) (Mod 256) -- should be Byte, but can’t convert yet

public export
data AllegedRivestCipher4 : KeySizeMin1 -> Type where
  ARC4 : ARC4Key n -> AllegedRivestCipher4 n

KSA : ARC4Key n -> Vect 256 (Mod 256)
KSA {n=n} key =
  nextJ 255 0 0 (map fromInteger (fromList [0..255]))
  where
    nextJ : Nat -> Fin 256 -> Mod 256 -> Vect 256 (Mod 256) -> Vect 256 (Mod 256)
    nextJ Z i j s =
      let ind = tightmod (cast i) (S (cast n))
      in let newJ = j + index i s + index ind key
         in swap i (cast newJ) s
    nextJ (S c) i j s =
      let ind = tightmod (cast i) (S (cast n))
      in let newJ = j + index i s + index ind key
         in let newS = (swap i (cast newJ) s)
            in case strengthen (FS i) of
              Left _ => newS
              Right newI => nextJ c newI newJ newS

PGRA : Mod 256 -> Mod 256 -> Vect 256 (Mod 256) -> Stream Byte
PGRA i j S = let newI = i + 1
             in let newJ = j + index (cast newI) S
                in let newS = swap (cast newI) (cast newJ) S
                   in Prelude.Stream.(::)
                      (modToBits (index (cast (index (cast newI) newS + index (cast newJ) newS)) newS))
                      (PGRA newI newJ newS)

implementation Cipher (AllegedRivestCipher4 n) where
  bitsPerChunk = 8

{-
implementation StreamCipher (AllegedRivestCipher4 n) where
  generateKeystream (ARC4 key) = PGRA 0 0 (KSA key)
-}