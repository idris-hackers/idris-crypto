module Data.Crypto.Encryption.ARC4

import Control.Monad.State
import Data.Mod

import Data.Crypto.Util
import Data.Crypto.Encryption.StreamCipher

%default total
%access private

KeySize : Type
KeySize = (n : Fin 256 ** so (n /= fZ))

public
ARC4Key : KeySize -> Type
ARC4Key (n ** p) = Vect (finToNat n) (Mod 256) -- should be Byte, but can’t convert yet

postulate stillNotZero : (x : Fin (S n)) -> so (x /= fZ) -> so (cast x /= Z)

public
data AllegedRivestCipher4 : KeySize -> Type where
  ARC4 : ARC4Key n -> AllegedRivestCipher4 n

KSA : ARC4Key n -> Vect 256 (Mod 256)
KSA {n=(n ** p)} key =
  fst (runIdentity (runStateT (nextJ (map Prelude.Classes.fromInteger (fromList [0..255])))
                              (0, 0)))
  where
    nextJ : Vect 256 (Mod 256) -> State (Mod 256, Mod 256) (Vect 256 (Mod 256))
    nextJ S = do
      (i, j) <- get
      let ind = tightmod (cast i) (cast n) (stillNotZero n p)
      let pos = index ind key
      let newJ = the (Mod 256) (j + index (cast i) S + pos)
      let newS = (swap (cast i) (cast newJ) S)
      if i == last
        then
          return newS
        else do
          put (i + 1, newJ)
          nextJ newS

PGRA : Mod 256 -> Mod 256 -> Vect 256 (Mod 256) -> Stream Byte
PGRA i j S = let newI = i + 1
             in let newJ = j + index (cast newI) S
                in let newS = swap (cast newI) (cast newJ) S
                   in Prelude.Stream.(::)
                      (modToBits (index (cast (index (cast newI) newS + index (cast newJ) newS)) newS))
                      (PGRA newI newJ newS)

instance StreamCipher (AllegedRivestCipher4 n) where
  bitsPerUnit = 8
  generateKeystream (ARC4 key) = PGRA 0 0 (KSA key)
