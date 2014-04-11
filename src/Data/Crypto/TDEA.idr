module Data.Crypto.TDEA

import Data.Crypto.DEA

%default total
%access private

public
TDEA1Key : Type
TDEA1Key = Vect 3 DEAKey

public
TDEA2Key : Type
TDEA2Key = Vect 2 DEAKey

public
forwardTDEA1 : Bits 64 -> TDEA1Key -> Bits 64
forwardTDEA1 d key =
  forwardDEA (inverseDEA (forwardDEA d (index 0 key)) (index 1 key))
             (index 2 key)

public
forwardTDEA2 : Bits 64 -> TDEA2Key -> Bits 64
forwardTDEA2 d key = forwardTDEA1 d (key ++ [index 0 key])

public
inverseTDEA1 : Bits 64 -> TDEA1Key -> Bits 64
inverseTDEA1 d key =
  inverseDEA (forwardDEA (inverseDEA d (index 2 key)) (index 1 key))
             (index 0 key)

public
inverseTDEA2 : Bits 64 -> TDEA2Key -> Bits 64
inverseTDEA2 d key = inverseTDEA1 d (key ++ [index 0 key])
