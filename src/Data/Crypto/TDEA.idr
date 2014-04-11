module Data.Crypto.TDEA

import Data.Crypto.DEA

%default total
%access private

public
forwardTDEA1 : Bits 64 -> Bits 64 -> Bits 64 -> Bits 64 -> Bits 64
forwardTDEA1 d key1 key2 key3 =
  forwardDEA (inverseDEA (forwardDEA d key1) key2) key3

public
forwardTDEA2 : Bits 64 -> Bits 64 -> Bits 64 -> Bits 64
forwardTDEA2 d key1 key2 = forwardTDEA1 d key1 key2 key1

public
inverseTDEA1 : Bits 64 -> Bits 64 -> Bits 64 -> Bits 64 -> Bits 64
inverseTDEA1 d key1 key2 key3 =
  inverseDEA (forwardDEA (inverseDEA d key3) key2) key1

public
inverseTDEA2 : Bits 64 -> Bits 64 -> Bits 64 -> Bits 64
inverseTDEA2 d key1 key2 = inverseTDEA1 d key1 key2 key1
