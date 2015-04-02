module Data.Crypto.Hash.MD5

import Data.Crypto
import Data.Crypto.Hash
import Data.Crypto.Util

%default total

public
data MessageDigest5 : Type where
  MD5 : Vect 4 (Bits 32) -> MessageDigest5

s : Vect 64 Nat
-- s = concat (map (Prelude.Vect.concat . replicate 4)
--                 [[7, 12, 17, 22],
--                  [5,  9, 14, 20],
--                  [4, 11, 16, 23],
--                  [6, 10, 15, 21]])
s = [7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,
     5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,
     4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,
     6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21]

K : Vect 64 (Bits 32)
-- K = map (\i => floor (abs (sin (i + 1)) * (2 `pow` 32))) [0..63]
K = map intToBits
        [0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
         0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
         0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
         0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
         0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
         0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
         0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
         0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
         0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
         0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
         0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
         0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
         0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
         0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
         0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
         0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

instance Hash MessageDigest5 512 128 where
  initialize {m=m} {n=n} msg =
    let msgLength = m * n
    in let padSize = 448 - (msgLength `mod` 512)
       in fst (partition' (append (concat msg)
                                  (append (intToBits {n=padSize} (cast (power 2 padSize `div` 2)))
                                          (intToBits {n=64} (cast msgLength)))))
  initialContext = MD5 (map intToBits [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476])
  updateContext (MD5 [A, B, C, D]) chunk with (the (Vect 16 (Bits 32)) (partition chunk))
    | M = MD5 (zipWith plus [A, B, C, D] (foldl iteration [A, B, C, D] [0..63]))
    where iteration : Vect 4 (Bits 32) -> Fin 64 -> Vect 4 (Bits 32)
          iteration [A, B, C, D] i =
            let iNat = finToNat i
            in let (F, g) =
                     if iNat < 16
                     then ((B `and` C) `or` (complement B `and` D),
                           iNat `tightmod` 16)
                     else if iNat < 32
                          then ((D `and` B) `or` (complement D `and` C),
                                (iNat*5 + 1) `tightmod` 16)
                          else if iNat < 48
                               then (B `xor` (C `xor` D),
                                     (iNat*3 + 5) `tightmod` 16)
                               else (C `xor` (B `or` complement D),
                                     (iNat*7) `tightmod` 16)
               in [C,
                   B,
                   B `plus` rotateLeft ((A `plus` F) `plus` (index i K `plus` index g M))
                                       (index i s),
                   D]
  finalize (MD5 context) = concat context

-- Tests

-- dummyMD5 = (MD5 (map intToBits [0, 0, 0, 0]))

-- shouldMatch_ : hashMessage dummyMD5 [] = intToBits 0xd41d8cd98f00b204e9800998ecf8427e
-- shouldMatch_ = refl

-- shouldMatch_a : hashMessage dummyMD5 (map (intToBits {n=8}) [97]) = intToBits 0cc175b9c0f1b6a831c399e269772661
-- shouldMatch_a = refl

-- shouldMatch_abc : hashMessage dummyMD5 (map (intToBits {n=8}) [97, 98, 99]) = intToBits 900150983cd24fb0d6963f7d28e17f72
-- shouldMatch_abc = refl

