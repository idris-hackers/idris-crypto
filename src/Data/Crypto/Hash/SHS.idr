||| [specification](http://csrc.nist.gov/publications/fips/fips180-4/fips-180-4.pdf)
module Data.Crypto.Hash.SHS

import Data.Bits
import Data.Crypto.Hash
import Data.Crypto.Util
import Data.Fin
import Data.Mod
import Data.Vect


-- Functions

ch : Bits n -> Bits n -> Bits n -> Bits n
ch x y z = (x `and` y) `xor` (complement x `and` z)

parity : Bits n -> Bits n -> Bits n -> Bits n
parity x y z = (x `xor` y) `xor` z

maj : Bits n -> Bits n -> Bits n -> Bits n
maj x y z = ((x `and` y) `xor` (x `and` z)) `xor` (y `and` z)

f : Fin 80 -> Bits 32 -> Bits 32 -> Bits 32 -> Bits 32
f t = if t <= 19 then ch
 else if t <= 39 then parity
 else if t <= 59 then maj
                 else parity

Σ256_0 : Bits 32 -> Bits 32
Σ256_0 x = (rotateRight 2 x `xor` rotateRight 13 x) `xor` rotateRight 22 x

Σ256_1 : Bits 32 -> Bits 32
Σ256_1 x = (rotateRight 6 x `xor` rotateRight 11 x) `xor` rotateRight 25 x

σ256_0 : Bits 32 -> Bits 32
σ256_0 x = (rotateRight 7 x `xor` rotateRight 18 x) `xor` shiftRightLogical x (intToBits 3)

σ256_1 : Bits 32 -> Bits 32
σ256_1 x = (rotateRight 17 x `xor` rotateRight 19 x) `xor` shiftRightLogical x (intToBits 10)

Σ512_0 : Bits 64 -> Bits 64
Σ512_0 x = (rotateRight 28 x `xor` rotateRight 34 x) `xor` rotateRight 39 x

Σ512_1 : Bits 64 -> Bits 64
Σ512_1 x = (rotateRight 14 x `xor` rotateRight 18 x) `xor` rotateRight 41 x

σ512_0 : Bits 64 -> Bits 64
σ512_0 x = (rotateRight 1 x `xor` rotateRight 8 x) `xor` shiftRightLogical x (intToBits 7)

σ512_1 : Bits 64 -> Bits 64
σ512_1 x = (rotateRight 19 x `xor` rotateRight 61 x) `xor` shiftRightLogical x (intToBits 6)

-- Constants

const1 : Vect 80 (Bits 32)
const1 = concat (map (replicate 20 . intToBits)
                     [0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6])

const256 : Vect 64 (Bits 32)
const256 = map intToBits
               [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
                0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
                0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
                0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
                0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
                
const512 : Vect 80 (Bits 64)
const512 = map intToBits
               [0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
                0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
                0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
                0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
                0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
                0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
                0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
                0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
                0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
                0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
                0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
                0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
                0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
                0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
                0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
                0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
                0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
                0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
                0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
                0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

-- Preprocessing

pad512 : Bits l -> Bits ((div l 512 + 1) * 512)
pad512 {l=l} message = append message
                              (append (intToBits 1)
                                      (append (the (Bits (modToNat (the (Mod 512) (448 - (natToMod l + 1))))) (intToBits 0))
                                              (the (Bits 64) (intToBits (cast l)))))

pad1024 : Bits l -> Bits ((div l 1024 + 1) * 1024)
pad1024 {l=l} message = append message
                               (append (intToBits 1)
                                       (append (the (Bits (modToNat (the (Mod 1024) (896 - (natToMod l + 1))))) (intToBits 0))
                                               (the (Bits 128) (intToBits (cast l)))))

parse512 : Bits (n * 512) -> Vect n (Bits 512)
parse512 = partition

parse1024 : Bits (n * 1024) -> Vect n (Bits 1024)
parse1024 = partition

-- Algorithms

data SecureHashAlgorithm1 : Type where
  SHA1 : Vect 5 (Bits 32) -> SecureHashAlgorithm1

vectIndex : (i : Nat) -> Vect (S n) a -> LTE i n -> a
vectIndex i v lte = index (natToFi i lte) v

sha1sched' : Vect 16 (Bits 32) -> Vect t (Bits 32) -> Bits 32
sha1sched' {t=t} M W =
  case isLTE t 15 of
    Yes lte => vectIndex t M lte
    No gt => rotateLeft 1 (foldl1 xor
                          --         (map (\off -> index (weakenN' (strMinus (natToFi t lteRefl) off)) W)
                          --              [3, 8, 14, 16]))
            [Vect.index (weakenN' (strMinus (natToFi t lteRefl)  3)) W,
             Vect.index (weakenN' (strMinus (natToFi t lteRefl)  8)) W,
             Vect.index (weakenN' (strMinus (natToFi t lteRefl) 14)) W,
             Vect.index (weakenN' (strMinus (natToFi t lteRefl) 16)) W])

-- NB: `foldl` doesn’t work here. Can we make something like `foldl`, but each
--      step is one element, and we get a Vect of elements back at the end?  
sha1sched : Vect 16 (Bits 32) -> Vect 80 (Bits 32)
sha1sched mpart = foldl (\W, t => sha1sched' {t=t} mpart W) [] [0..79]

implementation Hash SecureHashAlgorithm1 512 160 where
  initialize _ = toList . parse512 . pad512 . Util.concat
  initialContext _ = SHA1 (map intToBits
                               [0x67452301,
                                0xefcdab89,
                                0x98badcfe,
                                0x10325476,
                                0xc3d2e1f0])
  updateContext (SHA1 v) block = SHA1 (zipWith plus (foldl for v [0..79]) v) where
    -- seems like we could do this in one pass
    W : Vect 80 (Bits 32)
    W = sha1sched (partition block)
    for : Vect 5 (Bits 32) -> Fin 80 -> Vect 5 (Bits 32)
    for [a, b, c, d, e] t =
      [Vect.foldl1 plus [rotateLeft 5 a, f t b c d, e, index t const1, index t W],
       a,
       rotateLeft 30 b,
       c,
       d]
  finalize (SHA1 v) = concat v

data SecureHashAlgorithm256 : Type where
  SHA256 : Vect 8 (Bits 32) -> SecureHashAlgorithm256

hash256 : Vect 8 (Bits 32) -> Bits 512 -> Vect 8 (Bits 32)

implementation Hash SecureHashAlgorithm256 512 256 where
  initialize _ = toList . parse512 . pad512 . Util.concat
  initialContext _ = SHA256 (map intToBits
                                 [0x6a09e667,
                                  0xbb67ae85,
                                  0x3c6ef372,
                                  0xa54ff53a,
                                  0x510e527f,
                                  0x9b05688c,
                                  0x1f83d9ab,
                                  0x5be0cd19])
  updateContext (SHA256 v) = SHA256 . hash256 v
  finalize (SHA256 v) = concat v

data SecureHashAlgorithm224 : Type where
  SHA224 : Vect 8 (Bits 32) -> SecureHashAlgorithm224

implementation Hash SecureHashAlgorithm224 512 224 where
  initialize _ = toList . parse512 . pad512 . Util.concat
  initialContext _ = SHA224 (map intToBits
                                 [0xc1059ed8,
                                  0x367cd507,
                                  0x3070dd17,
                                  0xf70e5939,
                                  0xffc00b31,
                                  0x68581511,
                                  0x64f98fa7,
                                  0xbefa4fa4])
  updateContext (SHA224 v) = SHA224 . hash256 v
  finalize (SHA224 v) = concat (take 7 v)

data SecureHashAlgorithm512 : Type where
  SHA512 : Vect 8 (Bits 64) -> SecureHashAlgorithm512
  
hash512 : Vect 8 (Bits 64) -> Bits 1024 -> Vect 8 (Bits 64)

implementation Hash SecureHashAlgorithm512 1024 512 where
  initialize _ = toList . parse1024 . pad1024 . Util.concat
  initialContext _ = SHA512 (map intToBits
                                 [0x6a09e667f3bcc908,
                                  0xbb67ae8584caa73b,
                                  0x3c6ef372fe94f82b,
                                  0xa54ff53a5f1d36f1,
                                  0x510e527fade682d1,
                                  0x9b05688c2b3e6c1f,
                                  0x1f83d9abfb41bd6b,
                                  0x5be0cd19137e2179])
  updateContext (SHA512 v) = SHA512 . hash512 v
  finalize (SHA512 v) = concat v

data SecureHashAlgorithm512_224 : Type where
  SHA512_224 : Vect 8 (Bits 64) -> SecureHashAlgorithm512_224

implementation Hash SecureHashAlgorithm512_224 1024 224 where
  initialize _ = toList . parse1024 . pad1024 . Util.concat
  initialContext _ = SHA512_224 (map intToBits
                                     [0x8C3D37C819544DA2,
                                      0x73E1996689DCD4D6,
                                      0x1DFAB7AE32FF9C82, 
                                      0x679DD514582F9FCF,
                                      0x0F6D2B697BD44DA8,
                                      0x77E36F7304C48942,
                                      0x3F9D85A86A1D36C8,
                                      0x1112E6AD91D692A1])
  updateContext (SHA512_224 v) = SHA512_224 . hash512 v
  finalize (SHA512_224 v) = truncate (concat (take 4 v))

data SecureHashAlgorithm512_256 : Type where
  SHA512_256 : Vect 8 (Bits 64) -> SecureHashAlgorithm512_256

implementation Hash SecureHashAlgorithm512_256 1024 256 where
  initialize _ = toList . parse1024 . pad1024 . Util.concat
  initialContext _ = SHA512_256 (map intToBits
                                     [0x22312194FC2BF72C,
                                      0x9F555FA3C84C64C2,
                                      0x2393B86B6F53B151,
                                      0x963877195940EABD,
                                      0x96283EE2A88EFFE3,
                                      0xBE5E1E2553863992,
                                      0x2B0199FC2C85B8AA,
                                      0x0EB72DDC81C52CA2])
  updateContext (SHA512_256 v) = SHA512_256 . hash512 v
  finalize (SHA512_256 v) = concat (take 4 v)

data SecureHashAlgorithm384 : Type where
  SHA384 : Vect 8 (Bits 64) -> SecureHashAlgorithm384

implementation Hash SecureHashAlgorithm384 1024 384 where
  initialize _ = toList . parse1024 . pad1024 . Util.concat
  initialContext _ = SHA384 (map intToBits
                                 [0xcbbb9d5dc1059ed8,
                                  0x629a292a367cd507,
                                  0x9159015a3070dd17,
                                  0x152fecd8f70e5939,
                                  0x67332667ffc00b31,
                                  0x8eb44a8768581511,
                                  0xdb0c2e0d64f98fa7,
                                  0x47b5481dbefa4fa4])
  updateContext (SHA384 v) = SHA384 . hash512 v
  finalize (SHA384 v) = concat (take 6 v)
