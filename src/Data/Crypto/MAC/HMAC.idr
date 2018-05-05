module Data.Crypto.MAC.HMAC

import Data.Bits
import Data.Vect

import Data.Crypto.Hash
import Data.Crypto.MAC
import Data.Crypto.Util

%default total
%access private

public export
data HashMAC : Nat -> Type -> Type where
  HMAC : Bits n -> h -> HashMAC n h

formatKey : Hash h b o => HashMAC n h -> Bits b
formatKey {b=b} {n=n} (HMAC k h) =
  if n <= b then zeroExtend k else zeroExtend (hashMessage h [k])

ipad : Hash h b o => HashMAC n h -> Bits b
ipad {b=b} _ = concat (replicate (b `div` 8) (intToBits {n=8} 0x36))

opad : Hash h b o => HashMAC n h -> Bits b
opad {b=b} _ = concat (replicate (b `div` 8) (intToBits 0x5c))

implementation Hash h b o => Signer (HashMAC n h) b o where
  signMessage (HMAC key hash) message = 
    let fixedKey = formatKey (HMAC key hash)
    in hashMessage hash
                   (append (fixedKey `xor` opad)
                           (hashMessage hash
                                        (append (fixedKey `xor` ipad)
                                                (concat message))))

-- TODO: Remove when the default impl on MAC works.
implementation Hash h b o => Verifier (HashMAC n h) b o where
  verifyMessage key message digest = digest == signMessage key message

implementation Hash h b o => MAC (HashMAC n h) b o where
