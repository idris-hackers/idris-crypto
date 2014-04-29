idris-crypto
============

This project looks to develop cryptographic primitives using the general purpose functional language [Idris](http://www.idris-lang.org).

It is important to note that the Idris language is first and foremost a research project, and thus the tooling provided by `idris-crypto` should not necessarily be seen as production ready nor for industrial use.

## Motivation

Cryptography is something that is important to get right. It is also difficult to get right. Most languages make it too easy to shoot yourself in the foot ([buffer overflows](http://heartbleed.com), [gotos](https://www.imperialviolet.org/2014/02/22/applebug.html), etc.) and even those that don’t offer limited help, but some languages make it possible to _prove_ arbitrary properties of a program and this ability can give you more confidence that your program is doing what it should. However, a cryptography library also needs to be readily usable by other software, hopefully not tied to code written in its implementation language.

Idris is a win on both sides here. On the one hand, it allows us to prove things about the code, but unlike other proof assistants has [LLVM](http://en.wikipedia.org/wiki/LLVM) and JS backends, which means that it can be linked to very much like a C library, and can also be used by JS, on both the server and client side. It is in a relatively unique position that is ideal for crypto.

## Note on Security

The security of cryptographic software libraries and implementations is a tricky thing to get right.
The notion of what makes a cryptographic software library secure can be a highly contested subject.
It is not _good enough_ that a crypto software library is _just_ functionally correct, and contains no coding errors.
A secure cryptographic software library needs to be resitant to many types of attack for instance:

* Software bugs
* Lack of adherence to a specification
* Use of a poor specification
* Use of poor primitives
* Side Channel Attacks
* Using unproven math
* Use of provably secure crypto
* the list goes on and on and on.

A language that is safer than `C` only gets you so far.
However, the use of a __general purpose language__ that supports:

* full dependent types,
* totality checking,
* tactic based theorem proving,
* code generation to other languages

arguably provides an really interesting development environment in which to explore the development of possibly _provably secure_ and _demonstrably correct_ cryptographic primitives.

## Which primitives

The list of supported primitives will be summarised here.

### Encryption
* DES **insecure**
* Triple DES
* ARC4 **insecure**

### MAC / cryptographic hash
* SHA-1 (and the rest of the SHS functions – SHA-256, SHA-512, etc.)

## Usage

The easiest way to use the library is simply using encrypt/decrypt. You can pass it either a stream cipher, or a pair of a block cypher and encryption mode:

```
> the String (encrypt (ARC4 key) "some message")
"cuhrclh,.urch,.lih.ulchu" : String
> the String (decrypt (TDEA1 [key, key, key], CFB iv) "t893gy'c.,aihntebgl'"
"some message" : String
```

If you already have lists of bytes, try encryptMessage/decryptMessage instead.

The other useful pair of operations is specific to stream ciphers:

```
> decryptStream (ARC4 key) stream
? : Stream
```

and now you’re pipelining!

## Plans / Notes

* Get a couple of the more common primitives for each type of function
* work on getting something that is easily usable via an FFI
* prove interesting properties about various primitives (look in papers for these)
* start building up higher-level components / protocols
* MOAR PRIMITIVES

* would be nice to require that insecure primitives run inside of some monad, but need some restricted escape mechanism so, EG, TDEA can be secure while DEA isn’t.
* for DSA, implement it deterministically, both to avoid bad pRNGs (which we should do in general), but also just because determinism is nice

## Contributions

Every contribution is appreciated – from documentation, to fixing typos, to adding one little function to a data structure. Even if you’re just touching Idris, dependent types, etc. for the first time. [Join in!](CONTRIBUTING.md)
