idris-crypto
============

This project looks to develop cryptographic primitives using the general purpose functional language [Idris](http://www.idris-lang.org).
Idris has features influenced by Haskell and ML, including:

* Full dependent types with dependent pattern matching
* where clauses, with rule, simple case expressions, pattern matching let and lambda bindings
* Dependent records with projection and update
* Type classes
* Monad comprehensions
* Syntactic conveniences for lists, tuples, dependent pairs
* do notation and idiom brackets
* significant syntax
* Extensible syntax
* Tactic based theorem proving (influenced by Coq)
* Cumulative universes
* Totality checking
* Simple foreign function interface (to C)
* Hugs style interactive environment

It is important to note that the `Idris` language is first and foremost a research project, and thus the tooling provided by `idris-crypto` should not necessarily be seen as production ready nor for industrial use.

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

* 3DES


