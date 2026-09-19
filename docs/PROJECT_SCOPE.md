# Project scope

Version 1 of this project is only:

> Formal verification of Fischer's explicit 24-vertex connected subcubic counterexample satisfying alpha(H) = 9 and Z(H) = 11, sufficient to certify Z(H) > alpha(H) + 1.

The project is a reproduction-and-formalization effort. The underlying counterexample is Mikko Fischer's result; no novelty is claimed for that mathematical discovery.

Explicitly out of scope for version 1 unless a later deliberate scope change is made:

- proving that the 24-vertex example is minimal;
- formalising Fischer's 36-vertex cubic example;
- proving an infinite family;
- developing a general-purpose zero-forcing library;
- attacking repaired or unrelated open zero-forcing conjectures;
- expanding into a broad graph-theory research programme.

The project should prefer a short, auditable finite proof over general abstraction. Any abstraction added must directly reduce the trusted or review surface of the 24-vertex theorem.
