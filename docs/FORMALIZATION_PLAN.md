# Formalization plan

## Existing Mathlib infrastructure

The project is pinned to Lean 4.32.0 and Mathlib v4.32.0.

Mathlib already provides the core graph layer needed here:

- `SimpleGraph` and adjacency;
- `SimpleGraph.fromRel`, which symmetrizes a relation and removes loops;
- `SimpleGraph.Connected` and reachability;
- finite neighbour sets and `SimpleGraph.degree`;
- independent sets `SimpleGraph.IsIndepSet` and `IsNIndepSet`;
- the noncomputable independence number `SimpleGraph.indepNum`;
- finite-set and finite-cardinality infrastructure.

The project should reuse those definitions.

Zero forcing is project-local because Mathlib does not currently supply the exact invariant needed here.

## Zero-forcing definition

The bootstrap definition uses:

1. `CanForce G blue u v`: u is blue, v is white and adjacent to u, and every white neighbour of u equals v;
2. `ForceStep G blue blue'`: one legal force adds exactly v;
3. `IsZeroForcingSet G blue`: the reflexive-transitive closure of legal force steps reaches `Finset.univ`;
4. `zeroForcingNumber G`: the infimum of the cardinalities of zero-forcing sets.

For finite graphs this is the standard existential forcing-sequence formulation. Before final submission, add small lemmas establishing the expected minimum/witness interface and audit the definition directly against Fischer's prose.

## Explicit graph

Use `Fin 24` as the vertex type and encode the published graph with the 30-edge list reconstructed from the graph6 string. The graph definition uses `SimpleGraph.fromRel`.

Keep the source graph6 string outside Lean as a transcription certificate. The independent checker must continue to verify that the Lean edge list and the source graph6 encoding agree.

## Proof decomposition

Work in this order, stopping after each concrete obligation is kernel-checked:

1. **Graph identity and structure**
   - edge-list sanity;
   - 24 vertices;
   - connected;
   - every degree <= 3;
   - preferably 30 edges and the published degree multiset as auxiliary checks.

2. **Independence lower bound**
   - prove the explicit 9-set is independent;
   - conclude 9 <= indepNum.

3. **Independence upper bound**
   - prefer a compact branch decomposition or a verified small checker over a giant opaque `decide`;
   - prove every independent set has size <= 9;
   - conclude indepNum = 9.

4. **Zero-forcing upper bound**
   - prove the explicit 11-set is zero forcing;
   - expose the concrete force sequence.

5. **Zero-forcing lower bound**
   - formalise forts and the fact that every zero-forcing set meets every fort, or prove an equally transparent finite alternative;
   - reproduce the branch values t=12, h=3, m3=12, m4=25;
   - reduce the lower-bound search to the source's 17,712 candidates;
   - prove all candidates of size <=10 fail.

6. **Main theorem**
   - package the explicit graph facts as alpha(H)=9 and Z(H)=11;
   - derive Z(H)>alpha(H)+1.

## Certificate discipline

Preferred order:

1. short conceptual argument;
2. explicit finite certificate plus small verified checker;
3. structured enumeration with a human-readable reduction;
4. direct kernel computation only where genuinely small.

The final proof should not hide the lower bounds behind an enormous unstructured `decide` or `native_decide`. Computation is acceptable when the checked predicate, completeness argument, and case count are explicit.

The bootstrap `Challenge.lean` and `Solution.lean` contain deliberate `sorry` placeholders. They are not evidence of completion.
