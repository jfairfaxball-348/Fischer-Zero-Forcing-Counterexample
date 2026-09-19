# Source and provenance

## Primary source

Mikko Fischer, **"A counterexample to the zero forcing versus independence conjecture for cubic and subcubic graphs"**, arXiv:2607.23664v1 (2026), Theorem 2.

Stable identifier: arXiv:2607.23664.

The note states the TxGraffiti conjecture (2017), as recorded as Conjecture 2 in the survey of Davila, Brimkov and Pepper, in the form:

> If G is not K4, is connected, and has maximum degree at most 3, then Z(G) <= alpha(G) + 1.

Fischer notes that the survey's Lean 4 appendix carries an additional regularity/cubic hypothesis. The 24-vertex graph H refutes the textual subcubic conjecture; Fischer's separate 36-vertex graph G refutes the cubic form.

## Exact 24-vertex graph

The paper defines a general construction G(F). For H it takes F = K3 with distinguished attachment vertex z. The resulting graph H = G(K3) has 24 vertices and 30 edges.

The published graph6 string is:

```
W{CGW_@?Y??@?@?@_@??@??K_????G??C??B??@????_??B
```

It is copied verbatim to `reference/H24.g6`.

Using the standard graph6 order gives the following canonical labels:

- c0,c1,c2 = 0,1,2;
- r0 = 3; its two K3 copies are (z,a,b)=(4,5,6) and (7,8,9);
- r1 = 10; its two K3 copies are (11,12,13) and (14,15,16);
- r2 = 17; its two K3 copies are (18,19,20) and (21,22,23).

The complete edge list is:

```
0-1  0-2  1-2
0-3
3-4  4-5  4-6  5-6
3-7  7-8  7-9  8-9
1-10
10-11  11-12  11-13  12-13
10-14  14-15  14-16  15-16
2-17
17-18  18-19  18-20  19-20
17-21  21-22  21-23  22-23
```

The independent reconstruction script decodes the graph6 string independently and checks that this edge list is exactly the same graph under this labelling.

## Numerical claims and source certificates

Fischer's Theorem 2 states:

- alpha(H) = 9;
- Z(H) = 11.

The paper gives an independent-set witness pattern: in each branch, take r_j and one non-attachment vertex from each of its two K3 copies. In the canonical labels this repository uses:

```
{3,5,8,10,12,15,17,19,22}
```

For Z(H) <= 11 the paper takes z and a from five of the six K3 copies and a alone from the sixth. Choosing the last copy as the exceptional copy gives:

```
{4,5,7,8,11,12,14,15,18,19,22}
```

For Z(H) >= 11 the paper uses forts. For each 7-vertex branch it reports:

- 12 forts contained in that branch;
- minimum branch hitting-set size h = 3;
- 12 size-3 branch hitting sets;
- 25 size-4 branch hitting sets.

This reduces all possible zero-forcing sets of size at most 10 to 17,712 candidates, each of which fails to force.

`verification/check_fischer_h.py` independently reconstructs these counts using only Python's standard library and verifies the same finite claims.

## Minimality

The 2026 note does **not** establish in this paper that the 24-vertex example is minimum-order. It explicitly says that the minimum order of a counterexample is treated in a companion paper. Version 1 of this repository therefore makes no minimality claim.

## Reproduction versus new work

Source mathematics:

- the graph construction;
- the graph6 certificate;
- alpha(H)=9;
- Z(H)=11;
- the witness patterns and fort reduction.

Repository contribution intended here:

- faithful Lean 4 definitions;
- kernel-checked finite certificates/proofs;
- independent transcription checking;
- Palomar-oriented packaging and provenance.

## Existing formalisation search

Bootstrap searches on 2026-09-19 found no indexed public Lean formalisation, Palomar registration, or GitHub repository for this exact arXiv result. This is a time-sensitive negative search result, not a permanent claim. Recheck Palomar, GitHub, and public formalisation indexes immediately before submission.
