# Verification protocol

The final project requires two logically distinct checks.

## 1. Formal verification

From a fresh clone at the exact submitted commit:

```bash
lake update
lake build
```

must succeed under the committed `lean-toolchain` and pinned Mathlib release/manifest.

Before Palomar submission:

- remove every proof `sorry` outside the deliberate Challenge statement surface;
- run the exact Comparator configuration;
- check the permitted-axiom report;
- replay using Palomar's required independent kernel path.

A green Lean build alone is not enough: the advertised Challenge statement must be mechanically compared with the proved Solution statement.

## 2. Independent reconstruction

Run:

```bash
python3 verification/check_fischer_h.py
```

This checker deliberately does not import Lean or a graph package. It:

- reconstructs H from Fischer's G(K3) construction;
- independently decodes the source graph6 string;
- requires the two edge sets to match exactly;
- checks 24 vertices, 30 edges, connectivity and the degree multiset;
- checks the explicit independent 9-set and computes the exact independence number;
- checks the explicit 11-set and records a forcing sequence;
- enumerates branch forts and reproduces t=12, h=3, m3=12 and m4=25;
- constructs exactly the source's 17,712 lower-bound candidates and confirms none forces.

This layer is intended to catch transcription errors, label mismatches, witness mistakes, and incomplete finite-search assumptions independently of the Lean encoding.

## Audit rule

The independent Python result does not count as the formal proof. Conversely, the Lean encoding is not treated as independent evidence that the source graph was transcribed correctly.

A release candidate is acceptable only when both layers agree on the exact source graph and central finite facts.
