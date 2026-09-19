# Fischer Zero-Forcing Counterexample

**Status: BOOTSTRAP / NOT YET FORMALLY VERIFIED**

This repository is a tightly scoped Lean 4 formalization project for Mikko Fischer's explicit 24-vertex counterexample to the zero-forcing-versus-independence conjecture for connected subcubic graphs.

The target graph H is the graph denoted G(K3) in Fischer's 2026 note. The source reports:

- |V(H)| = 24
- alpha(H) = 9
- Z(H) = 11
- Delta(H) = 3

Hence Z(H) > alpha(H) + 1.

The underlying mathematical counterexample is Fischer's result. This repository's intended contribution is a faithful, auditable Lean formal verification and Palomar-ready packaging of that result.

## Primary source

Mikko Fischer, **"A counterexample to the zero forcing versus independence conjecture for cubic and subcubic graphs"**, arXiv:2607.23664v1 (2026).

The exact source graph and reconstruction notes are recorded in `docs/SOURCE_AND_PROVENANCE.md` and `reference/`.

## Environment

- Lean: `v4.32.0`
- Mathlib: release `v4.32.0`
- Lake project: repository root

Build from a fresh clone with:

```bash
lake update
lake build
```

The GitHub Actions workflow also runs the independent finite checker before the Lean build.

## Layout

- `FischerZeroForcing/` — project definitions and the explicit graph
- `Challenge.lean` — small Palomar-facing statement surface; currently contains a deliberate placeholder proof
- `Solution.lean` — eventual proof surface; currently contains a deliberate placeholder proof
- `docs/` — scope, provenance, proof architecture, verification, and Palomar plans
- `reference/H24.g6` — the published graph6 string for Fischer's 24-vertex graph
- `verification/check_fischer_h.py` — independent standard-library-only reconstruction and finite checker

## Scope

Version 1 is only the formal verification of Fischer's explicit 24-vertex connected subcubic counterexample, preferably with the stronger internal certificate alpha(H) = 9 and Z(H) = 11.

Minimality, the 36-vertex cubic example, infinite families, a general-purpose zero-forcing library, and unrelated graph-theory research are out of scope.

## Palomar objective

The intended endpoint is a public, pinned, independently replayable Lean proof suitable for Palomar submission. No Palomar submission is being made during bootstrap, and this README must not be read as claiming the target theorem is already formally proved.
