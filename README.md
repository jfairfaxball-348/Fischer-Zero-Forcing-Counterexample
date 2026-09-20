# Fischer Zero-Forcing Counterexample

**Status: formal proof complete; Palomar packaging and mechanical preflight enabled.**

This repository is a tightly scoped Lean 4 formalization of Mikko Fischer's
explicit 24-vertex counterexample to the zero-forcing-versus-independence
conjecture for connected subcubic graphs.

The mathematical counterexample is Fischer's result. This repository's
contribution is a faithful, auditable Lean verification, an independent
reconstruction of the finite certificates, and Palomar-facing packaging. It
does **not** claim discovery of the counterexample.

## Main theorem

The proved public theorem is:

```lean
theorem FischerZeroForcing.main_result :
  ∃ G : SimpleGraph (Fin 24),
    G.Connected ∧
    (∀ v : Fin 24, (G.neighborSet v).ncard ≤ 3) ∧
    G.indepNum = 9 ∧
    zeroForcingNumber G = 11
```

The witness is Fischer's graph (H = G(K_3)).

## Primary source

Mikko Fischer, **"A counterexample to the zero forcing versus independence
conjecture for cubic and subcubic graphs"**, arXiv:2607.23664v1 (2026).

The exact source graph, graph6 string, edge list, witness sets, fort counts, and
17,712-candidate reduction are recorded in
`docs/SOURCE_AND_PROVENANCE.md` and `reference/`.

## Trust boundary

`Solution.lean` proves the advertised theorem from the project development.
`Challenge.lean` is the deliberately small Palomar statement surface and
therefore contains the expected placeholder `sorry` for the advertised
theorem. Comparator compiles the Challenge separately and checks the proved
Solution declaration against it.

The hostile theorem-level audit of
`FischerZeroForcing.main_result` reports only the standard axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

No `native.native_decide.ax*`, `sorryAx`, custom project axiom,
`Lean.ofReduceBool`, or unchecked proof bridge is transitive to the final
theorem.

## Environment

- Lean: `v4.32.0`
- Mathlib: release `v4.32.0`
- Lake project: repository root
- committed `lake-manifest.json`

## Reproduce the checks

From a fresh checkout of the exact commit:

```bash
python3 verification/check_fischer_h.py
lake build
lake env lean Audit.lean
```

The Python checker is standard-library-only and independently reconstructs the
published graph, checks its edge list and graph6 certificate, computes
`alpha(H) = 9`, verifies an 11-vertex forcing set, reconstructs the branch
fort data, generates exactly 17,712 lower-bound candidates, and confirms that
none zero-force.

The `Palomar Preflight` GitHub Actions workflow invokes Palomar's pinned
official full mechanical preflight against `comparator.json`. That path
validates metadata/licensing and runs Comparator with Palomar's protected
independent NanoDa replay. It is a preflight only; it does not register or
submit the result.

## Repository layout

- `FischerZeroForcing/` — definitions, Fischer's graph, and the proved finite certificates
- `Challenge.lean` — human-auditable Palomar statement surface
- `Solution.lean` — proved Palomar solution surface
- `Audit.lean` — explicit `#print axioms` audit targets
- `comparator.json` — Comparator declaration and permitted-axiom configuration
- `formalization.yaml` — Palomar/formalization.yaml v0.4 metadata
- `verification/check_fischer_h.py` — independent finite reconstruction checker
- `docs/` — scope, provenance, verification, and packaging notes
- `reference/H24.g6` — published graph6 certificate

## Scope

Version 1 proves only Fischer's explicit 24-vertex connected subcubic example
with exact invariants `alpha(H) = 9` and `Z(H) = 11`.

Minimality, the 36-vertex cubic example, infinite families, a general-purpose
zero-forcing library, and unrelated graph-theory research are out of scope.
