# Palomar plan

No submission is made by this repository workflow. The final action remains a
separate human submission of one immutable 40-character commit.

Current Palomar requirements were rechecked on 2026-09-20 against the live
Palomar policy/submission tooling. The controlling metadata format is
`formalization.yaml` v0.4. The current PalomarSubmission toolchain floor is
Lean v4.28.0, so this project's pinned Lean v4.32.0 is within the supported
range.

## Current mechanical contract

The selected project contains:

- exactly one Lake project file at the project root;
- `lean-toolchain` pinned to Lean v4.32.0;
- committed `lake-manifest.json`;
- a short Mathlib-only `Challenge.lean`;
- matching proved `Solution.lean`;
- `comparator.json`;
- `formalization.yaml` v0.4;
- exactly one mechanically detectable root licence, `LICENSE`.

The Challenge's deliberate `sorry` is expected. Proof-status counts exclude
that statement placeholder. The proved Solution may not depend on `sorryAx`,
`Lean.ofReduceBool`, custom axioms, or unnamed missing definitions.

Palomar independently forces every exported proof through both Lean's kernel
and its pinned NanoDa kernel. The submitted `enable_nanoda` setting is not
authoritative; independent replay is enforced by Palomar.

## Comparator surface

The single advertised declaration is:

`FischerZeroForcing.main_result`

The Challenge repeats the project-local definitions `CanForce`, `ForceStep`,
`IsZeroForcingSet`, and `zeroForcingNumber` with the same definitions as the
proof development. They are concrete statement dependencies, not Comparator
definition holes, so `definition_names` is empty.

## Full preflight

`.github/workflows/palomar-preflight.yml` invokes the official
`PalomarRegistry/PalomarSubmission` reusable full-preflight workflow pinned to
commit `3561d237dcc4b28482558ad28a64d767d7cc8615`.

That preflight is the preferred final mechanical check because it exercises the
current Palomar validation, Comparator sandbox, and protected NanoDa replay
without registering the result.

## Metadata and provenance

The metadata records this as source-based work formalizing Fischer's result,
credits Mikko Fischer as the mathematical source author, identifies the
repository maintainer/formalizer, discloses AI assistance, states the exact
scope, and makes no novelty claim for Fischer's counterexample.

## Final readiness checklist

1. theorem statement unchanged and audited against Fischer;
2. independent Python reconstruction passes;
3. full `lake build` passes;
4. `Audit.lean` reports only `propext`, `Classical.choice`, and `Quot.sound`
   for the final theorem;
5. official Palomar full preflight passes;
6. exact result is not already registered or duplicated by a substantially
   identical public formalization;
7. the exact immutable commit used for submission is the commit that passed
   all checks;
8. only then open the Palomar submission form.
