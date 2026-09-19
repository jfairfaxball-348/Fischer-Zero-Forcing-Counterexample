# Palomar plan

No submission is made during bootstrap.

Current Palomar requirements were checked on 2026-09-19. Before submitting, re-read the live policy because it can change.

## Final repository surface

Prepare a public immutable commit containing at minimum:

- exactly one Lake project file at the selected project root;
- `lean-toolchain` pinned to a supported Lean release;
- a committed `lake-manifest.json` with Git dependencies resolved to full commit SHAs;
- a short, readable `Challenge.lean`;
- matching proved `Solution.lean`;
- `comparator.json` naming every compared theorem and any required definitions;
- `formalization.yaml` using the current schema (v0.4 at bootstrap time);
- exactly one accepted root licence file;
- source/provenance and human-readable mathematical account.

Palomar records a full 40-character source commit SHA, not a moving branch.

## Challenge discipline

The final Challenge should state the mathematically ordinary result and keep implementation machinery out of the statement surface.

Preferred strong statement:

> There exists a connected simple graph on 24 vertices, of maximum degree at most 3, with independence number 9 and zero-forcing number 11.

This directly implies the weaker existential counterexample statement.

If the explicit Fischer-graph statement produces a materially smaller or safer Comparator surface, document and choose that alternative before submission.

## Mechanical constraints

At bootstrap time Palomar requires Comparator to reject proofs depending on `sorryAx`, `Lean.ofReduceBool`, custom axioms, or unnamed missing definitions. The permitted standard axioms are controlled by Comparator policy. Palomar independently replays exported proofs with NanoDa as well as Lean's kernel.

The Challenge hard limits are 1,000 lines and 100 KiB; Palomar's preferred review surface is at most roughly 300 lines and 32 KiB.

Do not assume a normal `lake build` is equivalent to Palomar mechanical verification.

## Metadata and provenance

The final `formalization.yaml` must honestly record:

- this is source-based work formalising Fischer's result;
- Fischer as bibliographic source author;
- the repository formalizer/maintainer;
- AI assistance used in this project;
- the exact scope and any fidelity gaps;
- classification (math.CO; appropriate MSC codes, including the source's 05C69 and 05C50 if still appropriate);
- review status;
- related formalisations, if any;
- source-author endorsement/contact status if the current schema asks for it.

Do not claim novelty for Fischer's counterexample.

## Research-interest check

The Palomar policy asks for credible research interest and an identifiable mathematical audience. The intended case is factual rather than promotional: this is a formal verification of a recent explicit counterexample to a named graph-theory conjecture, and the source itself discusses a prior Lean 4 formulation of the conjecture.

Before submission, recheck that the exact theorem has not already been registered or publicly formalised. A duplicate or lightly repackaged formalisation can fail Palomar's editorial floor even if it builds.

## Final checklist

1. theorem statement audited against Fischer;
2. zero-forcing definition audited;
3. graph6/edge-list reconstruction agrees;
4. all source witnesses/case counts agree;
5. Solution has no prohibited proof mechanism;
6. fresh `lake build` succeeds;
7. Comparator succeeds;
8. independent Python reconstruction succeeds;
9. NanoDa/Palomar mechanical path succeeds;
10. metadata, licence and provenance validate;
11. exact result not already registered;
12. only then submit the immutable commit.
