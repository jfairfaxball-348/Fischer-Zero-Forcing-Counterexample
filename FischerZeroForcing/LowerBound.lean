import FischerZeroForcing.Certificates
import FischerZeroForcing.LowerBoundCandidates
import FischerZeroForcing.ZeroForcingClosure

/-!
# Fischer zero-forcing lower bound

The source fort reduction has already reduced every hypothetical zero-forcing
set of cardinality at most ten to the explicit list `lowerBoundCandidates`.

The verified deterministic closure remains part of the formal development and
is built by CI.  For the 17,712-candidate obstruction itself, however, directly
recomputing all closures is unnecessarily expensive.  The independent closure
computation collapses to a small family of terminal white sets.  This file
records those 112 sets as an explicit certificate and kernel-checks only the
facts needed for the lower bound:

* every listed obstruction is a nonempty fort;
* every one of the 17,712 candidates is disjoint from at least one listed fort.

By `IsZeroForcingSet.intersects_fort`, such a candidate cannot be zero forcing.
The proof does not trust the external provenance of the terminal sets: Lean
checks fort validity and exhaustive candidate coverage itself.
-/

namespace FischerZeroForcing

/--
The 112 distinct terminal-white obstruction sets found by the independent
closure computation, ordered by cardinality and then lexicographically.

Their role in the formal proof is only as explicit nonempty forts covering all
17,712 lower-bound candidates.
-/
def lowerBoundTerminalForts : List (Finset Vertex) := [
  ([0, 1, 4, 5, 11, 12] : List Vertex).toFinset,
  ([0, 1, 4, 5, 11, 13] : List Vertex).toFinset,
  ([0, 1, 4, 5, 14, 15] : List Vertex).toFinset,
  ([0, 1, 4, 5, 14, 16] : List Vertex).toFinset,
  ([0, 1, 4, 6, 11, 12] : List Vertex).toFinset,
  ([0, 1, 4, 6, 11, 13] : List Vertex).toFinset,
  ([0, 1, 4, 6, 14, 15] : List Vertex).toFinset,
  ([0, 1, 4, 6, 14, 16] : List Vertex).toFinset,
  ([0, 1, 7, 8, 11, 12] : List Vertex).toFinset,
  ([0, 1, 7, 8, 11, 13] : List Vertex).toFinset,
  ([0, 1, 7, 8, 14, 15] : List Vertex).toFinset,
  ([0, 1, 7, 8, 14, 16] : List Vertex).toFinset,
  ([0, 1, 7, 9, 11, 12] : List Vertex).toFinset,
  ([0, 1, 7, 9, 11, 13] : List Vertex).toFinset,
  ([0, 1, 7, 9, 14, 15] : List Vertex).toFinset,
  ([0, 1, 7, 9, 14, 16] : List Vertex).toFinset,
  ([0, 2, 4, 5, 18, 19] : List Vertex).toFinset,
  ([0, 2, 4, 5, 18, 20] : List Vertex).toFinset,
  ([0, 2, 4, 5, 21, 22] : List Vertex).toFinset,
  ([0, 2, 4, 5, 21, 23] : List Vertex).toFinset,
  ([0, 2, 4, 6, 18, 19] : List Vertex).toFinset,
  ([0, 2, 4, 6, 18, 20] : List Vertex).toFinset,
  ([0, 2, 4, 6, 21, 22] : List Vertex).toFinset,
  ([0, 2, 4, 6, 21, 23] : List Vertex).toFinset,
  ([0, 2, 7, 8, 18, 19] : List Vertex).toFinset,
  ([0, 2, 7, 8, 18, 20] : List Vertex).toFinset,
  ([0, 2, 7, 8, 21, 22] : List Vertex).toFinset,
  ([0, 2, 7, 8, 21, 23] : List Vertex).toFinset,
  ([0, 2, 7, 9, 18, 19] : List Vertex).toFinset,
  ([0, 2, 7, 9, 18, 20] : List Vertex).toFinset,
  ([0, 2, 7, 9, 21, 22] : List Vertex).toFinset,
  ([0, 2, 7, 9, 21, 23] : List Vertex).toFinset,
  ([1, 2, 11, 12, 18, 19] : List Vertex).toFinset,
  ([1, 2, 11, 12, 18, 20] : List Vertex).toFinset,
  ([1, 2, 11, 12, 21, 22] : List Vertex).toFinset,
  ([1, 2, 11, 12, 21, 23] : List Vertex).toFinset,
  ([1, 2, 11, 13, 18, 19] : List Vertex).toFinset,
  ([1, 2, 11, 13, 18, 20] : List Vertex).toFinset,
  ([1, 2, 11, 13, 21, 22] : List Vertex).toFinset,
  ([1, 2, 11, 13, 21, 23] : List Vertex).toFinset,
  ([1, 2, 14, 15, 18, 19] : List Vertex).toFinset,
  ([1, 2, 14, 15, 18, 20] : List Vertex).toFinset,
  ([1, 2, 14, 15, 21, 22] : List Vertex).toFinset,
  ([1, 2, 14, 15, 21, 23] : List Vertex).toFinset,
  ([1, 2, 14, 16, 18, 19] : List Vertex).toFinset,
  ([1, 2, 14, 16, 18, 20] : List Vertex).toFinset,
  ([1, 2, 14, 16, 21, 22] : List Vertex).toFinset,
  ([1, 2, 14, 16, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 21, 23] : List Vertex).toFinset
]

theorem lowerBoundTerminalForts_length :
    lowerBoundTerminalForts.length = 112 := by
  decide

/-- List-local proposition that every supplied obstruction is a nonempty fort. -/
def AllTerminalFortsValid : List (Finset Vertex) → Prop
  | [] => True
  | F :: rest =>
      (F.Nonempty ∧ IsFort fischerGraph F) ∧
      AllTerminalFortsValid rest

private instance lowerBoundFortDecidable (F : Finset Vertex) :
    Decidable (IsFort fischerGraph F) := by
  unfold IsFort
  infer_instance

private instance allTerminalFortsValidDecidable :
    ∀ forts : List (Finset Vertex), Decidable (AllTerminalFortsValid forts)
  | [] => isTrue trivial
  | F :: rest => by
      letI : Decidable (IsFort fischerGraph F) := lowerBoundFortDecidable F
      letI : Decidable (AllTerminalFortsValid rest) :=
        allTerminalFortsValidDecidable rest
      change Decidable
        ((F.Nonempty ∧ IsFort fischerGraph F) ∧ AllTerminalFortsValid rest)
      infer_instance

/--
Small kernel-checkable chunks of the 112 terminal forts.  The canonical
`lowerBoundTerminalForts` list above remains unchanged; these chunks merely
partition it into bounded proof obligations.
-/
private def lowerBoundTerminalFortsChunk00 : List (Finset Vertex) := [
  ([0, 1, 4, 5, 11, 12] : List Vertex).toFinset,
  ([0, 1, 4, 5, 11, 13] : List Vertex).toFinset,
  ([0, 1, 4, 5, 14, 15] : List Vertex).toFinset,
  ([0, 1, 4, 5, 14, 16] : List Vertex).toFinset,
  ([0, 1, 4, 6, 11, 12] : List Vertex).toFinset,
  ([0, 1, 4, 6, 11, 13] : List Vertex).toFinset,
  ([0, 1, 4, 6, 14, 15] : List Vertex).toFinset,
  ([0, 1, 4, 6, 14, 16] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk00_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk00 := by
  decide

private def lowerBoundTerminalFortsChunk01 : List (Finset Vertex) := [
  ([0, 1, 7, 8, 11, 12] : List Vertex).toFinset,
  ([0, 1, 7, 8, 11, 13] : List Vertex).toFinset,
  ([0, 1, 7, 8, 14, 15] : List Vertex).toFinset,
  ([0, 1, 7, 8, 14, 16] : List Vertex).toFinset,
  ([0, 1, 7, 9, 11, 12] : List Vertex).toFinset,
  ([0, 1, 7, 9, 11, 13] : List Vertex).toFinset,
  ([0, 1, 7, 9, 14, 15] : List Vertex).toFinset,
  ([0, 1, 7, 9, 14, 16] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk01_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk01 := by
  decide

private def lowerBoundTerminalFortsChunk02 : List (Finset Vertex) := [
  ([0, 2, 4, 5, 18, 19] : List Vertex).toFinset,
  ([0, 2, 4, 5, 18, 20] : List Vertex).toFinset,
  ([0, 2, 4, 5, 21, 22] : List Vertex).toFinset,
  ([0, 2, 4, 5, 21, 23] : List Vertex).toFinset,
  ([0, 2, 4, 6, 18, 19] : List Vertex).toFinset,
  ([0, 2, 4, 6, 18, 20] : List Vertex).toFinset,
  ([0, 2, 4, 6, 21, 22] : List Vertex).toFinset,
  ([0, 2, 4, 6, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk02_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk02 := by
  decide

private def lowerBoundTerminalFortsChunk03 : List (Finset Vertex) := [
  ([0, 2, 7, 8, 18, 19] : List Vertex).toFinset,
  ([0, 2, 7, 8, 18, 20] : List Vertex).toFinset,
  ([0, 2, 7, 8, 21, 22] : List Vertex).toFinset,
  ([0, 2, 7, 8, 21, 23] : List Vertex).toFinset,
  ([0, 2, 7, 9, 18, 19] : List Vertex).toFinset,
  ([0, 2, 7, 9, 18, 20] : List Vertex).toFinset,
  ([0, 2, 7, 9, 21, 22] : List Vertex).toFinset,
  ([0, 2, 7, 9, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk03_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk03 := by
  decide

private def lowerBoundTerminalFortsChunk04 : List (Finset Vertex) := [
  ([1, 2, 11, 12, 18, 19] : List Vertex).toFinset,
  ([1, 2, 11, 12, 18, 20] : List Vertex).toFinset,
  ([1, 2, 11, 12, 21, 22] : List Vertex).toFinset,
  ([1, 2, 11, 12, 21, 23] : List Vertex).toFinset,
  ([1, 2, 11, 13, 18, 19] : List Vertex).toFinset,
  ([1, 2, 11, 13, 18, 20] : List Vertex).toFinset,
  ([1, 2, 11, 13, 21, 22] : List Vertex).toFinset,
  ([1, 2, 11, 13, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk04_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk04 := by
  decide

private def lowerBoundTerminalFortsChunk05 : List (Finset Vertex) := [
  ([1, 2, 14, 15, 18, 19] : List Vertex).toFinset,
  ([1, 2, 14, 15, 18, 20] : List Vertex).toFinset,
  ([1, 2, 14, 15, 21, 22] : List Vertex).toFinset,
  ([1, 2, 14, 15, 21, 23] : List Vertex).toFinset,
  ([1, 2, 14, 16, 18, 19] : List Vertex).toFinset,
  ([1, 2, 14, 16, 18, 20] : List Vertex).toFinset,
  ([1, 2, 14, 16, 21, 22] : List Vertex).toFinset,
  ([1, 2, 14, 16, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk05_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk05 := by
  decide

private def lowerBoundTerminalFortsChunk06 : List (Finset Vertex) := [
  ([0, 1, 2, 4, 5, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 11, 13, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk06_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk06 := by
  decide

private def lowerBoundTerminalFortsChunk07 : List (Finset Vertex) := [
  ([0, 1, 2, 4, 5, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 5, 14, 16, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk07_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk07 := by
  decide

private def lowerBoundTerminalFortsChunk08 : List (Finset Vertex) := [
  ([0, 1, 2, 4, 6, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 11, 13, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk08_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk08 := by
  decide

private def lowerBoundTerminalFortsChunk09 : List (Finset Vertex) := [
  ([0, 1, 2, 4, 6, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 4, 6, 14, 16, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk09_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk09 := by
  decide

private def lowerBoundTerminalFortsChunk10 : List (Finset Vertex) := [
  ([0, 1, 2, 7, 8, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 11, 13, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk10_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk10 := by
  decide

private def lowerBoundTerminalFortsChunk11 : List (Finset Vertex) := [
  ([0, 1, 2, 7, 8, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 8, 14, 16, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk11_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk11 := by
  decide

private def lowerBoundTerminalFortsChunk12 : List (Finset Vertex) := [
  ([0, 1, 2, 7, 9, 11, 12, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 12, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 11, 13, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk12_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk12 := by
  decide

private def lowerBoundTerminalFortsChunk13 : List (Finset Vertex) := [
  ([0, 1, 2, 7, 9, 14, 15, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 15, 21, 23] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 18, 19] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 18, 20] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 21, 22] : List Vertex).toFinset,
  ([0, 1, 2, 7, 9, 14, 16, 21, 23] : List Vertex).toFinset
]

private theorem lowerBoundTerminalFortsChunk13_valid :
    AllTerminalFortsValid lowerBoundTerminalFortsChunk13 := by
  decide

private theorem AllTerminalFortsValid.append
    {xs ys : List (Finset Vertex)}
    (hx : AllTerminalFortsValid xs)
    (hy : AllTerminalFortsValid ys) :
    AllTerminalFortsValid (xs ++ ys) := by
  induction xs with
  | nil =>
      simpa [AllTerminalFortsValid] using hy
  | cons F rest ih =>
      simp only [AllTerminalFortsValid] at hx ⊢
      exact ⟨hx.1, ih hx.2 hy⟩

/--
Every one of the 112 explicit obstruction sets is a nonempty fort.

Lean checks fourteen independent eight-fort chunks with ordinary `decide`,
then combines those kernel-checked propositions structurally.
-/
theorem lowerBoundTerminalForts_valid :
    AllTerminalFortsValid lowerBoundTerminalForts := by
  change AllTerminalFortsValid (
      lowerBoundTerminalFortsChunk00 ++
      lowerBoundTerminalFortsChunk01 ++
      lowerBoundTerminalFortsChunk02 ++
      lowerBoundTerminalFortsChunk03 ++
      lowerBoundTerminalFortsChunk04 ++
      lowerBoundTerminalFortsChunk05 ++
      lowerBoundTerminalFortsChunk06 ++
      lowerBoundTerminalFortsChunk07 ++
      lowerBoundTerminalFortsChunk08 ++
      lowerBoundTerminalFortsChunk09 ++
      lowerBoundTerminalFortsChunk10 ++
      lowerBoundTerminalFortsChunk11 ++
      lowerBoundTerminalFortsChunk12 ++
      lowerBoundTerminalFortsChunk13)
  exact AllTerminalFortsValid.append lowerBoundTerminalFortsChunk00_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk01_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk02_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk03_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk04_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk05_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk06_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk07_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk08_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk09_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk10_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk11_valid (
      AllTerminalFortsValid.append lowerBoundTerminalFortsChunk12_valid (
      lowerBoundTerminalFortsChunk13_valid)))))))))))))

/-- Extract one fort's validity from the list-local validity certificate. -/
theorem AllTerminalFortsValid.of_mem
    {forts : List (Finset Vertex)}
    (hvalid : AllTerminalFortsValid forts)
    {F : Finset Vertex}
    (hmem : F ∈ forts) :
    F.Nonempty ∧ IsFort fischerGraph F := by
  induction forts with
  | nil =>
      simp at hmem
  | cons A rest ih =>
      simp only [AllTerminalFortsValid] at hvalid
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · subst F
        exact hvalid.1
      · exact ih hvalid.2 hmem

/--
Search a supplied finite fort list for one disjoint from `S`.

This Boolean is intentionally cheap: it checks only finite-set disjointness and
does not rerun the deterministic forcing closure.
-/
def HasDisjointTerminalFortBool (S : Finset Vertex) :
    List (Finset Vertex) → Bool
  | [] => false
  | F :: rest =>
      if decide (Disjoint S F) then true
      else HasDisjointTerminalFortBool S rest

/-- A true Boolean search result contains an actual disjoint listed fort. -/
theorem HasDisjointTerminalFortBool.of_true
    {S : Finset Vertex} {forts : List (Finset Vertex)}
    (h : HasDisjointTerminalFortBool S forts = true) :
    ∃ F ∈ forts, Disjoint S F := by
  induction forts with
  | nil =>
      simp [HasDisjointTerminalFortBool] at h
  | cons F rest ih =>
      by_cases hdisj : Disjoint S F
      · exact ⟨F, by simp, hdisj⟩
      · have hrest :
            HasDisjointTerminalFortBool S rest = true := by
          simpa [HasDisjointTerminalFortBool, hdisj] using h
        rcases ih hrest with ⟨T, hT, hTdisj⟩
        exact ⟨T, by simp [hT], hTdisj⟩

/-- Boolean coverage certificate over a finite candidate list. -/
def AllCandidatesCoveredBool : List (Finset Vertex) → Bool
  | [] => true
  | S :: rest =>
      HasDisjointTerminalFortBool S lowerBoundTerminalForts &&
      AllCandidatesCoveredBool rest

/-- Extract a covering disjoint fort for any member of a covered candidate list. -/
theorem AllCandidatesCoveredBool.of_mem
    {candidates : List (Finset Vertex)}
    (hcovered : AllCandidatesCoveredBool candidates = true)
    {S : Finset Vertex}
    (hmem : S ∈ candidates) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  induction candidates with
  | nil =>
      simp at hmem
  | cons A rest ih =>
      simp only [AllCandidatesCoveredBool] at hcovered
      have hparts :
          HasDisjointTerminalFortBool A lowerBoundTerminalForts = true ∧
            AllCandidatesCoveredBool rest = true :=
        Bool.and_eq_true_iff.mp hcovered
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · subst S
        exact HasDisjointTerminalFortBool.of_true hparts.1
      · exact ih hparts.2 hmem

/--
If a supplied fort is known to occur in the search list and is disjoint from
`S`, then the Boolean search succeeds.  This lets the final certificate use
explicit untrusted witness indices instead of asking the kernel to repeat the
full 112-fort search for every candidate.
-/
theorem HasDisjointTerminalFortBool.eq_true_of_exists
    {S : Finset Vertex} {forts : List (Finset Vertex)}
    (h : ∃ F ∈ forts, Disjoint S F) :
    HasDisjointTerminalFortBool S forts = true := by
  induction forts with
  | nil =>
      simp at h
  | cons A rest ih =>
      rcases h with ⟨F, hmem, hdisj⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [HasDisjointTerminalFortBool, hdisj]
      · by_cases hA : Disjoint S A
        · simp [HasDisjointTerminalFortBool, hA]
        · have hrest :
              HasDisjointTerminalFortBool S rest = true :=
            ih ⟨F, hmem, hdisj⟩
          simpa [HasDisjointTerminalFortBool, hA] using hrest

/-- Turn semantic coverage of every candidate into the existing Boolean API. -/
theorem AllCandidatesCoveredBool.eq_true_of_forall
    {candidates : List (Finset Vertex)}
    (h : ∀ S ∈ candidates,
      ∃ F ∈ lowerBoundTerminalForts, Disjoint S F) :
    AllCandidatesCoveredBool candidates = true := by
  induction candidates with
  | nil =>
      rfl
  | cons A rest ih =>
      have hA :
          HasDisjointTerminalFortBool A lowerBoundTerminalForts = true :=
        HasDisjointTerminalFortBool.eq_true_of_exists
          (h A (by simp))
      have hrest :
          ∀ S ∈ rest,
            ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
        intro S hS
        exact h S (by simp [hS])
      have htail : AllCandidatesCoveredBool rest = true :=
        ih hrest
      simp [AllCandidatesCoveredBool, hA, htail]

/-- Linear reference selector used only to justify list membership. -/
def terminalFortAt : Nat → List (Finset Vertex) → Option (Finset Vertex)
  | _, [] => none
  | 0, F :: _ => some F
  | Nat.succ i, _ :: rest => terminalFortAt i rest

/-- A successful reference lookup is a genuine member of the supplied list. -/
theorem terminalFortAt_mem
    {i : Nat} {forts : List (Finset Vertex)} {F : Finset Vertex}
    (h : terminalFortAt i forts = some F) :
    F ∈ forts := by
  induction forts generalizing i with
  | nil =>
      simp [terminalFortAt] at h
  | cons A rest ih =>
      cases i with
      | zero =>
          simp [terminalFortAt] at h
          subst F
          simp
      | succ i =>
          simp only [terminalFortAt] at h
          have hmem : F ∈ rest := ih h
          simp [hmem]

/--
A selected fort together with a proof that the slow reference selector returns
that same fort at the supplied index.  The proof is structural (`rfl` after
substituting the literal index), so the fast selector does not need to decide
membership in a 112-element list at every leaf.
-/
def TerminalFortSelection (i : Nat) :=
  {F : Finset Vertex //
    terminalFortAt i lowerBoundTerminalForts = some F}

/--
Balanced selector used by the 17,712-candidate certificate.

Only the computational lookup is balanced.  The attached equality proof links
each leaf back to `terminalFortAt`, after which `terminalFortAt_mem` supplies
the ordinary list-membership fact needed by the existing proof architecture.
-/
def terminalFortCertificate (i : Nat) : Option (TerminalFortSelection i) :=
  if i < 56 then
    if i < 28 then
      if i < 14 then
        if i < 7 then
          if i < 3 then
            if i < 1 then
              if h : i = 0 then
                some ⟨([0, 1, 4, 5, 11, 12] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 2 then
                if h : i = 1 then
                  some ⟨([0, 1, 4, 5, 11, 13] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 2 then
                  some ⟨([0, 1, 4, 5, 14, 15] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 5 then
              if i < 4 then
                if h : i = 3 then
                  some ⟨([0, 1, 4, 5, 14, 16] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 4 then
                  some ⟨([0, 1, 4, 6, 11, 12] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 6 then
                if h : i = 5 then
                  some ⟨([0, 1, 4, 6, 11, 13] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 6 then
                  some ⟨([0, 1, 4, 6, 14, 15] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 10 then
            if i < 8 then
              if h : i = 7 then
                some ⟨([0, 1, 4, 6, 14, 16] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 9 then
                if h : i = 8 then
                  some ⟨([0, 1, 7, 8, 11, 12] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 9 then
                  some ⟨([0, 1, 7, 8, 11, 13] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 12 then
              if i < 11 then
                if h : i = 10 then
                  some ⟨([0, 1, 7, 8, 14, 15] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 11 then
                  some ⟨([0, 1, 7, 8, 14, 16] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 13 then
                if h : i = 12 then
                  some ⟨([0, 1, 7, 9, 11, 12] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 13 then
                  some ⟨([0, 1, 7, 9, 11, 13] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
      else
        if i < 21 then
          if i < 17 then
            if i < 15 then
              if h : i = 14 then
                some ⟨([0, 1, 7, 9, 14, 15] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 16 then
                if h : i = 15 then
                  some ⟨([0, 1, 7, 9, 14, 16] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 16 then
                  some ⟨([0, 2, 4, 5, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 19 then
              if i < 18 then
                if h : i = 17 then
                  some ⟨([0, 2, 4, 5, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 18 then
                  some ⟨([0, 2, 4, 5, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 20 then
                if h : i = 19 then
                  some ⟨([0, 2, 4, 5, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 20 then
                  some ⟨([0, 2, 4, 6, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 24 then
            if i < 22 then
              if h : i = 21 then
                some ⟨([0, 2, 4, 6, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 23 then
                if h : i = 22 then
                  some ⟨([0, 2, 4, 6, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 23 then
                  some ⟨([0, 2, 4, 6, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 26 then
              if i < 25 then
                if h : i = 24 then
                  some ⟨([0, 2, 7, 8, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 25 then
                  some ⟨([0, 2, 7, 8, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 27 then
                if h : i = 26 then
                  some ⟨([0, 2, 7, 8, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 27 then
                  some ⟨([0, 2, 7, 8, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
    else
      if i < 42 then
        if i < 35 then
          if i < 31 then
            if i < 29 then
              if h : i = 28 then
                some ⟨([0, 2, 7, 9, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 30 then
                if h : i = 29 then
                  some ⟨([0, 2, 7, 9, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 30 then
                  some ⟨([0, 2, 7, 9, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 33 then
              if i < 32 then
                if h : i = 31 then
                  some ⟨([0, 2, 7, 9, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 32 then
                  some ⟨([1, 2, 11, 12, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 34 then
                if h : i = 33 then
                  some ⟨([1, 2, 11, 12, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 34 then
                  some ⟨([1, 2, 11, 12, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 38 then
            if i < 36 then
              if h : i = 35 then
                some ⟨([1, 2, 11, 12, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 37 then
                if h : i = 36 then
                  some ⟨([1, 2, 11, 13, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 37 then
                  some ⟨([1, 2, 11, 13, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 40 then
              if i < 39 then
                if h : i = 38 then
                  some ⟨([1, 2, 11, 13, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 39 then
                  some ⟨([1, 2, 11, 13, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 41 then
                if h : i = 40 then
                  some ⟨([1, 2, 14, 15, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 41 then
                  some ⟨([1, 2, 14, 15, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
      else
        if i < 49 then
          if i < 45 then
            if i < 43 then
              if h : i = 42 then
                some ⟨([1, 2, 14, 15, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 44 then
                if h : i = 43 then
                  some ⟨([1, 2, 14, 15, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 44 then
                  some ⟨([1, 2, 14, 16, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 47 then
              if i < 46 then
                if h : i = 45 then
                  some ⟨([1, 2, 14, 16, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 46 then
                  some ⟨([1, 2, 14, 16, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 48 then
                if h : i = 47 then
                  some ⟨([1, 2, 14, 16, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 48 then
                  some ⟨([0, 1, 2, 4, 5, 11, 12, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 52 then
            if i < 50 then
              if h : i = 49 then
                some ⟨([0, 1, 2, 4, 5, 11, 12, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 51 then
                if h : i = 50 then
                  some ⟨([0, 1, 2, 4, 5, 11, 12, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 51 then
                  some ⟨([0, 1, 2, 4, 5, 11, 12, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 54 then
              if i < 53 then
                if h : i = 52 then
                  some ⟨([0, 1, 2, 4, 5, 11, 13, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 53 then
                  some ⟨([0, 1, 2, 4, 5, 11, 13, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 55 then
                if h : i = 54 then
                  some ⟨([0, 1, 2, 4, 5, 11, 13, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 55 then
                  some ⟨([0, 1, 2, 4, 5, 11, 13, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
  else
    if i < 84 then
      if i < 70 then
        if i < 63 then
          if i < 59 then
            if i < 57 then
              if h : i = 56 then
                some ⟨([0, 1, 2, 4, 5, 14, 15, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 58 then
                if h : i = 57 then
                  some ⟨([0, 1, 2, 4, 5, 14, 15, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 58 then
                  some ⟨([0, 1, 2, 4, 5, 14, 15, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 61 then
              if i < 60 then
                if h : i = 59 then
                  some ⟨([0, 1, 2, 4, 5, 14, 15, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 60 then
                  some ⟨([0, 1, 2, 4, 5, 14, 16, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 62 then
                if h : i = 61 then
                  some ⟨([0, 1, 2, 4, 5, 14, 16, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 62 then
                  some ⟨([0, 1, 2, 4, 5, 14, 16, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 66 then
            if i < 64 then
              if h : i = 63 then
                some ⟨([0, 1, 2, 4, 5, 14, 16, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 65 then
                if h : i = 64 then
                  some ⟨([0, 1, 2, 4, 6, 11, 12, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 65 then
                  some ⟨([0, 1, 2, 4, 6, 11, 12, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 68 then
              if i < 67 then
                if h : i = 66 then
                  some ⟨([0, 1, 2, 4, 6, 11, 12, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 67 then
                  some ⟨([0, 1, 2, 4, 6, 11, 12, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 69 then
                if h : i = 68 then
                  some ⟨([0, 1, 2, 4, 6, 11, 13, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 69 then
                  some ⟨([0, 1, 2, 4, 6, 11, 13, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
      else
        if i < 77 then
          if i < 73 then
            if i < 71 then
              if h : i = 70 then
                some ⟨([0, 1, 2, 4, 6, 11, 13, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 72 then
                if h : i = 71 then
                  some ⟨([0, 1, 2, 4, 6, 11, 13, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 72 then
                  some ⟨([0, 1, 2, 4, 6, 14, 15, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 75 then
              if i < 74 then
                if h : i = 73 then
                  some ⟨([0, 1, 2, 4, 6, 14, 15, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 74 then
                  some ⟨([0, 1, 2, 4, 6, 14, 15, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 76 then
                if h : i = 75 then
                  some ⟨([0, 1, 2, 4, 6, 14, 15, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 76 then
                  some ⟨([0, 1, 2, 4, 6, 14, 16, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 80 then
            if i < 78 then
              if h : i = 77 then
                some ⟨([0, 1, 2, 4, 6, 14, 16, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 79 then
                if h : i = 78 then
                  some ⟨([0, 1, 2, 4, 6, 14, 16, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 79 then
                  some ⟨([0, 1, 2, 4, 6, 14, 16, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 82 then
              if i < 81 then
                if h : i = 80 then
                  some ⟨([0, 1, 2, 7, 8, 11, 12, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 81 then
                  some ⟨([0, 1, 2, 7, 8, 11, 12, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 83 then
                if h : i = 82 then
                  some ⟨([0, 1, 2, 7, 8, 11, 12, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 83 then
                  some ⟨([0, 1, 2, 7, 8, 11, 12, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
    else
      if i < 98 then
        if i < 91 then
          if i < 87 then
            if i < 85 then
              if h : i = 84 then
                some ⟨([0, 1, 2, 7, 8, 11, 13, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 86 then
                if h : i = 85 then
                  some ⟨([0, 1, 2, 7, 8, 11, 13, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 86 then
                  some ⟨([0, 1, 2, 7, 8, 11, 13, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 89 then
              if i < 88 then
                if h : i = 87 then
                  some ⟨([0, 1, 2, 7, 8, 11, 13, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 88 then
                  some ⟨([0, 1, 2, 7, 8, 14, 15, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 90 then
                if h : i = 89 then
                  some ⟨([0, 1, 2, 7, 8, 14, 15, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 90 then
                  some ⟨([0, 1, 2, 7, 8, 14, 15, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 94 then
            if i < 92 then
              if h : i = 91 then
                some ⟨([0, 1, 2, 7, 8, 14, 15, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 93 then
                if h : i = 92 then
                  some ⟨([0, 1, 2, 7, 8, 14, 16, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 93 then
                  some ⟨([0, 1, 2, 7, 8, 14, 16, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 96 then
              if i < 95 then
                if h : i = 94 then
                  some ⟨([0, 1, 2, 7, 8, 14, 16, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 95 then
                  some ⟨([0, 1, 2, 7, 8, 14, 16, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 97 then
                if h : i = 96 then
                  some ⟨([0, 1, 2, 7, 9, 11, 12, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 97 then
                  some ⟨([0, 1, 2, 7, 9, 11, 12, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
      else
        if i < 105 then
          if i < 101 then
            if i < 99 then
              if h : i = 98 then
                some ⟨([0, 1, 2, 7, 9, 11, 12, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 100 then
                if h : i = 99 then
                  some ⟨([0, 1, 2, 7, 9, 11, 12, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 100 then
                  some ⟨([0, 1, 2, 7, 9, 11, 13, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 103 then
              if i < 102 then
                if h : i = 101 then
                  some ⟨([0, 1, 2, 7, 9, 11, 13, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 102 then
                  some ⟨([0, 1, 2, 7, 9, 11, 13, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 104 then
                if h : i = 103 then
                  some ⟨([0, 1, 2, 7, 9, 11, 13, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 104 then
                  some ⟨([0, 1, 2, 7, 9, 14, 15, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
        else
          if i < 108 then
            if i < 106 then
              if h : i = 105 then
                some ⟨([0, 1, 2, 7, 9, 14, 15, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
              else
                none
            else
              if i < 107 then
                if h : i = 106 then
                  some ⟨([0, 1, 2, 7, 9, 14, 15, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 107 then
                  some ⟨([0, 1, 2, 7, 9, 14, 15, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
          else
            if i < 110 then
              if i < 109 then
                if h : i = 108 then
                  some ⟨([0, 1, 2, 7, 9, 14, 16, 18, 19] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 109 then
                  some ⟨([0, 1, 2, 7, 9, 14, 16, 18, 20] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
            else
              if i < 111 then
                if h : i = 110 then
                  some ⟨([0, 1, 2, 7, 9, 14, 16, 21, 22] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none
              else
                if h : i = 111 then
                  some ⟨([0, 1, 2, 7, 9, 14, 16, 21, 23] : List Vertex).toFinset, by subst i; rfl⟩
                else
                  none

/--
Bounded structural candidate blocks used by the kernel-only coverage certificate.

These are definitionally the outer `flatMap` blocks of the existing three
candidate classes.  Splitting at these boundaries keeps each `decide` small
without changing candidate ordering or zero-forcing semantics.
-/
def lowerBoundClassIBlock (A : Finset Vertex) : List (Finset Vertex) :=
  branch1Size3HittingSets.flatMap fun B =>
    branch2Size3HittingSets.map fun C =>
      A ∪ B ∪ C

def lowerBoundClassIIBlock (A : Finset Vertex) : List (Finset Vertex) :=
  branch1Size3HittingSets.flatMap fun B =>
    branch2Size3HittingSets.flatMap fun C =>
      centreVertices.map fun t =>
        A ∪ B ∪ C ∪ {t}

def lowerBoundClassIII0Block (A : Finset Vertex) : List (Finset Vertex) :=
  branch1Size3HittingSets.flatMap fun B =>
    branch2Size3HittingSets.map fun C =>
      A ∪ B ∪ C

def lowerBoundClassIII1Block (A : Finset Vertex) : List (Finset Vertex) :=
  branch1Size4HittingSets.flatMap fun B =>
    branch2Size3HittingSets.map fun C =>
      A ∪ B ∪ C

def lowerBoundClassIII2Block (A : Finset Vertex) : List (Finset Vertex) :=
  branch1Size3HittingSets.flatMap fun B =>
    branch2Size4HittingSets.map fun C =>
      A ∪ B ∪ C

/--
Untrusted terminal-fort witness indices, partitioned along the exact structural
blocks above.  Lean checks every block below; the external generator is not
trusted.
-/
def lowerBoundCoverageI00 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageI01 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageI02 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageI03 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageI04 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageI05 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageI06 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageI07 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageI08 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageI09 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageI10 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageI11 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageII00 : List Nat := [
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13,
  37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13,
  39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13,
  37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12,
  35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12,
  35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12,
  33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12,
  35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12
]

def lowerBoundCoverageII01 : List Nat := [
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9,
  39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9,
  39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8,
  35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8,
  33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8
]

def lowerBoundCoverageII02 : List Nat := [
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13,
  37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13,
  39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13,
  37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12,
  35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12,
  35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12,
  33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12,
  35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12
]

def lowerBoundCoverageII03 : List Nat := [
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9,
  39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9,
  39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8,
  35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8,
  33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8
]

def lowerBoundCoverageII04 : List Nat := [
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13,
  37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13,
  39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13,
  37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12,
  35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12,
  35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12,
  33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12,
  35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12
]

def lowerBoundCoverageII05 : List Nat := [
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11,
  45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9,
  39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9,
  39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8,
  35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8,
  33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8
]

def lowerBoundCoverageII06 : List Nat := [
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5,
  39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4,
  35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4,
  33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4
]

def lowerBoundCoverageII07 : List Nat := [
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5,
  39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4,
  35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4,
  33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4
]

def lowerBoundCoverageII08 : List Nat := [
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5,
  39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4,
  35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4,
  33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4
]

def lowerBoundCoverageII09 : List Nat := [
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1,
  39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0,
  35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0,
  33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0
]

def lowerBoundCoverageII10 : List Nat := [
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1,
  39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0,
  35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0,
  33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0
]

def lowerBoundCoverageII11 : List Nat := [
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1,
  39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0,
  35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0,
  33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0
]

def lowerBoundCoverageIII0_00 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII0_01 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII0_02 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII0_03 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII0_04 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII0_05 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII0_06 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII0_07 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII0_08 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII0_09 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII0_10 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII0_11 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII0_12 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII0_13 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII0_14 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_15 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_16 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_17 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_18 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_19 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_20 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_21 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_22 : List Nat := [
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32
]

def lowerBoundCoverageIII0_23 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII0_24 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII1_00 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII1_01 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII1_02 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII1_03 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII1_04 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96
]

def lowerBoundCoverageIII1_05 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80
]

def lowerBoundCoverageIII1_06 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII1_07 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII1_08 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64
]

def lowerBoundCoverageIII1_09 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII1_10 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII1_11 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48
]

def lowerBoundCoverageIII2_00 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109,
  108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 105, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 101, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99,
  98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96
]

def lowerBoundCoverageIII2_01 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93,
  92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10,
  89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11,
  11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10,
  10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11,
  11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10,
  10, 10, 10, 10, 89, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9,
  9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9,
  9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9,
  9, 9, 9, 9, 9, 9, 9, 85, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8,
  8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82,
  8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83,
  82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80
]

def lowerBoundCoverageIII2_02 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109,
  108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 105, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 101, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99,
  98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96
]

def lowerBoundCoverageIII2_03 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93,
  92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10,
  89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11,
  11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10,
  10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11,
  11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10,
  10, 10, 10, 10, 89, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9,
  9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9,
  9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9,
  9, 9, 9, 9, 9, 9, 9, 85, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8,
  8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82,
  8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83,
  82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80
]

def lowerBoundCoverageIII2_04 : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109,
  108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15,
  15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 105, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13,
  13, 13, 13, 13, 13, 13, 13, 101, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99,
  98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96
]

def lowerBoundCoverageIII2_05 : List Nat := [
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93,
  92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10,
  89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11,
  11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10,
  10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11,
  11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10,
  10, 10, 10, 10, 89, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9,
  9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9,
  9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9,
  9, 9, 9, 9, 9, 9, 9, 85, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8,
  8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82,
  8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83,
  82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80
]

def lowerBoundCoverageIII2_06 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77,
  76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6,
  73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7,
  7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6,
  6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6,
  6, 6, 6, 6, 73, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 69, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67,
  66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64
]

def lowerBoundCoverageIII2_07 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77,
  76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6,
  73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7,
  7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6,
  6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6,
  6, 6, 6, 6, 73, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 69, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67,
  66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64
]

def lowerBoundCoverageIII2_08 : List Nat := [
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77,
  76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6,
  73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7,
  7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6,
  6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6,
  6, 6, 6, 6, 73, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 69, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4,
  4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66,
  4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67,
  66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64
]

def lowerBoundCoverageIII2_09 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61,
  60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 57, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 53, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51,
  50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48
]

def lowerBoundCoverageIII2_10 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61,
  60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 57, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 53, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51,
  50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48
]

def lowerBoundCoverageIII2_11 : List Nat := [
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61,
  60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2,
  2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2,
  2, 2, 2, 2, 57, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 53, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51,
  50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48
]

/-- Check candidate/witness pairs using the balanced certified selector. -/
def CoverageWitnessesValidBool :
    List (Finset Vertex) → List Nat → Bool
  | [], [] => true
  | S :: rest, i :: more =>
      match terminalFortCertificate i with
      | none => false
      | some cert =>
          if Disjoint S cert.1 then
            CoverageWitnessesValidBool rest more
          else
            false
  | _, _ => false

/-- Extract semantic coverage from a successfully checked witness list. -/
theorem CoverageWitnessesValidBool.of_mem
    {candidates : List (Finset Vertex)} {witnesses : List Nat}
    (hvalid :
      CoverageWitnessesValidBool candidates witnesses = true)
    {S : Finset Vertex}
    (hmem : S ∈ candidates) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  induction candidates generalizing witnesses with
  | nil =>
      simp at hmem
  | cons A rest ih =>
      cases witnesses with
      | nil =>
          simp [CoverageWitnessesValidBool] at hvalid
      | cons i more =>
          cases hfort : terminalFortCertificate i with
          | none =>
              simp [CoverageWitnessesValidBool, hfort] at hvalid
          | some cert =>
              by_cases hdisj : Disjoint A cert.1
              · have htail :
                    CoverageWitnessesValidBool rest more = true := by
                  simpa [CoverageWitnessesValidBool, hfort, hdisj] using hvalid
                simp only [List.mem_cons] at hmem
                rcases hmem with hEq | hmem
                · subst S
                  exact ⟨cert.1, terminalFortAt_mem cert.2, hdisj⟩
                · exact ih htail hmem
              · simp [CoverageWitnessesValidBool, hfort, hdisj] at hvalid

/--
Kernel checks for the 17,712 candidate/witness pairs, split into 73 bounded
structural blocks.  The largest block contains 432 candidates.  Every theorem
uses ordinary kernel `decide`.
-/
/--
Combine three bounded candidate slices without recomputing a large Boolean
certificate.  Each premise is independently kernel checked.
-/
private theorem CoverageWitnessesValidBool.of_mem_three_slices
    {xs : List (Finset Vertex)}
    {w0 w1 w2 : List Nat}
    {n m : Nat}
    (h0 : CoverageWitnessesValidBool (xs.take n) w0 = true)
    (h1 : CoverageWitnessesValidBool ((xs.drop n).take m) w1 = true)
    (h2 : CoverageWitnessesValidBool ((xs.drop n).drop m) w2 = true)
    {S : Finset Vertex}
    (hS : S ∈ xs) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  rw [← List.take_append_drop n xs] at hS
  simp only [List.mem_append] at hS
  rcases hS with hfirst | hrest
  · exact CoverageWitnessesValidBool.of_mem h0 hfirst
  · rw [← List.take_append_drop m (xs.drop n)] at hrest
    simp only [List.mem_append] at hrest
    rcases hrest with hsecond | hthird
    · exact CoverageWitnessesValidBool.of_mem h1 hsecond
    · exact CoverageWitnessesValidBool.of_mem h2 hthird

private theorem lowerBoundCoverageI00_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([4, 5, 8] : List Vertex).toFinset))
      lowerBoundCoverageI00 = true := by
  decide

private theorem lowerBoundCoverageI01_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([4, 5, 9] : List Vertex).toFinset))
      lowerBoundCoverageI01 = true := by
  decide

private theorem lowerBoundCoverageI02_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([4, 6, 8] : List Vertex).toFinset))
      lowerBoundCoverageI02 = true := by
  decide

private theorem lowerBoundCoverageI03_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([4, 6, 9] : List Vertex).toFinset))
      lowerBoundCoverageI03 = true := by
  decide

private theorem lowerBoundCoverageI04_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([5, 6, 8] : List Vertex).toFinset))
      lowerBoundCoverageI04 = true := by
  decide

private theorem lowerBoundCoverageI05_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([5, 6, 9] : List Vertex).toFinset))
      lowerBoundCoverageI05 = true := by
  decide

private theorem lowerBoundCoverageI06_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([5, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageI06 = true := by
  decide

private theorem lowerBoundCoverageI07_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([5, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageI07 = true := by
  decide

private theorem lowerBoundCoverageI08_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([5, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageI08 = true := by
  decide

private theorem lowerBoundCoverageI09_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([6, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageI09 = true := by
  decide

private theorem lowerBoundCoverageI10_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([6, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageI10 = true := by
  decide

private theorem lowerBoundCoverageI11_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIBlock (([6, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageI11 = true := by
  decide

private theorem lowerBoundCoverageII00_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([4, 5, 8] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII00.take 144 = true := by
  decide

private theorem lowerBoundCoverageII00_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 5, 8] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII00.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII00_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 5, 8] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII00.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII01_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([4, 5, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII01.take 144 = true := by
  decide

private theorem lowerBoundCoverageII01_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 5, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII01.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII01_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 5, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII01.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII02_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([4, 6, 8] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII02.take 144 = true := by
  decide

private theorem lowerBoundCoverageII02_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 6, 8] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII02.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII02_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 6, 8] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII02.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII03_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([4, 6, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII03.take 144 = true := by
  decide

private theorem lowerBoundCoverageII03_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 6, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII03.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII03_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([4, 6, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII03.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII04_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([5, 6, 8] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII04.take 144 = true := by
  decide

private theorem lowerBoundCoverageII04_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 6, 8] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII04.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII04_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 6, 8] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII04.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII05_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([5, 6, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII05.take 144 = true := by
  decide

private theorem lowerBoundCoverageII05_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 6, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII05.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII05_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 6, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII05.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII06_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([5, 7, 8] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII06.take 144 = true := by
  decide

private theorem lowerBoundCoverageII06_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 7, 8] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII06.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII06_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 7, 8] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII06.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII07_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([5, 7, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII07.take 144 = true := by
  decide

private theorem lowerBoundCoverageII07_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 7, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII07.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII07_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 7, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII07.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII08_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([5, 8, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII08.take 144 = true := by
  decide

private theorem lowerBoundCoverageII08_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 8, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII08.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII08_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([5, 8, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII08.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII09_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([6, 7, 8] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII09.take 144 = true := by
  decide

private theorem lowerBoundCoverageII09_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([6, 7, 8] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII09.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII09_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([6, 7, 8] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII09.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII10_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([6, 7, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII10.take 144 = true := by
  decide

private theorem lowerBoundCoverageII10_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([6, 7, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII10.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII10_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([6, 7, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII10.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageII11_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIIBlock (([6, 8, 9] : List Vertex).toFinset)).take 144
      lowerBoundCoverageII11.take 144 = true := by
  decide

private theorem lowerBoundCoverageII11_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([6, 8, 9] : List Vertex).toFinset)).drop 144).take 144
      (lowerBoundCoverageII11.drop 144).take 144 = true := by
  decide

private theorem lowerBoundCoverageII11_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIIBlock (([6, 8, 9] : List Vertex).toFinset)).drop 144).drop 144
      (lowerBoundCoverageII11.drop 144).drop 144 = true := by
  decide

private theorem lowerBoundCoverageIII0_00_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 4, 5, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_00 = true := by
  decide

private theorem lowerBoundCoverageIII0_01_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 4, 5, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_01 = true := by
  decide

private theorem lowerBoundCoverageIII0_02_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 4, 6, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_02 = true := by
  decide

private theorem lowerBoundCoverageIII0_03_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 4, 6, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_03 = true := by
  decide

private theorem lowerBoundCoverageIII0_04_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 5, 6, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_04 = true := by
  decide

private theorem lowerBoundCoverageIII0_05_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 5, 6, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_05 = true := by
  decide

private theorem lowerBoundCoverageIII0_06_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 5, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_06 = true := by
  decide

private theorem lowerBoundCoverageIII0_07_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 5, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_07 = true := by
  decide

private theorem lowerBoundCoverageIII0_08_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 5, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_08 = true := by
  decide

private theorem lowerBoundCoverageIII0_09_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 6, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_09 = true := by
  decide

private theorem lowerBoundCoverageIII0_10_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 6, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_10 = true := by
  decide

private theorem lowerBoundCoverageIII0_11_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([3, 6, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_11 = true := by
  decide

private theorem lowerBoundCoverageIII0_12_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 5, 6, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_12 = true := by
  decide

private theorem lowerBoundCoverageIII0_13_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 5, 6, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_13 = true := by
  decide

private theorem lowerBoundCoverageIII0_14_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 5, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_14 = true := by
  decide

private theorem lowerBoundCoverageIII0_15_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 5, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_15 = true := by
  decide

private theorem lowerBoundCoverageIII0_16_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 5, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_16 = true := by
  decide

private theorem lowerBoundCoverageIII0_17_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 6, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_17 = true := by
  decide

private theorem lowerBoundCoverageIII0_18_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 6, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_18 = true := by
  decide

private theorem lowerBoundCoverageIII0_19_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([4, 6, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_19 = true := by
  decide

private theorem lowerBoundCoverageIII0_20_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([5, 6, 7, 8] : List Vertex).toFinset))
      lowerBoundCoverageIII0_20 = true := by
  decide

private theorem lowerBoundCoverageIII0_21_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([5, 6, 7, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_21 = true := by
  decide

private theorem lowerBoundCoverageIII0_22_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([5, 6, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_22 = true := by
  decide

private theorem lowerBoundCoverageIII0_23_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([5, 7, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_23 = true := by
  decide

private theorem lowerBoundCoverageIII0_24_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII0Block (([6, 7, 8, 9] : List Vertex).toFinset))
      lowerBoundCoverageIII0_24 = true := by
  decide

private theorem lowerBoundCoverageIII1_00_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([4, 5, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_00.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_00_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 5, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_00.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_00_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 5, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_00.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_01_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([4, 5, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_01.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_01_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 5, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_01.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_01_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 5, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_01.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_02_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([4, 6, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_02.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_02_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 6, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_02.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_02_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 6, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_02.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_03_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([4, 6, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_03.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_03_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 6, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_03.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_03_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([4, 6, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_03.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_04_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([5, 6, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_04.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_04_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 6, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_04.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_04_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 6, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_04.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_05_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([5, 6, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_05.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_05_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 6, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_05.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_05_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 6, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_05.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_06_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([5, 7, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_06.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_06_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 7, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_06.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_06_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 7, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_06.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_07_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([5, 7, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_07.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_07_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 7, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_07.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_07_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 7, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_07.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_08_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([5, 8, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_08.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_08_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 8, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_08.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_08_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([5, 8, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_08.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_09_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([6, 7, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_09.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_09_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([6, 7, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_09.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_09_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([6, 7, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_09.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_10_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([6, 7, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_10.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_10_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([6, 7, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_10.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_10_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([6, 7, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_10.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_11_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII1Block (([6, 8, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII1_11.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_11_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([6, 8, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII1_11.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII1_11_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII1Block (([6, 8, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII1_11.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_00_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([4, 5, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_00.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_00_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 5, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_00.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_00_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 5, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_00.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_01_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([4, 5, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_01.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_01_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 5, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_01.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_01_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 5, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_01.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_02_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([4, 6, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_02.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_02_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 6, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_02.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_02_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 6, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_02.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_03_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([4, 6, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_03.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_03_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 6, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_03.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_03_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([4, 6, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_03.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_04_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([5, 6, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_04.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_04_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 6, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_04.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_04_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 6, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_04.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_05_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([5, 6, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_05.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_05_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 6, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_05.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_05_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 6, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_05.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_06_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([5, 7, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_06.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_06_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 7, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_06.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_06_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 7, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_06.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_07_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([5, 7, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_07.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_07_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 7, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_07.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_07_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 7, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_07.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_08_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([5, 8, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_08.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_08_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 8, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_08.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_08_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([5, 8, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_08.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_09_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([6, 7, 8] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_09.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_09_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([6, 7, 8] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_09.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_09_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([6, 7, 8] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_09.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_10_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([6, 7, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_10.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_10_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([6, 7, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_10.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_10_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([6, 7, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_10.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_11_a_valid :
    CoverageWitnessesValidBool
      (lowerBoundClassIII2Block (([6, 8, 9] : List Vertex).toFinset)).take 120
      lowerBoundCoverageIII2_11.take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_11_b_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([6, 8, 9] : List Vertex).toFinset)).drop 120).take 120
      (lowerBoundCoverageIII2_11.drop 120).take 120 = true := by
  decide

private theorem lowerBoundCoverageIII2_11_c_valid :
    CoverageWitnessesValidBool
      ((lowerBoundClassIII2Block (([6, 8, 9] : List Vertex).toFinset)).drop 120).drop 120
      (lowerBoundCoverageIII2_11.drop 120).drop 120 = true := by
  decide

private theorem lowerBoundClassIBlock_covered
    {A S : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hS : S ∈ lowerBoundClassIBlock A) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  simp only [branch0Size3HittingSets, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI00_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI01_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI02_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI03_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI04_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI05_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI06_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI07_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI08_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI09_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI10_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageI11_valid hS

private theorem lowerBoundClassIIBlock_covered
    {A S : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hS : S ∈ lowerBoundClassIIBlock A) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  simp only [branch0Size3HittingSets, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII00_a_valid lowerBoundCoverageII00_b_valid lowerBoundCoverageII00_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII01_a_valid lowerBoundCoverageII01_b_valid lowerBoundCoverageII01_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII02_a_valid lowerBoundCoverageII02_b_valid lowerBoundCoverageII02_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII03_a_valid lowerBoundCoverageII03_b_valid lowerBoundCoverageII03_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII04_a_valid lowerBoundCoverageII04_b_valid lowerBoundCoverageII04_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII05_a_valid lowerBoundCoverageII05_b_valid lowerBoundCoverageII05_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII06_a_valid lowerBoundCoverageII06_b_valid lowerBoundCoverageII06_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII07_a_valid lowerBoundCoverageII07_b_valid lowerBoundCoverageII07_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII08_a_valid lowerBoundCoverageII08_b_valid lowerBoundCoverageII08_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII09_a_valid lowerBoundCoverageII09_b_valid lowerBoundCoverageII09_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII10_a_valid lowerBoundCoverageII10_b_valid lowerBoundCoverageII10_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageII11_a_valid lowerBoundCoverageII11_b_valid lowerBoundCoverageII11_c_valid hS

private theorem lowerBoundClassIII0Block_covered
    {A S : Finset Vertex}
    (hA : A ∈ branch0Size4HittingSets)
    (hS : S ∈ lowerBoundClassIII0Block A) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  simp only [branch0Size4HittingSets, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_00_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_01_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_02_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_03_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_04_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_05_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_06_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_07_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_08_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_09_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_10_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_11_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_12_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_13_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_14_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_15_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_16_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_17_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_18_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_19_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_20_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_21_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_22_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_23_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem lowerBoundCoverageIII0_24_valid hS

private theorem lowerBoundClassIII1Block_covered
    {A S : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hS : S ∈ lowerBoundClassIII1Block A) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  simp only [branch0Size3HittingSets, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_00_a_valid lowerBoundCoverageIII1_00_b_valid lowerBoundCoverageIII1_00_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_01_a_valid lowerBoundCoverageIII1_01_b_valid lowerBoundCoverageIII1_01_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_02_a_valid lowerBoundCoverageIII1_02_b_valid lowerBoundCoverageIII1_02_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_03_a_valid lowerBoundCoverageIII1_03_b_valid lowerBoundCoverageIII1_03_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_04_a_valid lowerBoundCoverageIII1_04_b_valid lowerBoundCoverageIII1_04_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_05_a_valid lowerBoundCoverageIII1_05_b_valid lowerBoundCoverageIII1_05_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_06_a_valid lowerBoundCoverageIII1_06_b_valid lowerBoundCoverageIII1_06_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_07_a_valid lowerBoundCoverageIII1_07_b_valid lowerBoundCoverageIII1_07_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_08_a_valid lowerBoundCoverageIII1_08_b_valid lowerBoundCoverageIII1_08_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_09_a_valid lowerBoundCoverageIII1_09_b_valid lowerBoundCoverageIII1_09_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_10_a_valid lowerBoundCoverageIII1_10_b_valid lowerBoundCoverageIII1_10_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII1_11_a_valid lowerBoundCoverageIII1_11_b_valid lowerBoundCoverageIII1_11_c_valid hS

private theorem lowerBoundClassIII2Block_covered
    {A S : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hS : S ∈ lowerBoundClassIII2Block A) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  simp only [branch0Size3HittingSets, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA | hA
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_00_a_valid lowerBoundCoverageIII2_00_b_valid lowerBoundCoverageIII2_00_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_01_a_valid lowerBoundCoverageIII2_01_b_valid lowerBoundCoverageIII2_01_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_02_a_valid lowerBoundCoverageIII2_02_b_valid lowerBoundCoverageIII2_02_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_03_a_valid lowerBoundCoverageIII2_03_b_valid lowerBoundCoverageIII2_03_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_04_a_valid lowerBoundCoverageIII2_04_b_valid lowerBoundCoverageIII2_04_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_05_a_valid lowerBoundCoverageIII2_05_b_valid lowerBoundCoverageIII2_05_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_06_a_valid lowerBoundCoverageIII2_06_b_valid lowerBoundCoverageIII2_06_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_07_a_valid lowerBoundCoverageIII2_07_b_valid lowerBoundCoverageIII2_07_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_08_a_valid lowerBoundCoverageIII2_08_b_valid lowerBoundCoverageIII2_08_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_09_a_valid lowerBoundCoverageIII2_09_b_valid lowerBoundCoverageIII2_09_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_10_a_valid lowerBoundCoverageIII2_10_b_valid lowerBoundCoverageIII2_10_c_valid hS
  · subst A
    exact CoverageWitnessesValidBool.of_mem_three_slices
      lowerBoundCoverageIII2_11_a_valid lowerBoundCoverageIII2_11_b_valid lowerBoundCoverageIII2_11_c_valid hS

private theorem lowerBoundCandidateClassI_terminal_fort_coverage
    {S : Finset Vertex}
    (hmem : S ∈ lowerBoundCandidateClassI) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  change S ∈ branch0Size3HittingSets.flatMap lowerBoundClassIBlock at hmem
  simp only [List.mem_flatMap] at hmem
  rcases hmem with ⟨A, hA, hS⟩
  exact lowerBoundClassIBlock_covered hA hS

private theorem lowerBoundCandidateClassII_terminal_fort_coverage
    {S : Finset Vertex}
    (hmem : S ∈ lowerBoundCandidateClassII) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  change S ∈ branch0Size3HittingSets.flatMap lowerBoundClassIIBlock at hmem
  simp only [List.mem_flatMap] at hmem
  rcases hmem with ⟨A, hA, hS⟩
  exact lowerBoundClassIIBlock_covered hA hS

private theorem lowerBoundCandidateClassIII_terminal_fort_coverage
    {S : Finset Vertex}
    (hmem : S ∈ lowerBoundCandidateClassIII) :
    ∃ F ∈ lowerBoundTerminalForts, Disjoint S F := by
  change S ∈
    (branch0Size4HittingSets.flatMap lowerBoundClassIII0Block) ++
    (branch0Size3HittingSets.flatMap lowerBoundClassIII1Block) ++
    (branch0Size3HittingSets.flatMap lowerBoundClassIII2Block) at hmem
  simp only [List.mem_append, List.mem_flatMap] at hmem
  rcases hmem with h01 | h2
  · rcases h01 with h0 | h1
    · rcases h0 with ⟨A, hA, hS⟩
      exact lowerBoundClassIII0Block_covered hA hS
    · rcases h1 with ⟨A, hA, hS⟩
      exact lowerBoundClassIII1Block_covered hA hS
  · rcases h2 with ⟨A, hA, hS⟩
    exact lowerBoundClassIII2Block_covered hA hS

/--
Exhaustive finite obstruction certificate: every one of the formally generated
17,712 lower-bound candidates is disjoint from one of the 112 explicit
nonempty forts.
-/
theorem lowerBoundCandidates_terminal_fort_coverage :
    AllCandidatesCoveredBool lowerBoundCandidates = true := by
  apply AllCandidatesCoveredBool.eq_true_of_forall
  intro S hmem
  change S ∈
    lowerBoundCandidateClassI ++
    lowerBoundCandidateClassII ++
    lowerBoundCandidateClassIII at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hI_II | hIII
  · rcases hI_II with hI | hII
    · exact lowerBoundCandidateClassI_terminal_fort_coverage hI
    · exact lowerBoundCandidateClassII_terminal_fort_coverage hII
  · exact lowerBoundCandidateClassIII_terminal_fort_coverage hIII

/-- None of the 17,712 reduced candidates is a zero-forcing set. -/
theorem lowerBoundCandidates_not_zeroForcing :
    ∀ S ∈ lowerBoundCandidates, ¬ IsZeroForcingSet fischerGraph S := by
  intro S hmem hZ
  rcases AllCandidatesCoveredBool.of_mem
      lowerBoundCandidates_terminal_fort_coverage hmem with
    ⟨F, hFmem, hdisj⟩
  have hFvalid :
      F.Nonempty ∧ IsFort fischerGraph F :=
    AllTerminalFortsValid.of_mem lowerBoundTerminalForts_valid hFmem
  have hinter : (S ∩ F).Nonempty :=
    hZ.intersects_fort hFvalid.2 hFvalid.1
  rcases hinter with ⟨v, hv⟩
  have hvS : v ∈ S := (Finset.mem_inter.mp hv).1
  have hvF : v ∈ F := (Finset.mem_inter.mp hv).2
  exact (Finset.disjoint_left.mp hdisj) hvS hvF

/--
Fischer's graph has zero-forcing number at least eleven.

The only finite-search input is the already-proved 17,712-candidate reduction;
the contradiction then uses the exhaustive terminal-fort certificate above.
-/
theorem fischerGraph_zeroForcingNumber_ge :
    11 ≤ zeroForcingNumber fischerGraph := by
  unfold zeroForcingNumber
  have hnonempty :
      {n : ℕ |
        ∃ blue : Finset Vertex,
          blue.card = n ∧ IsZeroForcingSet fischerGraph blue}.Nonempty := by
    refine ⟨11, zeroForcingWitness, zeroForcingWitness_card, ?_⟩
    exact zeroForcingWitness_isZeroForcing
  have hmin :=
    Nat.sInf_mem hnonempty
  rcases hmin with ⟨S, hcard, hZ⟩
  by_contra hge
  have hsmall : S.card ≤ 10 := by
    have hsInfLt :
        sInf {n : ℕ |
          ∃ blue : Finset Vertex,
            blue.card = n ∧ IsZeroForcingSet fischerGraph blue} < 11 :=
      Nat.lt_of_not_ge hge
    omega
  have hmem :
      S ∈ lowerBoundCandidates :=
    zeroForcingSet_card_le_ten_mem_candidates hZ hsmall
  exact (lowerBoundCandidates_not_zeroForcing S hmem) hZ

/-- Fischer's explicit graph has zero-forcing number exactly eleven. -/
theorem fischerGraph_zeroForcingNumber :
    zeroForcingNumber fischerGraph = 11 := by
  exact le_antisymm
    fischerGraph_zeroForcingNumber_le
    fischerGraph_zeroForcingNumber_ge

/-- The exact numerical gap in the Fischer counterexample. -/
theorem fischerGraph_indepNum_lt_zeroForcingNumber :
    fischerGraph.indepNum < zeroForcingNumber fischerGraph := by
  rw [fischerGraph_indepNum, fischerGraph_zeroForcingNumber]
  omega

/--
Project-local statement of the completed Fischer counterexample certificate.
-/
theorem fischerGraph_counterexample :
    fischerGraph.Connected ∧
      (∀ v : Vertex, (fischerGraph.neighborSet v).ncard ≤ 3) ∧
      fischerGraph.indepNum = 9 ∧
      zeroForcingNumber fischerGraph = 11 := by
  exact ⟨fischerGraph_connected,
    fischerGraph_subcubic,
    fischerGraph_indepNum,
    fischerGraph_zeroForcingNumber⟩

end FischerZeroForcing
