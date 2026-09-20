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
Every one of the 112 explicit obstruction sets is a nonempty fort.

The certificate is deliberately elaborated one fort at a time.  This is the
same kernel-checked finite proof as a single `decide`, but avoids forcing the
kernel to normalize one very large nested decision in a single reduction.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lowerBoundTerminalForts_valid :
    AllTerminalFortsValid lowerBoundTerminalForts := by
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  refine ⟨by decide, ?_⟩
  trivial

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
For each of the 17,712 candidates, this list gives the zero-based index of one
of the 112 terminal forts disjoint from that candidate.

The indices are certificate data only: their provenance is not trusted.  Lean
checks every candidate/index pair below, and the selector theorem proves that
each selected obstruction really belongs to `lowerBoundTerminalForts`.
-/
def lowerBoundCoverageWitnesses : List Nat := [
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77,
  77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65,
  65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66,
  67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77,
  77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65,
  65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53,
  53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50,
  51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61,
  61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49,
  49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53,
  53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50,
  51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15, 45, 29, 15, 44, 28, 15, 44, 28,
  15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40,
  28, 14, 40, 28, 14, 40, 28, 14, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 41, 29,
  14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46,
  30, 15, 45, 29, 15, 45, 29, 15, 45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14, 39, 31, 13, 38, 30, 13, 39, 31,
  13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 39, 31, 13, 38,
  30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28,
  13, 36, 28, 13, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32,
  28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12,
  33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29,
  12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46,
  26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10, 47, 27, 11, 46, 26, 11, 47, 27,
  11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42,
  26, 10, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24,
  11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40,
  24, 10, 40, 24, 10, 40, 24, 10, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25,
  9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38,
  26, 9, 37, 25, 9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34, 26, 8, 35, 27,
  8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34,
  26, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15, 45, 29, 15, 44, 28, 15, 44, 28,
  15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40,
  28, 14, 40, 28, 14, 40, 28, 14, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 41, 29,
  14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46,
  30, 15, 45, 29, 15, 45, 29, 15, 45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14, 39, 31, 13, 38, 30, 13, 39, 31,
  13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 39, 31, 13, 38,
  30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28,
  13, 36, 28, 13, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32,
  28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12,
  33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29,
  12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46,
  26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10, 47, 27, 11, 46, 26, 11, 47, 27,
  11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42,
  26, 10, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24,
  11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40,
  24, 10, 40, 24, 10, 40, 24, 10, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25,
  9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38,
  26, 9, 37, 25, 9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34, 26, 8, 35, 27,
  8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34,
  26, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8,
  47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15, 45, 29, 15, 44, 28, 15, 44, 28,
  15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40,
  28, 14, 40, 28, 14, 40, 28, 14, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 45, 29, 15, 45, 29, 15,
  45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14, 41, 29,
  14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46, 30, 15, 47, 31, 15, 46,
  30, 15, 45, 29, 15, 45, 29, 15, 45, 29, 15, 44, 28, 15, 44, 28, 15, 44, 28, 15, 43, 31, 14, 42, 30, 14, 43, 31, 14, 42, 30, 14,
  43, 31, 14, 42, 30, 14, 41, 29, 14, 41, 29, 14, 41, 29, 14, 40, 28, 14, 40, 28, 14, 40, 28, 14, 39, 31, 13, 38, 30, 13, 39, 31,
  13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13, 39, 31, 13, 38,
  30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28, 13, 36, 28, 13,
  39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 39, 31, 13, 38, 30, 13, 37, 29, 13, 37, 29, 13, 37, 29, 13, 36, 28, 13, 36, 28,
  13, 36, 28, 13, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12, 33, 29, 12, 32,
  28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29, 12, 33, 29, 12,
  33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 35, 31, 12, 34, 30, 12, 33, 29,
  12, 33, 29, 12, 33, 29, 12, 32, 28, 12, 32, 28, 12, 32, 28, 12, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46,
  26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10,
  43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10, 47, 27, 11, 46, 26, 11, 47, 27,
  11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24, 11, 44, 24, 11, 43, 27, 10, 42,
  26, 10, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40, 24, 10, 40, 24, 10, 40, 24, 10,
  47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 47, 27, 11, 46, 26, 11, 45, 25, 11, 45, 25, 11, 45, 25, 11, 44, 24, 11, 44, 24,
  11, 44, 24, 11, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 43, 27, 10, 42, 26, 10, 41, 25, 10, 41, 25, 10, 41, 25, 10, 40,
  24, 10, 40, 24, 10, 40, 24, 10, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25, 9, 37, 25, 9,
  37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 37, 25,
  9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38, 26, 9, 39, 27, 9, 38,
  26, 9, 37, 25, 9, 37, 25, 9, 37, 25, 9, 36, 24, 9, 36, 24, 9, 36, 24, 9, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8,
  35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34, 26, 8, 35, 27,
  8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8, 35, 27, 8, 34,
  26, 8, 35, 27, 8, 34, 26, 8, 35, 27, 8, 34, 26, 8, 33, 25, 8, 33, 25, 8, 33, 25, 8, 32, 24, 8, 32, 24, 8, 32, 24, 8,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20,
  7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40,
  20, 6, 40, 20, 6, 40, 20, 6, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 41, 21,
  6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46,
  22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6, 39, 23, 5, 38, 22, 5, 39, 23,
  5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38,
  22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20,
  5, 36, 20, 5, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32,
  20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4,
  33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21,
  4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46,
  22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6, 47, 23, 7, 46, 22, 7, 47, 23,
  7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42,
  22, 6, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20,
  7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40,
  20, 6, 40, 20, 6, 40, 20, 6, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5,
  37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21,
  5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38,
  22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4,
  35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23,
  4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34,
  22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4,
  47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20,
  7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40,
  20, 6, 40, 20, 6, 40, 20, 6, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 45, 21, 7, 45, 21, 7,
  45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6, 41, 21,
  6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46, 22, 7, 47, 23, 7, 46,
  22, 7, 45, 21, 7, 45, 21, 7, 45, 21, 7, 44, 20, 7, 44, 20, 7, 44, 20, 7, 43, 23, 6, 42, 22, 6, 43, 23, 6, 42, 22, 6,
  43, 23, 6, 42, 22, 6, 41, 21, 6, 41, 21, 6, 41, 21, 6, 40, 20, 6, 40, 20, 6, 40, 20, 6, 39, 23, 5, 38, 22, 5, 39, 23,
  5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5, 39, 23, 5, 38,
  22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20, 5, 36, 20, 5,
  39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 39, 23, 5, 38, 22, 5, 37, 21, 5, 37, 21, 5, 37, 21, 5, 36, 20, 5, 36, 20,
  5, 36, 20, 5, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4, 33, 21, 4, 32,
  20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21, 4, 33, 21, 4,
  33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 35, 23, 4, 34, 22, 4, 33, 21,
  4, 33, 21, 4, 33, 21, 4, 32, 20, 4, 32, 20, 4, 32, 20, 4, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46,
  18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2, 47, 19, 3, 46, 18, 3, 47, 19,
  3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42,
  18, 2, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16,
  3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40,
  16, 2, 40, 16, 2, 40, 16, 2, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17,
  1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38,
  18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19,
  0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34,
  18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16,
  3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40,
  16, 2, 40, 16, 2, 40, 16, 2, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3,
  45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 41, 17,
  2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46,
  18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2, 39, 19, 1, 38, 18, 1, 39, 19,
  1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38,
  18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1,
  39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16,
  1, 36, 16, 1, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32,
  16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0,
  33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17,
  0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46,
  18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2,
  43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2, 47, 19, 3, 46, 18, 3, 47, 19,
  3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16, 3, 44, 16, 3, 43, 19, 2, 42,
  18, 2, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40, 16, 2, 40, 16, 2, 40, 16, 2,
  47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 47, 19, 3, 46, 18, 3, 45, 17, 3, 45, 17, 3, 45, 17, 3, 44, 16, 3, 44, 16,
  3, 44, 16, 3, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 43, 19, 2, 42, 18, 2, 41, 17, 2, 41, 17, 2, 41, 17, 2, 40,
  16, 2, 40, 16, 2, 40, 16, 2, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17, 1, 37, 17, 1,
  37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 37, 17,
  1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38, 18, 1, 39, 19, 1, 38,
  18, 1, 37, 17, 1, 37, 17, 1, 37, 17, 1, 36, 16, 1, 36, 16, 1, 36, 16, 1, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0,
  35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34, 18, 0, 35, 19,
  0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0, 35, 19, 0, 34,
  18, 0, 35, 19, 0, 34, 18, 0, 35, 19, 0, 34, 18, 0, 33, 17, 0, 33, 17, 0, 33, 17, 0, 32, 16, 0, 32, 16, 0, 32, 16, 0,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77,
  77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65,
  65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66,
  67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77,
  77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65,
  65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53,
  53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50,
  51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61,
  61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49,
  49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53,
  53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50,
  51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90,
  91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85,
  85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45,
  45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33,
  33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37,
  37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34,
  35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45,
  45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33,
  33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37,
  37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34,
  35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45,
  45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33,
  33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37,
  37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34,
  35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45,
  45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33,
  33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37,
  37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34,
  35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32,
  47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45,
  45, 44, 44, 44, 43, 42, 43, 42, 43, 42, 41, 41, 41, 40, 40, 40, 47, 46, 47, 46, 47, 46, 45, 45, 45, 44, 44, 44, 43, 42, 43, 42,
  43, 42, 41, 41, 41, 40, 40, 40, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36,
  39, 38, 39, 38, 39, 38, 37, 37, 37, 36, 36, 36, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33,
  33, 32, 32, 32, 35, 34, 35, 34, 35, 34, 33, 33, 33, 32, 32, 32, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66,
  67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61,
  61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58,
  59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49,
  49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101,
  101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98,
  99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 31, 30, 31, 30, 31, 30, 29, 29,
  29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30,
  31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29,
  29, 28, 28, 28, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94,
  95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92,
  91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89,
  89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86,
  87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89,
  89, 88, 88, 88, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26,
  27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25,
  25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82,
  83, 82, 81, 81, 81, 80, 80, 80, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102,
  103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30,
  31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29,
  29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 103, 102, 103, 102,
  103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92,
  91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89,
  89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86,
  87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81,
  81, 80, 80, 80, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 27, 26, 27, 26,
  27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25,
  25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26,
  27, 26, 25, 25, 25, 24, 24, 24, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97,
  97, 96, 96, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 107, 106, 107, 106,
  107, 106, 105, 105, 105, 104, 104, 104, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28,
  31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29,
  29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30,
  31, 30, 29, 29, 29, 28, 28, 28, 31, 30, 31, 30, 31, 30, 29, 29, 29, 28, 28, 28, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100,
  99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89,
  89, 88, 88, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 95, 94, 95, 94,
  95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81,
  81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 95, 94, 95, 94,
  95, 94, 93, 93, 93, 92, 92, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25,
  25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26,
  27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24, 27, 26, 27, 26, 27, 26, 25, 25, 25, 24, 24, 24,
  87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 79, 78, 79, 78, 79, 78, 77, 77,
  77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66,
  67, 66, 65, 65, 65, 64, 64, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21,
  21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22,
  23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65,
  65, 64, 64, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78,
  79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76,
  75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66,
  67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76,
  75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21,
  21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22,
  23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74,
  75, 74, 73, 73, 73, 72, 72, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 71, 70, 71, 70, 71, 70, 69, 69,
  69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66,
  67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 23, 22, 23, 22, 23, 22, 21, 21,
  21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22,
  23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20,
  23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21, 21, 20, 20, 20, 23, 22, 23, 22, 23, 22, 21, 21,
  21, 20, 20, 20, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 63, 62, 63, 62,
  63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60,
  59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57,
  57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54,
  55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57,
  57, 56, 56, 56, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18,
  19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17,
  17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50,
  51, 50, 49, 49, 49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56,
  63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61,
  61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54,
  55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61,
  61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18,
  19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17,
  17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 55, 54, 55, 54,
  55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60,
  59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57,
  57, 56, 56, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 55, 54, 55, 54,
  55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 51, 50, 51, 50, 49, 49,
  49, 48, 48, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 19, 18, 19, 18,
  19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16,
  19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17,
  17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18, 19, 18, 17, 17, 17, 16, 16, 16, 19, 18, 19, 18,
  19, 18, 17, 17, 17, 16, 16, 16, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48,
  111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105,
  105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110,
  15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14,
  14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107,
  106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14, 105, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100,
  100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13,
  13, 13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101,
  100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98,
  97, 97, 97, 96, 96, 96, 99, 98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99,
  98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11,
  11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88, 95, 94,
  95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89,
  88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11,
  11, 11, 11, 11, 11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10,
  89, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87,
  86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84,
  87, 86, 9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8, 8, 8,
  8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83,
  82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 111, 110, 111, 110, 111, 110, 109, 109,
  109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14,
  14, 14, 14, 14, 14, 14, 14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15,
  15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14, 105, 104, 111, 110, 111, 110,
  111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104,
  104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14, 105, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13,
  13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101, 100,
  103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101, 100, 99, 98, 99, 98, 99, 98, 97,
  97, 97, 96, 96, 96, 99, 98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98,
  12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12, 12, 12, 12, 12, 12, 12,
  12, 12, 97, 96, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93, 92, 91, 90, 91,
  90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92,
  92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10,
  10, 10, 10, 10, 10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93,
  92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88, 87, 86, 87, 86, 87, 86,
  85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87,
  86, 9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9, 9, 9,
  9, 9, 9, 85, 84, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82,
  83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81,
  80, 80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15,
  15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14,
  105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108, 111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107,
  106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14, 14, 14, 14, 14, 105, 104, 111, 110, 111, 110, 111, 110, 109, 109, 109, 108, 108, 108,
  111, 110, 15, 15, 15, 15, 15, 15, 15, 15, 15, 109, 108, 107, 106, 107, 106, 107, 106, 105, 105, 105, 104, 104, 104, 107, 106, 14, 14, 14, 14, 14,
  14, 14, 14, 14, 105, 104, 103, 102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101, 100, 103,
  102, 103, 102, 103, 102, 101, 101, 101, 100, 100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101, 100, 103, 102, 103, 102, 103, 102, 101, 101,
  101, 100, 100, 100, 103, 102, 13, 13, 13, 13, 13, 13, 13, 13, 13, 101, 100, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12,
  12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12, 12, 12, 12, 12, 12, 12, 12,
  12, 97, 96, 99, 98, 99, 98, 99, 98, 97, 97, 97, 96, 96, 96, 99, 98, 12, 12, 12, 12, 12, 12, 12, 12, 12, 97, 96, 95, 94, 95, 94,
  95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88,
  88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88, 95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11,
  11, 11, 11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89, 89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88,
  95, 94, 95, 94, 95, 94, 93, 93, 93, 92, 92, 92, 95, 94, 11, 11, 11, 11, 11, 11, 11, 11, 11, 93, 92, 91, 90, 91, 90, 91, 90, 89,
  89, 89, 88, 88, 88, 91, 90, 10, 10, 10, 10, 10, 10, 10, 10, 10, 89, 88, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86,
  9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9, 9, 9, 9,
  9, 9, 85, 84, 87, 86, 87, 86, 87, 86, 85, 85, 85, 84, 84, 84, 87, 86, 9, 9, 9, 9, 9, 9, 9, 9, 9, 85, 84, 83, 82, 83,
  82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80,
  80, 80, 83, 82, 8, 8, 8, 8, 8, 8, 8, 8, 8, 81, 80, 83, 82, 83, 82, 83, 82, 81, 81, 81, 80, 80, 80, 83, 82, 8, 8, 8,
  8, 8, 8, 8, 8, 8, 81, 80, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77,
  76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 79, 78, 79, 78, 79, 78,
  77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75,
  74, 6, 6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 71, 70,
  71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69,
  68, 68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5,
  5, 5, 5, 5, 5, 5, 5, 69, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4,
  65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67,
  66, 65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76,
  79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6,
  6, 6, 6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75,
  74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77,
  77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6,
  6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70,
  71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5, 5, 69, 68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64,
  64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4,
  4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64,
  79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73,
  73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78,
  7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75, 74, 75, 74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6,
  6, 6, 73, 72, 79, 78, 79, 78, 79, 78, 77, 77, 77, 76, 76, 76, 79, 78, 7, 7, 7, 7, 7, 7, 7, 7, 7, 77, 76, 75, 74, 75,
  74, 75, 74, 73, 73, 73, 72, 72, 72, 75, 74, 6, 6, 6, 6, 6, 6, 6, 6, 6, 73, 72, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68,
  68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 69, 68, 71, 70, 71, 70, 71, 70, 69, 69, 69, 68, 68, 68, 71, 70, 5, 5, 5, 5, 5, 5, 5, 5, 5, 69,
  68, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66,
  65, 65, 65, 64, 64, 64, 67, 66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 67, 66, 67, 66, 67, 66, 65, 65, 65, 64, 64, 64, 67,
  66, 4, 4, 4, 4, 4, 4, 4, 4, 4, 65, 64, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3,
  3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 63, 62,
  63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57,
  56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3,
  3, 3, 3, 3, 3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2,
  57, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55,
  54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52,
  55, 54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51,
  50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 63, 62, 63, 62, 63, 62, 61, 61,
  61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2,
  2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 63, 62, 63, 62,
  63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56,
  56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52,
  55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52, 51, 50, 51, 50, 51, 50, 49,
  49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 49, 48, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61, 60, 59, 58, 59,
  58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60,
  60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61, 60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2,
  2, 2, 2, 2, 2, 2, 57, 56, 63, 62, 63, 62, 63, 62, 61, 61, 61, 60, 60, 60, 63, 62, 3, 3, 3, 3, 3, 3, 3, 3, 3, 61,
  60, 59, 58, 59, 58, 59, 58, 57, 57, 57, 56, 56, 56, 59, 58, 2, 2, 2, 2, 2, 2, 2, 2, 2, 57, 56, 55, 54, 55, 54, 55, 54,
  53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55,
  54, 1, 1, 1, 1, 1, 1, 1, 1, 1, 53, 52, 55, 54, 55, 54, 55, 54, 53, 53, 53, 52, 52, 52, 55, 54, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 53, 52, 51, 50, 51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50,
  51, 50, 51, 50, 49, 49, 49, 48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48, 51, 50, 51, 50, 51, 50, 49, 49, 49,
  48, 48, 48, 51, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 48
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
Kernel check of all 17,712 explicit candidate/witness pairs.  Unlike the former
monolithic search, this performs one checked disjointness test per candidate.
-/
theorem lowerBoundCoverageWitnesses_valid :
    CoverageWitnessesValidBool
      lowerBoundCandidates lowerBoundCoverageWitnesses = true := by
  decide

/--
Exhaustive finite obstruction certificate: every one of the formally generated
17,712 lower-bound candidates is disjoint from one of the 112 explicit
nonempty forts.
-/
theorem lowerBoundCandidates_terminal_fort_coverage :
    AllCandidatesCoveredBool lowerBoundCandidates = true := by
  apply AllCandidatesCoveredBool.eq_true_of_forall
  intro S hmem
  exact CoverageWitnessesValidBool.of_mem
    lowerBoundCoverageWitnesses_valid hmem

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
