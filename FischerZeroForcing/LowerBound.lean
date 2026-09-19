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

/-- Every one of the 112 explicit obstruction sets is a nonempty fort. -/
theorem lowerBoundTerminalForts_valid :
    AllTerminalFortsValid lowerBoundTerminalForts := by
  decide

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
Exhaustive finite obstruction certificate: every one of the formally generated
17,712 lower-bound candidates is disjoint from one of the 112 explicit
nonempty forts.
-/
set_option maxRecDepth 100000 maxHeartbeats 0 in
theorem lowerBoundCandidates_terminal_fort_coverage :
    AllCandidatesCoveredBool lowerBoundCandidates = true := by
  decide

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
