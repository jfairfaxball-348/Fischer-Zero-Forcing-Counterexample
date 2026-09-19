import FischerZeroForcing.Certificates
import FischerZeroForcing.LowerBoundCandidates
import FischerZeroForcing.ZeroForcingClosure

/-!
# Fischer zero-forcing lower bound

The source fort reduction has already reduced every hypothetical zero-forcing
set of cardinality at most ten to the explicit list `lowerBoundCandidates`.
This file performs the remaining finite check with the verified deterministic
closure and derives the exact zero-forcing number.
-/

namespace FischerZeroForcing

/--
A compact Boolean certificate saying that the deterministic closure of every
listed candidate stops short of the full vertex set.

Using a Boolean accumulator avoids constructing a 17,712-deep nested
proposition during native evaluation while checking exactly the same exhaustive
candidate family.
-/
def AllCandidatesFailBool : List (Finset Vertex) → Bool
  | [] => true
  | S :: rest =>
      decide (fischerForceClosure S ≠ (Finset.univ : Finset Vertex)) &&
      AllCandidatesFailBool rest

/-- Membership extraction from the recursive finite Boolean failure certificate. -/
theorem AllCandidatesFailBool.of_mem
    {candidates : List (Finset Vertex)}
    (hfail : AllCandidatesFailBool candidates = true)
    {S : Finset Vertex}
    (hmem : S ∈ candidates) :
    fischerForceClosure S ≠ (Finset.univ : Finset Vertex) := by
  induction candidates with
  | nil =>
      simp at hmem
  | cons A rest ih =>
      simp only [AllCandidatesFailBool] at hfail
      have hparts :
          decide
              (fischerForceClosure A ≠ (Finset.univ : Finset Vertex)) = true ∧
            AllCandidatesFailBool rest = true :=
        Bool.and_eq_true_iff.mp hfail
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · subst S
        exact of_decide_eq_true hparts.1
      · exact ih hparts.2 hmem

/--
The single finite computation for Fischer's lower-bound obstruction:
all 17,712 already-generated candidates have non-full deterministic closure.
-/
theorem lowerBoundCandidates_closure_fail :
    AllCandidatesFailBool lowerBoundCandidates = true := by
  native_decide

/-- None of the 17,712 reduced candidates is a zero-forcing set. -/
theorem lowerBoundCandidates_not_zeroForcing :
    ∀ S ∈ lowerBoundCandidates, ¬ IsZeroForcingSet fischerGraph S := by
  intro S hmem hZ
  have hfail :
      fischerForceClosure S ≠ (Finset.univ : Finset Vertex) :=
    AllCandidatesFailBool.of_mem lowerBoundCandidates_closure_fail hmem
  exact hfail ((fischerForceClosure_eq_univ_iff S).2 hZ)

/--
Fischer's graph has zero-forcing number at least eleven.

The only finite-search input is the already-proved 17,712-candidate reduction;
the contradiction then uses the exhaustive candidate failure certificate above.
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
