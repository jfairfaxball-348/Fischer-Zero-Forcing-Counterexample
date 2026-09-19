import FischerZeroForcing.FischerGraph

/-!
# Fischer branch-0 fort certificate

This file formalizes the finite fort certificate for the first seven-vertex
branch of Fischer's graph.  The fort family and the minimum hitting-set
certificate are kept explicit and auditable; the only exhaustive checks range
over the 2^7 subsets of this one branch.
-/

namespace FischerZeroForcing

/-- The first seven-vertex branch: root 3 and the two attached triangles. -/
def branch0 : Finset Vertex :=
  ([3, 4, 5, 6, 7, 8, 9] : List Vertex).toFinset

/--
The twelve nonempty forts contained in branch 0, in the order produced by the
independent checker (increasing cardinality, then lexicographic order).
-/
def branch0Forts : List (Finset Vertex) :=
  [([5, 6] : List Vertex).toFinset,
   ([8, 9] : List Vertex).toFinset,
   ([4, 5, 7, 8] : List Vertex).toFinset,
   ([4, 5, 7, 9] : List Vertex).toFinset,
   ([4, 6, 7, 8] : List Vertex).toFinset,
   ([4, 6, 7, 9] : List Vertex).toFinset,
   ([5, 6, 8, 9] : List Vertex).toFinset,
   ([4, 5, 6, 7, 8] : List Vertex).toFinset,
   ([4, 5, 6, 7, 9] : List Vertex).toFinset,
   ([4, 5, 7, 8, 9] : List Vertex).toFinset,
   ([4, 6, 7, 8, 9] : List Vertex).toFinset,
   ([4, 5, 6, 7, 8, 9] : List Vertex).toFinset]

/-- Branch 0 contains exactly seven vertices. -/
theorem branch0_card : branch0.card = 7 := by
  native_decide

/-- The explicit branch-0 fort certificate has twelve entries. -/
theorem branch0Forts_length : branch0Forts.length = 12 := by
  native_decide

/-- The twelve explicit branch-0 forts are pairwise distinct. -/
theorem branch0Forts_nodup : branch0Forts.Nodup := by
  native_decide

/--
`S` hits a finite fort family when it has a vertex in every listed fort.

The recursive formulation is propositionally the usual membership statement,
but keeps finite certificate evaluation local to the supplied list rather than
to the ambient type of all finite vertex sets.
-/
def HitsForts (S : Finset Vertex) : List (Finset Vertex) → Prop
  | [] => True
  | F :: forts => (S ∩ F).Nonempty ∧ HitsForts S forts

/-- Membership formulation of `HitsForts`. -/
theorem hitsForts_iff {S : Finset Vertex} {forts : List (Finset Vertex)} :
    HitsForts S forts ↔ ∀ F ∈ forts, (S ∩ F).Nonempty := by
  induction forts with
  | nil =>
      simp [HitsForts]
  | cons F forts ih =>
      simp [HitsForts, ih]

/--
Complete branch-specific fort enumeration.

The left side explicitly checks the 128 subsets of branch 0 and keeps exactly
the nonempty forts.  Its equality with the human-readable twelve-set list is
the finite completeness certificate used below.
-/
theorem branch0_fort_filter_eq :
    branch0.powerset.filter (fun F => F.Nonempty ∧ IsFort fischerGraph F) =
      branch0Forts.toFinset := by
  native_decide

/-- Every explicitly listed branch-0 set is a nonempty fort. -/
theorem branch0Forts_areForts :
    ∀ F ∈ branch0Forts, IsFort fischerGraph F := by
  intro F hF
  have hmem : F ∈ branch0Forts.toFinset := by
    simpa using hF
  rw [← branch0_fort_filter_eq] at hmem
  exact (Finset.mem_filter.mp hmem).2.2

/-- Every explicitly listed branch-0 fort is nonempty. -/
theorem branch0Forts_nonempty :
    ∀ F ∈ branch0Forts, F.Nonempty := by
  intro F hF
  have hmem : F ∈ branch0Forts.toFinset := by
    simpa using hF
  rw [← branch0_fort_filter_eq] at hmem
  exact (Finset.mem_filter.mp hmem).2.1

/-- Every explicitly listed branch-0 fort lies inside branch 0. -/
theorem branch0Forts_subset :
    ∀ F ∈ branch0Forts, F ⊆ branch0 := by
  intro F hF
  have hmem : F ∈ branch0Forts.toFinset := by
    simpa using hF
  rw [← branch0_fort_filter_eq] at hmem
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1

/-- The twelve listed sets are exactly the nonempty forts contained in branch 0. -/
theorem branch0_fort_iff {F : Finset Vertex}
    (hsub : F ⊆ branch0) (hne : F.Nonempty) :
    IsFort fischerGraph F ↔ F ∈ branch0Forts := by
  constructor
  · intro hfort
    have hmem :
        F ∈ branch0.powerset.filter (fun T => T.Nonempty ∧ IsFort fischerGraph T) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hne, hfort⟩⟩
    rw [branch0_fort_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    exact branch0Forts_areForts F hmem

/-- Restricting a hitting set to a region containing every fort preserves hitting. -/
theorem HitsForts.inter_region {S region : Finset Vertex}
    {forts : List (Finset Vertex)}
    (hhit : HitsForts S forts)
    (hsub : ∀ F ∈ forts, F ⊆ region) :
    HitsForts (S ∩ region) forts := by
  rw [hitsForts_iff] at hhit ⊢
  intro F hF
  rcases hhit F hF with ⟨v, hv⟩
  have hvS : v ∈ S := (Finset.mem_inter.mp hv).1
  have hvF : v ∈ F := (Finset.mem_inter.mp hv).2
  have hvRegion : v ∈ region := hsub F hF hvF
  exact ⟨v, by simp [hvS, hvRegion, hvF]⟩

/-- No branch-0 subset of size at most two hits all twelve branch forts. -/
private theorem branch0_no_small_hitting_set :
    branch0.powerset.filter
        (fun S => S.card < 3 ∧ HitsForts S branch0Forts) = ∅ := by
  native_decide

/-- Any subset of branch 0 hitting every branch-0 fort has at least three vertices. -/
theorem branch0_hittingSet_card_ge_three {S : Finset Vertex}
    (hS : S ⊆ branch0)
    (hhit : HitsForts S branch0Forts) :
    3 ≤ S.card := by
  by_contra hcard
  have hlt : S.card < 3 := Nat.lt_of_not_ge hcard
  have hmem :
      S ∈ branch0.powerset.filter
        (fun T => T.card < 3 ∧ HitsForts T branch0Forts) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hS, ⟨hlt, hhit⟩⟩
  rw [branch0_no_small_hitting_set] at hmem
  simpa using hmem

/-- Any set hitting the branch-0 fort family uses at least three branch-0 vertices. -/
theorem branch0_three_le_card_inter {S : Finset Vertex}
    (hhit : HitsForts S branch0Forts) :
    3 ≤ (S ∩ branch0).card := by
  apply branch0_hittingSet_card_ge_three (S := S ∩ branch0)
  · exact Finset.inter_subset_right
  · exact HitsForts.inter_region hhit branch0Forts_subset

/--
The exact twelve size-three hitting sets for branch 0.
-/
def branch0Size3HittingSets : List (Finset Vertex) :=
  [([4, 5, 8] : List Vertex).toFinset,
   ([4, 5, 9] : List Vertex).toFinset,
   ([4, 6, 8] : List Vertex).toFinset,
   ([4, 6, 9] : List Vertex).toFinset,
   ([5, 6, 8] : List Vertex).toFinset,
   ([5, 6, 9] : List Vertex).toFinset,
   ([5, 7, 8] : List Vertex).toFinset,
   ([5, 7, 9] : List Vertex).toFinset,
   ([5, 8, 9] : List Vertex).toFinset,
   ([6, 7, 8] : List Vertex).toFinset,
   ([6, 7, 9] : List Vertex).toFinset,
   ([6, 8, 9] : List Vertex).toFinset]

/-- The explicit size-three hitting-set certificate has twelve entries. -/
theorem branch0Size3HittingSets_length : branch0Size3HittingSets.length = 12 := by
  native_decide

/-- The twelve explicit size-three hitting sets are pairwise distinct. -/
theorem branch0Size3HittingSets_nodup : branch0Size3HittingSets.Nodup := by
  native_decide

/-- Complete finite enumeration of the size-three branch-0 hitting sets. -/
theorem branch0_size3_hitting_filter_eq :
    branch0.powerset.filter
        (fun S => S.card = 3 ∧ HitsForts S branch0Forts) =
      branch0Size3HittingSets.toFinset := by
  native_decide

/-- A three-vertex branch-0 subset hits all forts exactly when it is on the explicit list. -/
theorem branch0_size3_hitting_iff {S : Finset Vertex}
    (hsub : S ⊆ branch0) (hcard : S.card = 3) :
    HitsForts S branch0Forts ↔ S ∈ branch0Size3HittingSets := by
  constructor
  · intro hhit
    have hmem :
        S ∈ branch0.powerset.filter
          (fun T => T.card = 3 ∧ HitsForts T branch0Forts) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hcard, hhit⟩⟩
    rw [branch0_size3_hitting_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    have hfin : S ∈ branch0Size3HittingSets.toFinset := by
      simpa using hmem
    rw [← branch0_size3_hitting_filter_eq] at hfin
    exact (Finset.mem_filter.mp hfin).2.2

/--
Local zero-forcing consequence: every zero-forcing set contains at least three
vertices from branch 0.

The proof exposes the intended architecture: a zero-forcing set intersects
each nonempty fort, hence hits the complete explicit branch family, and the
branch hitting-number certificate forces three branch vertices.
-/
theorem zeroForcingSet_branch0_card_ge_three {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S) :
    3 ≤ (S ∩ branch0).card := by
  apply branch0_three_le_card_inter
  rw [hitsForts_iff]
  intro F hF
  exact hZ.intersects_fort
    (branch0Forts_areForts F hF)
    (branch0Forts_nonempty F hF)

end FischerZeroForcing
