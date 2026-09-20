import FischerZeroForcing.BranchForts

/-!
# Remaining branch fort and hitting-set certificates

This file extends the already closed branch-0 certificate to branches 1 and 2,
and records the exact size-four hitting-set families for all three branches.
All exhaustive checks remain local to a seven-vertex branch.
-/

namespace FischerZeroForcing

/-- The second seven-vertex branch. -/
def branch1 : Finset Vertex :=
  ([10, 11, 12, 13, 14, 15, 16] : List Vertex).toFinset

/-- The third seven-vertex branch. -/
def branch2 : Finset Vertex :=
  ([17, 18, 19, 20, 21, 22, 23] : List Vertex).toFinset

/-- The twelve nonempty forts contained in branch 1. -/
def branch1Forts : List (Finset Vertex) :=
  [([12, 13] : List Vertex).toFinset,
   ([15, 16] : List Vertex).toFinset,
   ([11, 12, 14, 15] : List Vertex).toFinset,
   ([11, 12, 14, 16] : List Vertex).toFinset,
   ([11, 13, 14, 15] : List Vertex).toFinset,
   ([11, 13, 14, 16] : List Vertex).toFinset,
   ([12, 13, 15, 16] : List Vertex).toFinset,
   ([11, 12, 13, 14, 15] : List Vertex).toFinset,
   ([11, 12, 13, 14, 16] : List Vertex).toFinset,
   ([11, 12, 14, 15, 16] : List Vertex).toFinset,
   ([11, 13, 14, 15, 16] : List Vertex).toFinset,
   ([11, 12, 13, 14, 15, 16] : List Vertex).toFinset]

/-- The twelve nonempty forts contained in branch 2. -/
def branch2Forts : List (Finset Vertex) :=
  [([19, 20] : List Vertex).toFinset,
   ([22, 23] : List Vertex).toFinset,
   ([18, 19, 21, 22] : List Vertex).toFinset,
   ([18, 19, 21, 23] : List Vertex).toFinset,
   ([18, 20, 21, 22] : List Vertex).toFinset,
   ([18, 20, 21, 23] : List Vertex).toFinset,
   ([19, 20, 22, 23] : List Vertex).toFinset,
   ([18, 19, 20, 21, 22] : List Vertex).toFinset,
   ([18, 19, 20, 21, 23] : List Vertex).toFinset,
   ([18, 19, 21, 22, 23] : List Vertex).toFinset,
   ([18, 20, 21, 22, 23] : List Vertex).toFinset,
   ([18, 19, 20, 21, 22, 23] : List Vertex).toFinset]

private instance branchCertificatesHitsFortsDecidable
    (S : Finset Vertex) (forts : List (Finset Vertex)) :
    Decidable (HitsForts S forts) := by
  induction forts with
  | nil =>
      exact isTrue trivial
  | cons F forts ih =>
      letI : Decidable (HitsForts S forts) := ih
      change Decidable ((S ∩ F).Nonempty ∧ HitsForts S forts)
      infer_instance

private instance branchCertificatesFortDecidable (F : Finset Vertex) :
    Decidable (IsFort fischerGraph F) := by
  unfold IsFort
  infer_instance

theorem branch1_card : branch1.card = 7 := by
  decide

theorem branch2_card : branch2.card = 7 := by
  decide

theorem branch1Forts_length : branch1Forts.length = 12 := by
  decide

theorem branch2Forts_length : branch2Forts.length = 12 := by
  decide

theorem branch1Forts_nodup : branch1Forts.Nodup := by
  decide

theorem branch2Forts_nodup : branch2Forts.Nodup := by
  decide

theorem branch1_fort_filter_eq :
    branch1.powerset.filter (fun F => F.Nonempty ∧ IsFort fischerGraph F) =
      branch1Forts.toFinset := by
  decide

theorem branch2_fort_filter_eq :
    branch2.powerset.filter (fun F => F.Nonempty ∧ IsFort fischerGraph F) =
      branch2Forts.toFinset := by
  decide

theorem branch1Forts_areForts :
    ∀ F ∈ branch1Forts, IsFort fischerGraph F := by
  intro F hF
  have hmem : F ∈ branch1Forts.toFinset := by
    simpa using hF
  rw [← branch1_fort_filter_eq] at hmem
  exact (Finset.mem_filter.mp hmem).2.2

theorem branch2Forts_areForts :
    ∀ F ∈ branch2Forts, IsFort fischerGraph F := by
  intro F hF
  have hmem : F ∈ branch2Forts.toFinset := by
    simpa using hF
  rw [← branch2_fort_filter_eq] at hmem
  exact (Finset.mem_filter.mp hmem).2.2

theorem branch1Forts_nonempty :
    ∀ F ∈ branch1Forts, F.Nonempty := by
  intro F hF
  have hmem : F ∈ branch1Forts.toFinset := by
    simpa using hF
  rw [← branch1_fort_filter_eq] at hmem
  exact (Finset.mem_filter.mp hmem).2.1

theorem branch2Forts_nonempty :
    ∀ F ∈ branch2Forts, F.Nonempty := by
  intro F hF
  have hmem : F ∈ branch2Forts.toFinset := by
    simpa using hF
  rw [← branch2_fort_filter_eq] at hmem
  exact (Finset.mem_filter.mp hmem).2.1

theorem branch1Forts_subset :
    ∀ F ∈ branch1Forts, F ⊆ branch1 := by
  intro F hF
  have hmem : F ∈ branch1Forts.toFinset := by
    simpa using hF
  rw [← branch1_fort_filter_eq] at hmem
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1

theorem branch2Forts_subset :
    ∀ F ∈ branch2Forts, F ⊆ branch2 := by
  intro F hF
  have hmem : F ∈ branch2Forts.toFinset := by
    simpa using hF
  rw [← branch2_fort_filter_eq] at hmem
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1

theorem branch1_fort_iff {F : Finset Vertex}
    (hsub : F ⊆ branch1) (hne : F.Nonempty) :
    IsFort fischerGraph F ↔ F ∈ branch1Forts := by
  constructor
  · intro hfort
    have hmem :
        F ∈ branch1.powerset.filter (fun T => T.Nonempty ∧ IsFort fischerGraph T) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hne, hfort⟩⟩
    rw [branch1_fort_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    exact branch1Forts_areForts F hmem

theorem branch2_fort_iff {F : Finset Vertex}
    (hsub : F ⊆ branch2) (hne : F.Nonempty) :
    IsFort fischerGraph F ↔ F ∈ branch2Forts := by
  constructor
  · intro hfort
    have hmem :
        F ∈ branch2.powerset.filter (fun T => T.Nonempty ∧ IsFort fischerGraph T) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hne, hfort⟩⟩
    rw [branch2_fort_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    exact branch2Forts_areForts F hmem

private theorem branch1_no_small_hitting_set :
    branch1.powerset.filter
        (fun S => S.card < 3 ∧ HitsForts S branch1Forts) = ∅ := by
  decide

private theorem branch2_no_small_hitting_set :
    branch2.powerset.filter
        (fun S => S.card < 3 ∧ HitsForts S branch2Forts) = ∅ := by
  decide

theorem branch1_hittingSet_card_ge_three {S : Finset Vertex}
    (hS : S ⊆ branch1)
    (hhit : HitsForts S branch1Forts) :
    3 ≤ S.card := by
  by_contra hcard
  have hlt : S.card < 3 := Nat.lt_of_not_ge hcard
  have hmem :
      S ∈ branch1.powerset.filter
        (fun T => T.card < 3 ∧ HitsForts T branch1Forts) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hS, ⟨hlt, hhit⟩⟩
  rw [branch1_no_small_hitting_set] at hmem
  simpa using hmem

theorem branch2_hittingSet_card_ge_three {S : Finset Vertex}
    (hS : S ⊆ branch2)
    (hhit : HitsForts S branch2Forts) :
    3 ≤ S.card := by
  by_contra hcard
  have hlt : S.card < 3 := Nat.lt_of_not_ge hcard
  have hmem :
      S ∈ branch2.powerset.filter
        (fun T => T.card < 3 ∧ HitsForts T branch2Forts) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hS, ⟨hlt, hhit⟩⟩
  rw [branch2_no_small_hitting_set] at hmem
  simpa using hmem

theorem branch1_three_le_card_inter {S : Finset Vertex}
    (hhit : HitsForts S branch1Forts) :
    3 ≤ (S ∩ branch1).card := by
  apply branch1_hittingSet_card_ge_three (S := S ∩ branch1)
  · exact Finset.inter_subset_right
  · exact HitsForts.inter_region hhit branch1Forts_subset

theorem branch2_three_le_card_inter {S : Finset Vertex}
    (hhit : HitsForts S branch2Forts) :
    3 ≤ (S ∩ branch2).card := by
  apply branch2_hittingSet_card_ge_three (S := S ∩ branch2)
  · exact Finset.inter_subset_right
  · exact HitsForts.inter_region hhit branch2Forts_subset

/-- The exact twelve size-three hitting sets for branch 1. -/
def branch1Size3HittingSets : List (Finset Vertex) :=
  [([11, 12, 15] : List Vertex).toFinset,
   ([11, 12, 16] : List Vertex).toFinset,
   ([11, 13, 15] : List Vertex).toFinset,
   ([11, 13, 16] : List Vertex).toFinset,
   ([12, 13, 15] : List Vertex).toFinset,
   ([12, 13, 16] : List Vertex).toFinset,
   ([12, 14, 15] : List Vertex).toFinset,
   ([12, 14, 16] : List Vertex).toFinset,
   ([12, 15, 16] : List Vertex).toFinset,
   ([13, 14, 15] : List Vertex).toFinset,
   ([13, 14, 16] : List Vertex).toFinset,
   ([13, 15, 16] : List Vertex).toFinset]

/-- The exact twelve size-three hitting sets for branch 2. -/
def branch2Size3HittingSets : List (Finset Vertex) :=
  [([18, 19, 22] : List Vertex).toFinset,
   ([18, 19, 23] : List Vertex).toFinset,
   ([18, 20, 22] : List Vertex).toFinset,
   ([18, 20, 23] : List Vertex).toFinset,
   ([19, 20, 22] : List Vertex).toFinset,
   ([19, 20, 23] : List Vertex).toFinset,
   ([19, 21, 22] : List Vertex).toFinset,
   ([19, 21, 23] : List Vertex).toFinset,
   ([19, 22, 23] : List Vertex).toFinset,
   ([20, 21, 22] : List Vertex).toFinset,
   ([20, 21, 23] : List Vertex).toFinset,
   ([20, 22, 23] : List Vertex).toFinset]

theorem branch1Size3HittingSets_length :
    branch1Size3HittingSets.length = 12 := by
  decide

theorem branch2Size3HittingSets_length :
    branch2Size3HittingSets.length = 12 := by
  decide

theorem branch1Size3HittingSets_nodup :
    branch1Size3HittingSets.Nodup := by
  decide

theorem branch2Size3HittingSets_nodup :
    branch2Size3HittingSets.Nodup := by
  decide

theorem branch1_size3_hitting_filter_eq :
    branch1.powerset.filter
        (fun S => S.card = 3 ∧ HitsForts S branch1Forts) =
      branch1Size3HittingSets.toFinset := by
  decide

theorem branch2_size3_hitting_filter_eq :
    branch2.powerset.filter
        (fun S => S.card = 3 ∧ HitsForts S branch2Forts) =
      branch2Size3HittingSets.toFinset := by
  decide

theorem branch1_size3_hitting_iff {S : Finset Vertex}
    (hsub : S ⊆ branch1) (hcard : S.card = 3) :
    HitsForts S branch1Forts ↔ S ∈ branch1Size3HittingSets := by
  constructor
  · intro hhit
    have hmem :
        S ∈ branch1.powerset.filter
          (fun T => T.card = 3 ∧ HitsForts T branch1Forts) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hcard, hhit⟩⟩
    rw [branch1_size3_hitting_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    have hfin : S ∈ branch1Size3HittingSets.toFinset := by
      simpa using hmem
    rw [← branch1_size3_hitting_filter_eq] at hfin
    exact (Finset.mem_filter.mp hfin).2.2

theorem branch2_size3_hitting_iff {S : Finset Vertex}
    (hsub : S ⊆ branch2) (hcard : S.card = 3) :
    HitsForts S branch2Forts ↔ S ∈ branch2Size3HittingSets := by
  constructor
  · intro hhit
    have hmem :
        S ∈ branch2.powerset.filter
          (fun T => T.card = 3 ∧ HitsForts T branch2Forts) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hcard, hhit⟩⟩
    rw [branch2_size3_hitting_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    have hfin : S ∈ branch2Size3HittingSets.toFinset := by
      simpa using hmem
    rw [← branch2_size3_hitting_filter_eq] at hfin
    exact (Finset.mem_filter.mp hfin).2.2

theorem zeroForcingSet_branch1_card_ge_three {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S) :
    3 ≤ (S ∩ branch1).card := by
  apply branch1_three_le_card_inter
  rw [hitsForts_iff]
  intro F hF
  exact hZ.intersects_fort
    (branch1Forts_areForts F hF)
    (branch1Forts_nonempty F hF)

theorem zeroForcingSet_branch2_card_ge_three {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S) :
    3 ≤ (S ∩ branch2).card := by
  apply branch2_three_le_card_inter
  rw [hitsForts_iff]
  intro F hF
  exact hZ.intersects_fort
    (branch2Forts_areForts F hF)
    (branch2Forts_nonempty F hF)

/-- The exact twenty-five size-four hitting sets for branch 0. -/
def branch0Size4HittingSets : List (Finset Vertex) :=
  [([3, 4, 5, 8] : List Vertex).toFinset,
   ([3, 4, 5, 9] : List Vertex).toFinset,
   ([3, 4, 6, 8] : List Vertex).toFinset,
   ([3, 4, 6, 9] : List Vertex).toFinset,
   ([3, 5, 6, 8] : List Vertex).toFinset,
   ([3, 5, 6, 9] : List Vertex).toFinset,
   ([3, 5, 7, 8] : List Vertex).toFinset,
   ([3, 5, 7, 9] : List Vertex).toFinset,
   ([3, 5, 8, 9] : List Vertex).toFinset,
   ([3, 6, 7, 8] : List Vertex).toFinset,
   ([3, 6, 7, 9] : List Vertex).toFinset,
   ([3, 6, 8, 9] : List Vertex).toFinset,
   ([4, 5, 6, 8] : List Vertex).toFinset,
   ([4, 5, 6, 9] : List Vertex).toFinset,
   ([4, 5, 7, 8] : List Vertex).toFinset,
   ([4, 5, 7, 9] : List Vertex).toFinset,
   ([4, 5, 8, 9] : List Vertex).toFinset,
   ([4, 6, 7, 8] : List Vertex).toFinset,
   ([4, 6, 7, 9] : List Vertex).toFinset,
   ([4, 6, 8, 9] : List Vertex).toFinset,
   ([5, 6, 7, 8] : List Vertex).toFinset,
   ([5, 6, 7, 9] : List Vertex).toFinset,
   ([5, 6, 8, 9] : List Vertex).toFinset,
   ([5, 7, 8, 9] : List Vertex).toFinset,
   ([6, 7, 8, 9] : List Vertex).toFinset]

/-- The exact twenty-five size-four hitting sets for branch 1. -/
def branch1Size4HittingSets : List (Finset Vertex) :=
  [([10, 11, 12, 15] : List Vertex).toFinset,
   ([10, 11, 12, 16] : List Vertex).toFinset,
   ([10, 11, 13, 15] : List Vertex).toFinset,
   ([10, 11, 13, 16] : List Vertex).toFinset,
   ([10, 12, 13, 15] : List Vertex).toFinset,
   ([10, 12, 13, 16] : List Vertex).toFinset,
   ([10, 12, 14, 15] : List Vertex).toFinset,
   ([10, 12, 14, 16] : List Vertex).toFinset,
   ([10, 12, 15, 16] : List Vertex).toFinset,
   ([10, 13, 14, 15] : List Vertex).toFinset,
   ([10, 13, 14, 16] : List Vertex).toFinset,
   ([10, 13, 15, 16] : List Vertex).toFinset,
   ([11, 12, 13, 15] : List Vertex).toFinset,
   ([11, 12, 13, 16] : List Vertex).toFinset,
   ([11, 12, 14, 15] : List Vertex).toFinset,
   ([11, 12, 14, 16] : List Vertex).toFinset,
   ([11, 12, 15, 16] : List Vertex).toFinset,
   ([11, 13, 14, 15] : List Vertex).toFinset,
   ([11, 13, 14, 16] : List Vertex).toFinset,
   ([11, 13, 15, 16] : List Vertex).toFinset,
   ([12, 13, 14, 15] : List Vertex).toFinset,
   ([12, 13, 14, 16] : List Vertex).toFinset,
   ([12, 13, 15, 16] : List Vertex).toFinset,
   ([12, 14, 15, 16] : List Vertex).toFinset,
   ([13, 14, 15, 16] : List Vertex).toFinset]

/-- The exact twenty-five size-four hitting sets for branch 2. -/
def branch2Size4HittingSets : List (Finset Vertex) :=
  [([17, 18, 19, 22] : List Vertex).toFinset,
   ([17, 18, 19, 23] : List Vertex).toFinset,
   ([17, 18, 20, 22] : List Vertex).toFinset,
   ([17, 18, 20, 23] : List Vertex).toFinset,
   ([17, 19, 20, 22] : List Vertex).toFinset,
   ([17, 19, 20, 23] : List Vertex).toFinset,
   ([17, 19, 21, 22] : List Vertex).toFinset,
   ([17, 19, 21, 23] : List Vertex).toFinset,
   ([17, 19, 22, 23] : List Vertex).toFinset,
   ([17, 20, 21, 22] : List Vertex).toFinset,
   ([17, 20, 21, 23] : List Vertex).toFinset,
   ([17, 20, 22, 23] : List Vertex).toFinset,
   ([18, 19, 20, 22] : List Vertex).toFinset,
   ([18, 19, 20, 23] : List Vertex).toFinset,
   ([18, 19, 21, 22] : List Vertex).toFinset,
   ([18, 19, 21, 23] : List Vertex).toFinset,
   ([18, 19, 22, 23] : List Vertex).toFinset,
   ([18, 20, 21, 22] : List Vertex).toFinset,
   ([18, 20, 21, 23] : List Vertex).toFinset,
   ([18, 20, 22, 23] : List Vertex).toFinset,
   ([19, 20, 21, 22] : List Vertex).toFinset,
   ([19, 20, 21, 23] : List Vertex).toFinset,
   ([19, 20, 22, 23] : List Vertex).toFinset,
   ([19, 21, 22, 23] : List Vertex).toFinset,
   ([20, 21, 22, 23] : List Vertex).toFinset]

theorem branch0Size4HittingSets_length :
    branch0Size4HittingSets.length = 25 := by
  decide

theorem branch1Size4HittingSets_length :
    branch1Size4HittingSets.length = 25 := by
  decide

theorem branch2Size4HittingSets_length :
    branch2Size4HittingSets.length = 25 := by
  decide

theorem branch0Size4HittingSets_nodup :
    branch0Size4HittingSets.Nodup := by
  decide

theorem branch1Size4HittingSets_nodup :
    branch1Size4HittingSets.Nodup := by
  decide

theorem branch2Size4HittingSets_nodup :
    branch2Size4HittingSets.Nodup := by
  decide

theorem branch0_size4_hitting_filter_eq :
    branch0.powerset.filter
        (fun S => S.card = 4 ∧ HitsForts S branch0Forts) =
      branch0Size4HittingSets.toFinset := by
  decide

theorem branch1_size4_hitting_filter_eq :
    branch1.powerset.filter
        (fun S => S.card = 4 ∧ HitsForts S branch1Forts) =
      branch1Size4HittingSets.toFinset := by
  decide

theorem branch2_size4_hitting_filter_eq :
    branch2.powerset.filter
        (fun S => S.card = 4 ∧ HitsForts S branch2Forts) =
      branch2Size4HittingSets.toFinset := by
  decide

theorem branch0_size4_hitting_iff {S : Finset Vertex}
    (hsub : S ⊆ branch0) (hcard : S.card = 4) :
    HitsForts S branch0Forts ↔ S ∈ branch0Size4HittingSets := by
  constructor
  · intro hhit
    have hmem :
        S ∈ branch0.powerset.filter
          (fun T => T.card = 4 ∧ HitsForts T branch0Forts) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hcard, hhit⟩⟩
    rw [branch0_size4_hitting_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    have hfin : S ∈ branch0Size4HittingSets.toFinset := by
      simpa using hmem
    rw [← branch0_size4_hitting_filter_eq] at hfin
    exact (Finset.mem_filter.mp hfin).2.2

theorem branch1_size4_hitting_iff {S : Finset Vertex}
    (hsub : S ⊆ branch1) (hcard : S.card = 4) :
    HitsForts S branch1Forts ↔ S ∈ branch1Size4HittingSets := by
  constructor
  · intro hhit
    have hmem :
        S ∈ branch1.powerset.filter
          (fun T => T.card = 4 ∧ HitsForts T branch1Forts) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hcard, hhit⟩⟩
    rw [branch1_size4_hitting_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    have hfin : S ∈ branch1Size4HittingSets.toFinset := by
      simpa using hmem
    rw [← branch1_size4_hitting_filter_eq] at hfin
    exact (Finset.mem_filter.mp hfin).2.2

theorem branch2_size4_hitting_iff {S : Finset Vertex}
    (hsub : S ⊆ branch2) (hcard : S.card = 4) :
    HitsForts S branch2Forts ↔ S ∈ branch2Size4HittingSets := by
  constructor
  · intro hhit
    have hmem :
        S ∈ branch2.powerset.filter
          (fun T => T.card = 4 ∧ HitsForts T branch2Forts) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, ⟨hcard, hhit⟩⟩
    rw [branch2_size4_hitting_filter_eq] at hmem
    simpa using hmem
  · intro hmem
    have hfin : S ∈ branch2Size4HittingSets.toFinset := by
      simpa using hmem
    rw [← branch2_size4_hitting_filter_eq] at hfin
    exact (Finset.mem_filter.mp hfin).2.2

end FischerZeroForcing
