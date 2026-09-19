import FischerZeroForcing.BranchCertificates

/-!
# Fischer lower-bound candidate reduction

This file constructs exactly the 17,712 candidates appearing in Fischer's
fort-based lower-bound reduction.  It does not check whether those candidates
zero-force the graph; that computation is deliberately left to the next stage.
-/

namespace FischerZeroForcing

/-- The three centre vertices joining the branches. -/
def centreVertices : List Vertex := [0, 1, 2]

/-- The centre triangle as a finite vertex set. -/
def centreTriangle : Finset Vertex := centreVertices.toFinset

theorem centreTriangle_card : centreTriangle.card = 3 := by
  native_decide

/-- Class I: 3+3+3 branch hitting sets, hence size 9. -/
def lowerBoundCandidateClassI : List (Finset Vertex) :=
  branch0Size3HittingSets.flatMap fun A =>
    branch1Size3HittingSets.flatMap fun B =>
      branch2Size3HittingSets.map fun C =>
        A ∪ B ∪ C

/-- Class II: 3+3+3 branch hitting sets plus one centre vertex, hence size 10. -/
def lowerBoundCandidateClassII : List (Finset Vertex) :=
  branch0Size3HittingSets.flatMap fun A =>
    branch1Size3HittingSets.flatMap fun B =>
      branch2Size3HittingSets.flatMap fun C =>
        centreVertices.map fun t =>
          A ∪ B ∪ C ∪ {t}

/-- Class III: one branch contributes four vertices and the other two contribute three. -/
def lowerBoundCandidateClassIII : List (Finset Vertex) :=
  (branch0Size4HittingSets.flatMap fun A =>
    branch1Size3HittingSets.flatMap fun B =>
      branch2Size3HittingSets.map fun C =>
        A ∪ B ∪ C) ++
  (branch0Size3HittingSets.flatMap fun A =>
    branch1Size4HittingSets.flatMap fun B =>
      branch2Size3HittingSets.map fun C =>
        A ∪ B ∪ C) ++
  (branch0Size3HittingSets.flatMap fun A =>
    branch1Size3HittingSets.flatMap fun B =>
      branch2Size4HittingSets.map fun C =>
        A ∪ B ∪ C)

/-- The complete finite family used for the size-at-most-ten lower-bound reduction. -/
def lowerBoundCandidates : List (Finset Vertex) :=
  lowerBoundCandidateClassI ++
  lowerBoundCandidateClassII ++
  lowerBoundCandidateClassIII

theorem lowerBoundCandidateClassI_length :
    lowerBoundCandidateClassI.length = 1728 := by
  native_decide

theorem lowerBoundCandidateClassII_length :
    lowerBoundCandidateClassII.length = 5184 := by
  native_decide

theorem lowerBoundCandidateClassIII_length :
    lowerBoundCandidateClassIII.length = 10800 := by
  native_decide

/-- The source reduction generates exactly 17,712 candidate occurrences. -/
theorem lowerBoundCandidates_length :
    lowerBoundCandidates.length = 17712 := by
  native_decide

/-- The 17,712 generated candidate sets are pairwise distinct. -/
theorem lowerBoundCandidates_nodup :
    lowerBoundCandidates.Nodup := by
  native_decide

private theorem candidateClassI_mem
    {A B C : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hB : B ∈ branch1Size3HittingSets)
    (hC : C ∈ branch2Size3HittingSets) :
    A ∪ B ∪ C ∈ lowerBoundCandidateClassI := by
  simp [lowerBoundCandidateClassI, hA, hB, hC]

private theorem candidateClassII_mem
    {A B C : Finset Vertex} {t : Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hB : B ∈ branch1Size3HittingSets)
    (hC : C ∈ branch2Size3HittingSets)
    (ht : t ∈ centreVertices) :
    A ∪ B ∪ C ∪ {t} ∈ lowerBoundCandidateClassII := by
  simp [lowerBoundCandidateClassII, hA, hB, hC, ht]

private theorem candidateClassIII0_mem
    {A B C : Finset Vertex}
    (hA : A ∈ branch0Size4HittingSets)
    (hB : B ∈ branch1Size3HittingSets)
    (hC : C ∈ branch2Size3HittingSets) :
    A ∪ B ∪ C ∈ lowerBoundCandidateClassIII := by
  simp [lowerBoundCandidateClassIII, hA, hB, hC]

private theorem candidateClassIII1_mem
    {A B C : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hB : B ∈ branch1Size4HittingSets)
    (hC : C ∈ branch2Size3HittingSets) :
    A ∪ B ∪ C ∈ lowerBoundCandidateClassIII := by
  simp [lowerBoundCandidateClassIII, hA, hB, hC]

private theorem candidateClassIII2_mem
    {A B C : Finset Vertex}
    (hA : A ∈ branch0Size3HittingSets)
    (hB : B ∈ branch1Size3HittingSets)
    (hC : C ∈ branch2Size4HittingSets) :
    A ∪ B ∪ C ∈ lowerBoundCandidateClassIII := by
  simp [lowerBoundCandidateClassIII, hA, hB, hC]

private theorem branch0_branch1_disjoint : Disjoint branch0 branch1 := by
  native_decide

private theorem branch0_branch2_disjoint : Disjoint branch0 branch2 := by
  native_decide

private theorem branch1_branch2_disjoint : Disjoint branch1 branch2 := by
  native_decide

private theorem branch0_centre_disjoint : Disjoint branch0 centreTriangle := by
  native_decide

private theorem branch1_centre_disjoint : Disjoint branch1 centreTriangle := by
  native_decide

private theorem branch2_centre_disjoint : Disjoint branch2 centreTriangle := by
  native_decide

/-- The centre and the three branches partition all 24 vertices. -/
theorem centre_branches_partition :
    centreTriangle ∪ branch0 ∪ branch1 ∪ branch2 =
      (Finset.univ : Finset Vertex) := by
  native_decide

private theorem restrict_disjoint {S A B : Finset Vertex}
    (h : Disjoint A B) :
    Disjoint (S ∩ A) (S ∩ B) := by
  exact h.mono Finset.inter_subset_right Finset.inter_subset_right

private theorem zeroForcing_hits_branch0 {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S) :
    HitsForts (S ∩ branch0) branch0Forts := by
  apply HitsForts.inter_region (region := branch0)
  · rw [hitsForts_iff]
    intro F hF
    exact hZ.intersects_fort
      (branch0Forts_areForts F hF)
      (branch0Forts_nonempty F hF)
  · exact branch0Forts_subset

private theorem zeroForcing_hits_branch1 {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S) :
    HitsForts (S ∩ branch1) branch1Forts := by
  apply HitsForts.inter_region (region := branch1)
  · rw [hitsForts_iff]
    intro F hF
    exact hZ.intersects_fort
      (branch1Forts_areForts F hF)
      (branch1Forts_nonempty F hF)
  · exact branch1Forts_subset

private theorem zeroForcing_hits_branch2 {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S) :
    HitsForts (S ∩ branch2) branch2Forts := by
  apply HitsForts.inter_region (region := branch2)
  · rw [hitsForts_iff]
    intro F hF
    exact hZ.intersects_fort
      (branch2Forts_areForts F hF)
      (branch2Forts_nonempty F hF)
  · exact branch2Forts_subset

private theorem set_partition (S : Finset Vertex) :
    S =
      (((S ∩ branch0) ∪ (S ∩ branch1)) ∪ (S ∩ branch2)) ∪
        (S ∩ centreTriangle) := by
  ext v
  fin_cases v <;>
    simp [branch0, branch1, branch2, centreTriangle, centreVertices]

private theorem three_regions_disjoint_from_fourth
    {S A B C D : Finset Vertex}
    (hAD : Disjoint A D)
    (hBD : Disjoint B D)
    (hCD : Disjoint C D) :
    Disjoint (((S ∩ A) ∪ (S ∩ B)) ∪ (S ∩ C)) (S ∩ D) := by
  rw [Finset.disjoint_left]
  intro x hx hxd
  rcases Finset.mem_union.mp hx with hxAB | hxC
  · rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact Finset.disjoint_left.mp (restrict_disjoint (S := S) hAD) hxA hxd
    · exact Finset.disjoint_left.mp (restrict_disjoint (S := S) hBD) hxB hxd
  · exact Finset.disjoint_left.mp (restrict_disjoint (S := S) hCD) hxC hxd

private theorem first_two_disjoint_third
    {S A B C : Finset Vertex}
    (hAC : Disjoint A C)
    (hBC : Disjoint B C) :
    Disjoint ((S ∩ A) ∪ (S ∩ B)) (S ∩ C) := by
  rw [Finset.disjoint_left]
  intro x hx hxc
  rcases Finset.mem_union.mp hx with hxA | hxB
  · exact Finset.disjoint_left.mp (restrict_disjoint (S := S) hAC) hxA hxc
  · exact Finset.disjoint_left.mp (restrict_disjoint (S := S) hBC) hxB hxc

private theorem card_partition (S : Finset Vertex) :
    S.card =
      (((S ∩ branch0).card + (S ∩ branch1).card) +
        (S ∩ branch2).card) +
        (S ∩ centreTriangle).card := by
  have h01 : Disjoint (S ∩ branch0) (S ∩ branch1) :=
    restrict_disjoint branch0_branch1_disjoint
  have h012 :
      Disjoint ((S ∩ branch0) ∪ (S ∩ branch1)) (S ∩ branch2) :=
    first_two_disjoint_third branch0_branch2_disjoint branch1_branch2_disjoint
  have h012c :
      Disjoint
        (((S ∩ branch0) ∪ (S ∩ branch1)) ∪ (S ∩ branch2))
        (S ∩ centreTriangle) :=
    three_regions_disjoint_from_fourth
      branch0_centre_disjoint branch1_centre_disjoint branch2_centre_disjoint
  rw [set_partition S,
    Finset.card_union_of_disjoint h012c,
    Finset.card_union_of_disjoint h012,
    Finset.card_union_of_disjoint h01]

/--
Every hypothetical zero-forcing set of cardinality at most ten is one of the
17,712 generated candidates.
-/
theorem zeroForcingSet_card_le_ten_mem_candidates
    {S : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph S)
    (hcard : S.card ≤ 10) :
    S ∈ lowerBoundCandidates := by
  have h0 : 3 ≤ (S ∩ branch0).card :=
    zeroForcingSet_branch0_card_ge_three hZ
  have h1 : 3 ≤ (S ∩ branch1).card :=
    zeroForcingSet_branch1_card_ge_three hZ
  have h2 : 3 ≤ (S ∩ branch2).card :=
    zeroForcingSet_branch2_card_ge_three hZ
  have hsum := card_partition S

  have hhit0 := zeroForcing_hits_branch0 hZ
  have hhit1 := zeroForcing_hits_branch1 hZ
  have hhit2 := zeroForcing_hits_branch2 hZ

  by_cases h4_0 : (S ∩ branch0).card = 4
  · have h3_1 : (S ∩ branch1).card = 3 := by omega
    have h3_2 : (S ∩ branch2).card = 3 := by omega
    have hc0 : (S ∩ centreTriangle).card = 0 := by omega
    have hA :
        S ∩ branch0 ∈ branch0Size4HittingSets :=
      (branch0_size4_hitting_iff Finset.inter_subset_right h4_0).mp hhit0
    have hB :
        S ∩ branch1 ∈ branch1Size3HittingSets :=
      (branch1_size3_hitting_iff Finset.inter_subset_right h3_1).mp hhit1
    have hC :
        S ∩ branch2 ∈ branch2Size3HittingSets :=
      (branch2_size3_hitting_iff Finset.inter_subset_right h3_2).mp hhit2
    have hcentre : S ∩ centreTriangle = ∅ :=
      Finset.card_eq_zero.mp hc0
    have hmem :
        (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) ∈
          lowerBoundCandidateClassIII :=
      candidateClassIII0_mem hA hB hC
    have hS :
        S = (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) := by
      rw [set_partition S, hcentre]
      simp
    rw [hS]
    simp [lowerBoundCandidates, hmem]

  · have h3_0 : (S ∩ branch0).card = 3 := by omega
    by_cases h4_1 : (S ∩ branch1).card = 4
    · have h3_2 : (S ∩ branch2).card = 3 := by omega
      have hc0 : (S ∩ centreTriangle).card = 0 := by omega
      have hA :
          S ∩ branch0 ∈ branch0Size3HittingSets :=
        (branch0_size3_hitting_iff Finset.inter_subset_right h3_0).mp hhit0
      have hB :
          S ∩ branch1 ∈ branch1Size4HittingSets :=
        (branch1_size4_hitting_iff Finset.inter_subset_right h4_1).mp hhit1
      have hC :
          S ∩ branch2 ∈ branch2Size3HittingSets :=
        (branch2_size3_hitting_iff Finset.inter_subset_right h3_2).mp hhit2
      have hcentre : S ∩ centreTriangle = ∅ :=
        Finset.card_eq_zero.mp hc0
      have hmem :
          (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) ∈
            lowerBoundCandidateClassIII :=
        candidateClassIII1_mem hA hB hC
      have hS :
          S = (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) := by
        rw [set_partition S, hcentre]
        simp
      rw [hS]
      simp [lowerBoundCandidates, hmem]

    · have h3_1 : (S ∩ branch1).card = 3 := by omega
      by_cases h4_2 : (S ∩ branch2).card = 4
      · have hc0 : (S ∩ centreTriangle).card = 0 := by omega
        have hA :
            S ∩ branch0 ∈ branch0Size3HittingSets :=
          (branch0_size3_hitting_iff Finset.inter_subset_right h3_0).mp hhit0
        have hB :
            S ∩ branch1 ∈ branch1Size3HittingSets :=
          (branch1_size3_hitting_iff Finset.inter_subset_right h3_1).mp hhit1
        have hC :
            S ∩ branch2 ∈ branch2Size4HittingSets :=
          (branch2_size4_hitting_iff Finset.inter_subset_right h4_2).mp hhit2
        have hcentre : S ∩ centreTriangle = ∅ :=
          Finset.card_eq_zero.mp hc0
        have hmem :
            (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) ∈
              lowerBoundCandidateClassIII :=
          candidateClassIII2_mem hA hB hC
        have hS :
            S = (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) := by
          rw [set_partition S, hcentre]
          simp
        rw [hS]
        simp [lowerBoundCandidates, hmem]

      · have h3_2 : (S ∩ branch2).card = 3 := by omega
        have hA :
            S ∩ branch0 ∈ branch0Size3HittingSets :=
          (branch0_size3_hitting_iff Finset.inter_subset_right h3_0).mp hhit0
        have hB :
            S ∩ branch1 ∈ branch1Size3HittingSets :=
          (branch1_size3_hitting_iff Finset.inter_subset_right h3_1).mp hhit1
        have hC :
            S ∩ branch2 ∈ branch2Size3HittingSets :=
          (branch2_size3_hitting_iff Finset.inter_subset_right h3_2).mp hhit2
        have hc : (S ∩ centreTriangle).card = 0 ∨
            (S ∩ centreTriangle).card = 1 := by
          omega
        rcases hc with hc0 | hc1
        · have hcentre : S ∩ centreTriangle = ∅ :=
            Finset.card_eq_zero.mp hc0
          have hmem :
              (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) ∈
                lowerBoundCandidateClassI :=
            candidateClassI_mem hA hB hC
          have hS :
              S = (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) := by
            rw [set_partition S, hcentre]
            simp
          rw [hS]
          simp [lowerBoundCandidates, hmem]
        · rcases Finset.card_eq_one.mp hc1 with ⟨t, hcentre⟩
          have htInter : t ∈ S ∩ centreTriangle := by
            rw [hcentre]
            simp
          have htCentre : t ∈ centreTriangle :=
            (Finset.mem_inter.mp htInter).2
          have htList : t ∈ centreVertices := by
            simpa [centreTriangle] using htCentre
          have hmem :
              (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) ∪ {t} ∈
                lowerBoundCandidateClassII :=
            candidateClassII_mem hA hB hC htList
          have hS :
              S =
                (S ∩ branch0) ∪ (S ∩ branch1) ∪ (S ∩ branch2) ∪ {t} := by
            rw [set_partition S, hcentre]
          rw [hS]
          simp [lowerBoundCandidates, hmem]

end FischerZeroForcing
