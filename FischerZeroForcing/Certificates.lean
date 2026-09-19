import FischerZeroForcing.FischerGraph
import FischerZeroForcing.Independence

/-!
# Explicit source witnesses

These finite sets are the graph6-labelled versions of the witness patterns
described in Fischer's note. The independent-set witness and the explicit
zero-forcing sequence are kernel-checked below.
-/

namespace FischerZeroForcing

/-- Nine vertices: each branch centre plus one non-attachment vertex from each K3 copy. -/
def independentWitness : Finset Vertex :=
  ([3, 5, 8, 10, 12, 15, 17, 19, 22] : List Vertex).toFinset

/-- The explicit independence witness has nine vertices. -/
theorem independentWitness_card : independentWitness.card = 9 := by
  native_decide

/-- Fischer's explicit nine-vertex witness is an independent set. -/
theorem independentWitness_isIndependent :
    fischerGraph.IsIndepSet independentWitness := by
  native_decide

/-- The explicit witness gives the lower bound α(H) ≥ 9. -/
theorem nine_le_fischerGraph_indepNum : 9 ≤ fischerGraph.indepNum := by
  rw [← independentWitness_card]
  exact independentWitness_isIndependent.card_le_indepNum

/--
A nine-class clique-cover certificate for Fischer's graph.

The classes are
`{0,3}`, `{1,10}`, `{2,17}`, and the six attached triangles.
Thus every independent set can contain at most one vertex from each class.
-/
private def independenceCliqueCoverClass : Vertex → Fin 9 :=
  ![0, 1, 2, 0, 3, 3, 3, 4, 4, 4, 1, 5, 5, 5, 6, 6, 6, 2, 7, 7, 7, 8, 8, 8]

/--
Distinct vertices in the same clique-cover class are adjacent.

This is the finite certificate check: only 24 × 24 ordered vertex pairs are
considered, and adjacency is checked against the explicit Fischer edge list.
-/
private theorem independenceCliqueCoverClass_eq_implies_adj :
    ∀ u v : Vertex,
      independenceCliqueCoverClass u = independenceCliqueCoverClass v →
      u ≠ v →
      fischerGraph.Adj u v := by
  native_decide

/-- Every independent set in Fischer's graph has at most nine vertices. -/
theorem fischerGraph_independentSet_card_le (S : Finset Vertex)
    (hS : fischerGraph.IsIndepSet S) : S.card ≤ 9 := by
  have hinj : Function.Injective
      (fun v : {v // v ∈ S} => independenceCliqueCoverClass v.1) := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    exact (hS (by simpa using u.2) (by simpa using v.2) hne)
      (independenceCliqueCoverClass_eq_implies_adj u.1 v.1 huv hne)
  simpa using
    (Fintype.card_le_of_injective
      (fun v : {v // v ∈ S} => independenceCliqueCoverClass v.1) hinj)

/-- Fischer's graph has independence number at most nine. -/
theorem fischerGraph_indepNum_le : fischerGraph.indepNum ≤ 9 := by
  obtain ⟨S, hS⟩ := (SimpleGraph.maximumIndepSet_exists (G := fischerGraph))
  rw [← SimpleGraph.maximumIndepSet_card_eq_indepNum S hS]
  exact fischerGraph_independentSet_card_le S hS.isIndepSet

/-- Fischer's explicit graph has independence number exactly nine. -/
theorem fischerGraph_indepNum : fischerGraph.indepNum = 9 := by
  exact le_antisymm fischerGraph_indepNum_le nine_le_fischerGraph_indepNum

/-- Eleven vertices: z,a in five K3 copies and a alone in the sixth. -/
def zeroForcingWitness : Finset Vertex :=
  ([4, 5, 7, 8, 11, 12, 14, 15, 18, 19, 22] : List Vertex).toFinset

/-- The explicit zero-forcing witness has eleven vertices. -/
theorem zeroForcingWitness_card : zeroForcingWitness.card = 11 := by
  native_decide

/-!
The following intermediate blue sets expose Fischer's 13-force certificate.
Each set is obtained by inserting exactly the newly forced vertex from the
preceding step.
-/

private def zeroForcingBlue1 : Finset Vertex := insert 6 zeroForcingWitness
private def zeroForcingBlue2 : Finset Vertex := insert 3 zeroForcingBlue1
private def zeroForcingBlue3 : Finset Vertex := insert 0 zeroForcingBlue2
private def zeroForcingBlue4 : Finset Vertex := insert 9 zeroForcingBlue3
private def zeroForcingBlue5 : Finset Vertex := insert 13 zeroForcingBlue4
private def zeroForcingBlue6 : Finset Vertex := insert 10 zeroForcingBlue5
private def zeroForcingBlue7 : Finset Vertex := insert 1 zeroForcingBlue6
private def zeroForcingBlue8 : Finset Vertex := insert 2 zeroForcingBlue7
private def zeroForcingBlue9 : Finset Vertex := insert 17 zeroForcingBlue8
private def zeroForcingBlue10 : Finset Vertex := insert 16 zeroForcingBlue9
private def zeroForcingBlue11 : Finset Vertex := insert 21 zeroForcingBlue10
private def zeroForcingBlue12 : Finset Vertex := insert 20 zeroForcingBlue11
private def zeroForcingBlue13 : Finset Vertex := insert 23 zeroForcingBlue12

private theorem zeroForcingStep_5_6 :
    ForceStep fischerGraph zeroForcingWitness zeroForcingBlue1 := by
  refine ⟨5, 6, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_4_3 :
    ForceStep fischerGraph zeroForcingBlue1 zeroForcingBlue2 := by
  refine ⟨4, 3, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_3_0 :
    ForceStep fischerGraph zeroForcingBlue2 zeroForcingBlue3 := by
  refine ⟨3, 0, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_7_9 :
    ForceStep fischerGraph zeroForcingBlue3 zeroForcingBlue4 := by
  refine ⟨7, 9, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_12_13 :
    ForceStep fischerGraph zeroForcingBlue4 zeroForcingBlue5 := by
  refine ⟨12, 13, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_11_10 :
    ForceStep fischerGraph zeroForcingBlue5 zeroForcingBlue6 := by
  refine ⟨11, 10, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_10_1 :
    ForceStep fischerGraph zeroForcingBlue6 zeroForcingBlue7 := by
  refine ⟨10, 1, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_0_2 :
    ForceStep fischerGraph zeroForcingBlue7 zeroForcingBlue8 := by
  refine ⟨0, 2, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_2_17 :
    ForceStep fischerGraph zeroForcingBlue8 zeroForcingBlue9 := by
  refine ⟨2, 17, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_14_16 :
    ForceStep fischerGraph zeroForcingBlue9 zeroForcingBlue10 := by
  refine ⟨14, 16, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_17_21 :
    ForceStep fischerGraph zeroForcingBlue10 zeroForcingBlue11 := by
  refine ⟨17, 21, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_18_20 :
    ForceStep fischerGraph zeroForcingBlue11 zeroForcingBlue12 := by
  refine ⟨18, 20, ?_, rfl⟩
  native_decide

private theorem zeroForcingStep_21_23 :
    ForceStep fischerGraph zeroForcingBlue12 zeroForcingBlue13 := by
  refine ⟨21, 23, ?_, rfl⟩
  native_decide

private theorem zeroForcingBlue13_eq_univ :
    zeroForcingBlue13 = (Finset.univ : Finset Vertex) := by
  native_decide

/--
Fischer's explicit eleven-vertex witness zero-forces every vertex.

The proof is exactly the source/checker sequence
5→6, 4→3, 3→0, 7→9, 12→13, 11→10, 10→1,
0→2, 2→17, 14→16, 17→21, 18→20, 21→23.
-/
theorem zeroForcingWitness_isZeroForcing :
    IsZeroForcingSet fischerGraph zeroForcingWitness := by
  have h0 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingWitness :=
    Relation.ReflTransGen.refl
  have h1 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue1 :=
    Relation.ReflTransGen.tail h0 zeroForcingStep_5_6
  have h2 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue2 :=
    Relation.ReflTransGen.tail h1 zeroForcingStep_4_3
  have h3 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue3 :=
    Relation.ReflTransGen.tail h2 zeroForcingStep_3_0
  have h4 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue4 :=
    Relation.ReflTransGen.tail h3 zeroForcingStep_7_9
  have h5 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue5 :=
    Relation.ReflTransGen.tail h4 zeroForcingStep_12_13
  have h6 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue6 :=
    Relation.ReflTransGen.tail h5 zeroForcingStep_11_10
  have h7 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue7 :=
    Relation.ReflTransGen.tail h6 zeroForcingStep_10_1
  have h8 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue8 :=
    Relation.ReflTransGen.tail h7 zeroForcingStep_0_2
  have h9 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue9 :=
    Relation.ReflTransGen.tail h8 zeroForcingStep_2_17
  have h10 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue10 :=
    Relation.ReflTransGen.tail h9 zeroForcingStep_14_16
  have h11 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue11 :=
    Relation.ReflTransGen.tail h10 zeroForcingStep_17_21
  have h12 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue12 :=
    Relation.ReflTransGen.tail h11 zeroForcingStep_18_20
  have h13 : Relation.ReflTransGen (ForceStep fischerGraph)
      zeroForcingWitness zeroForcingBlue13 :=
    Relation.ReflTransGen.tail h12 zeroForcingStep_21_23
  rw [← zeroForcingBlue13_eq_univ]
  exact h13

/-- The explicit witness gives the formal upper bound Z(H) ≤ 11. -/
theorem fischerGraph_zeroForcingNumber_le :
    zeroForcingNumber fischerGraph ≤ 11 := by
  rw [← zeroForcingWitness_card]
  exact zeroForcingNumber_le_card fischerGraph zeroForcingWitness_isZeroForcing

end FischerZeroForcing
