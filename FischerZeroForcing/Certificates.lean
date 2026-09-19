import FischerZeroForcing.FischerGraph
import FischerZeroForcing.Independence

/-!
# Explicit source witnesses

These finite sets are the graph6-labelled versions of the witness patterns
described in Fischer's note. The independent-set witness is kernel-checked
below; the zero-forcing witness remains data for later formalisation.
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
  obtain ⟨S, hS⟩ := (maximumIndepSet_exists (G := fischerGraph))
  rw [← maximumIndepSet_card_eq_indepNum S hS]
  exact fischerGraph_independentSet_card_le S hS.isIndepSet

/-- Fischer's explicit graph has independence number exactly nine. -/
theorem fischerGraph_indepNum : fischerGraph.indepNum = 9 := by
  exact le_antisymm fischerGraph_indepNum_le nine_le_fischerGraph_indepNum

/-- Eleven vertices: z,a in five K3 copies and a alone in the sixth. -/
def zeroForcingWitness : Finset Vertex :=
  ([4, 5, 7, 8, 11, 12, 14, 15, 18, 19, 22] : List Vertex).toFinset

end FischerZeroForcing
