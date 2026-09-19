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

/-- Eleven vertices: z,a in five K3 copies and a alone in the sixth. -/
def zeroForcingWitness : Finset Vertex :=
  ([4, 5, 7, 8, 11, 12, 14, 15, 18, 19, 22] : List Vertex).toFinset

end FischerZeroForcing
