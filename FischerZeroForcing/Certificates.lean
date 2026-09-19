import FischerZeroForcing.FischerGraph
import FischerZeroForcing.Independence

/-!
# Explicit source witnesses

These finite sets are the graph6-labelled versions of the witness patterns
described in Fischer's note. Their mathematical properties are not yet claimed
as Lean theorems in this bootstrap commit.
-/

namespace FischerZeroForcing

/-- Nine vertices: each branch centre plus one non-attachment vertex from each K3 copy. -/
def independentWitness : Finset Vertex :=
  ([3, 5, 8, 10, 12, 15, 17, 19, 22] : List Vertex).toFinset

/-- Eleven vertices: z,a in five K3 copies and a alone in the sixth. -/
def zeroForcingWitness : Finset Vertex :=
  ([4, 5, 7, 8, 11, 12, 14, 15, 18, 19, 22] : List Vertex).toFinset

end FischerZeroForcing
