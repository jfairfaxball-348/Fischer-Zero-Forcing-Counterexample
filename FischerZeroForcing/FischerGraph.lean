import FischerZeroForcing.ZeroForcing

/-!
# Fischer's 24-vertex graph H

The vertex numbering is the graph6 order from arXiv:2607.23664v1 and is also
compatible with the paper's construction H = G(K3):

* c0,c1,c2 = 0,1,2
* branch 0: r0=3 and triangles (z,a,b)=(4,5,6),(7,8,9)
* branch 1: r1=10 and triangles (z,a,b)=(11,12,13),(14,15,16)
* branch 2: r2=17 and triangles (z,a,b)=(18,19,20),(21,22,23)

The list below is independently cross-checked against the published graph6
string by verification/check_fischer_h.py.
-/

namespace FischerZeroForcing

/-- The 30 undirected edges, written once each with the smaller endpoint first. -/
def fischerEdges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (1, 2),
   (0, 3),
   (3, 4), (4, 5), (4, 6), (5, 6),
   (3, 7), (7, 8), (7, 9), (8, 9),
   (1, 10),
   (10, 11), (11, 12), (11, 13), (12, 13),
   (10, 14), (14, 15), (14, 16), (15, 16),
   (2, 17),
   (17, 18), (18, 19), (18, 20), (19, 20),
   (17, 21), (21, 22), (21, 23), (22, 23)]

private def fischerEdgeRel (u v : Vertex) : Prop :=
  (u.val, v.val) ∈ fischerEdges

/-- Fischer's explicit 24-vertex subcubic graph H. -/
def fischerGraph : SimpleGraph Vertex :=
  SimpleGraph.fromRel fischerEdgeRel

end FischerZeroForcing
