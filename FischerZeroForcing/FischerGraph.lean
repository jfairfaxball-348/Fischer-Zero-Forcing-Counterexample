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

/--
Audit-facing characterization of adjacency: the graph is exactly the
symmetrized, loop-free relation induced by the explicit edge list above.
-/
@[simp] theorem fischerGraph_adj_iff (u v : Vertex) :
    fischerGraph.Adj u v ↔
      u ≠ v ∧
        ((u.val, v.val) ∈ fischerEdges ∨ (v.val, u.val) ∈ fischerEdges) := by
  rfl

instance fischerGraphDecidableAdj : DecidableRel fischerGraph.Adj := by
  intro u v
  change Decidable
    (u ≠ v ∧
      ((u.val, v.val) ∈ fischerEdges ∨ (v.val, u.val) ∈ fischerEdges))
  infer_instance

/-- The human-readable edge list contains exactly 30 entries. -/
theorem fischerEdges_length : fischerEdges.length = 30 := by
  native_decide

/--
Fischer's graph is connected.

The proof exposes a spanning tree rooted at vertex 0. Each tree edge is checked
directly against the explicit graph relation, then reachability is propagated
along those 23 edges.
-/
theorem fischerGraph_connected : fischerGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩

  have r0 : fischerGraph.Reachable 0 0 := SimpleGraph.Reachable.rfl
  have r1 : fischerGraph.Reachable 0 1 :=
    (show fischerGraph.Adj 0 1 by decide).reachable
  have r2 : fischerGraph.Reachable 0 2 :=
    (show fischerGraph.Adj 0 2 by decide).reachable
  have r3 : fischerGraph.Reachable 0 3 :=
    (show fischerGraph.Adj 0 3 by decide).reachable

  have r4 : fischerGraph.Reachable 0 4 :=
    r3.trans (show fischerGraph.Adj 3 4 by decide).reachable
  have r5 : fischerGraph.Reachable 0 5 :=
    r4.trans (show fischerGraph.Adj 4 5 by decide).reachable
  have r6 : fischerGraph.Reachable 0 6 :=
    r4.trans (show fischerGraph.Adj 4 6 by decide).reachable
  have r7 : fischerGraph.Reachable 0 7 :=
    r3.trans (show fischerGraph.Adj 3 7 by decide).reachable
  have r8 : fischerGraph.Reachable 0 8 :=
    r7.trans (show fischerGraph.Adj 7 8 by decide).reachable
  have r9 : fischerGraph.Reachable 0 9 :=
    r7.trans (show fischerGraph.Adj 7 9 by decide).reachable

  have r10 : fischerGraph.Reachable 0 10 :=
    r1.trans (show fischerGraph.Adj 1 10 by decide).reachable
  have r11 : fischerGraph.Reachable 0 11 :=
    r10.trans (show fischerGraph.Adj 10 11 by decide).reachable
  have r12 : fischerGraph.Reachable 0 12 :=
    r11.trans (show fischerGraph.Adj 11 12 by decide).reachable
  have r13 : fischerGraph.Reachable 0 13 :=
    r11.trans (show fischerGraph.Adj 11 13 by decide).reachable
  have r14 : fischerGraph.Reachable 0 14 :=
    r10.trans (show fischerGraph.Adj 10 14 by decide).reachable
  have r15 : fischerGraph.Reachable 0 15 :=
    r14.trans (show fischerGraph.Adj 14 15 by decide).reachable
  have r16 : fischerGraph.Reachable 0 16 :=
    r14.trans (show fischerGraph.Adj 14 16 by decide).reachable

  have r17 : fischerGraph.Reachable 0 17 :=
    r2.trans (show fischerGraph.Adj 2 17 by decide).reachable
  have r18 : fischerGraph.Reachable 0 18 :=
    r17.trans (show fischerGraph.Adj 17 18 by decide).reachable
  have r19 : fischerGraph.Reachable 0 19 :=
    r18.trans (show fischerGraph.Adj 18 19 by decide).reachable
  have r20 : fischerGraph.Reachable 0 20 :=
    r18.trans (show fischerGraph.Adj 18 20 by decide).reachable
  have r21 : fischerGraph.Reachable 0 21 :=
    r17.trans (show fischerGraph.Adj 17 21 by decide).reachable
  have r22 : fischerGraph.Reachable 0 22 :=
    r21.trans (show fischerGraph.Adj 21 22 by decide).reachable
  have r23 : fischerGraph.Reachable 0 23 :=
    r21.trans (show fischerGraph.Adj 21 23 by decide).reachable

  intro v
  fin_cases v <;> assumption

/-- Every vertex of Fischer's graph has at most three neighbours. -/
theorem fischerGraph_subcubic :
    ∀ v : Vertex, (fischerGraph.neighborSet v).ncard ≤ 3 := by
  intro v
  rw [Set.ncard_eq_toFinset_card']
  fin_cases v <;> native_decide

end FischerZeroForcing
