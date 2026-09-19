import FischerZeroForcing.Graph

/-!
# Zero forcing

A small project-local definition of the standard zero-forcing process.

A blue vertex `u` may force a white vertex `v` when `v` is its unique
white neighbour. A set is zero forcing when a finite sequence of such legal
steps reaches the full vertex set.
-/

namespace FischerZeroForcing

universe u

variable {V : Type u}

/-- `u` can force `v` from the current blue set. -/
def CanForce [DecidableEq V] (G : SimpleGraph V) (blue : Finset V) (u v : V) : Prop :=
  u ∈ blue ∧
    v ∉ blue ∧
    G.Adj u v ∧
    ∀ w : V, w ∉ blue → G.Adj u w → w = v

/-- One legal zero-forcing colour-change step. -/
def ForceStep [DecidableEq V] (G : SimpleGraph V) (blue blue' : Finset V) : Prop :=
  ∃ u v : V, CanForce G blue u v ∧ blue' = insert v blue

/-- A set from which legal forcing steps can colour every vertex blue. -/
def IsZeroForcingSet [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (blue : Finset V) : Prop :=
  Relation.ReflTransGen (ForceStep G) blue Finset.univ

/-- The minimum cardinality of a zero-forcing set. -/
noncomputable def zeroForcingNumber [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ blue : Finset V, blue.card = n ∧ IsZeroForcingSet G blue}

/-- Any explicit zero-forcing set gives the corresponding upper bound. -/
theorem zeroForcingNumber_le_card [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {blue : Finset V} (h : IsZeroForcingSet G blue) :
    zeroForcingNumber G ≤ blue.card := by
  unfold zeroForcingNumber
  exact Nat.sInf_le ⟨blue, rfl, h⟩

end FischerZeroForcing
