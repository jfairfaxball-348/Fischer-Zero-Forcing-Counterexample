import Mathlib

/-!
# Fischer's zero-forcing counterexample: advertised statement

This is the deliberately small Palomar-facing statement surface. The theorem
below contains one intentional `sorry`: Palomar/Comparator compiles this
Challenge separately and checks that the proved declaration in `Solution.lean`
has the same statement and uses only the permitted axioms.

The zero-forcing definitions are repeated here so the Challenge depends only on
allowlisted Mathlib rather than on implementation-heavy project modules.
-/

namespace FischerZeroForcing

universe u

variable {V : Type u}

def CanForce [DecidableEq V] (G : SimpleGraph V) (blue : Finset V) (u v : V) : Prop :=
  u ∈ blue ∧
    v ∉ blue ∧
    G.Adj u v ∧
    ∀ w : V, w ∉ blue → G.Adj u w → w = v

def ForceStep [DecidableEq V] (G : SimpleGraph V) (blue blue' : Finset V) : Prop :=
  ∃ u v : V, CanForce G blue u v ∧ blue' = insert v blue

def IsZeroForcingSet [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (blue : Finset V) : Prop :=
  Relation.ReflTransGen (ForceStep G) blue Finset.univ

noncomputable def zeroForcingNumber [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ blue : Finset V, blue.card = n ∧ IsZeroForcingSet G blue}

/--
There exists a connected simple graph on 24 vertices of maximum degree at most
3 with independence number 9 and zero-forcing number 11.
-/
theorem main_result :
    ∃ G : SimpleGraph (Fin 24),
      G.Connected ∧
      (∀ v : Fin 24, (G.neighborSet v).ncard ≤ 3) ∧
      G.indepNum = 9 ∧
      zeroForcingNumber G = 11 := by
  sorry

end FischerZeroForcing
