import Mathlib

/-!
# Fischer's zero-forcing counterexample: advertised statement

This is the intended small Palomar-facing surface. During bootstrap the theorem
below deliberately contains `sorry`; the repository status is therefore NOT
YET FORMALLY VERIFIED.

The local zero-forcing definitions are repeated here so that the eventual
Challenge module can remain auditable and depend only on allowlisted Mathlib
rather than on implementation-heavy project modules.
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
