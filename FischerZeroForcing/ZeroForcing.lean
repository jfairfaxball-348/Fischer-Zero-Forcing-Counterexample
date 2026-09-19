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

/--
A fort is a set of vertices such that no vertex outside the set has exactly
one neighbour in it.

The formulation below is equivalent to the usual cardinality condition:
whenever an outside vertex is adjacent to a vertex `v` of the fort, it has a
second, distinct neighbour `w` in the fort. This form matches `CanForce`
directly and remains suitable for finite certificate checking.
-/
def IsFort [DecidableEq V] (G : SimpleGraph V) (F : Finset V) : Prop :=
  ∀ u : V, u ∉ F →
    ∀ v : V, v ∈ F → G.Adj u v →
      ∃ w : V, w ∈ F ∧ G.Adj u w ∧ w ≠ v

/--
A legal force cannot enter a fort that is completely white.

If `blue` is disjoint from `F`, the forcing vertex `u` lies outside `F`.
Were the newly forced vertex `v` in `F`, the fort property would provide a
second neighbour `w ∈ F` of `u`. Since the whole fort is white, `w` is a
white neighbour of `u`, contradicting the uniqueness clause in `CanForce`.
-/
theorem ForceStep.disjoint_fort_preserved [DecidableEq V]
    {G : SimpleGraph V} {blue blue' F : Finset V}
    (hF : IsFort G F)
    (hdisj : Disjoint blue F)
    (hstep : ForceStep G blue blue') :
    Disjoint blue' F := by
  rw [Finset.disjoint_left] at hdisj ⊢
  intro x hxblue' hxF
  rcases hstep with ⟨u, v, hforce, rfl⟩
  rcases hforce with ⟨huBlue, _hvWhite, huv, huniq⟩
  rw [Finset.mem_insert] at hxblue'
  rcases hxblue' with hxeq | hxblue
  · subst x
    have huNotF : u ∉ F := by
      intro huF
      exact hdisj u huBlue huF
    rcases hF u huNotF v hxF huv with ⟨w, hwF, huw, hwne⟩
    have hwWhite : w ∉ blue := by
      intro hwBlue
      exact hdisj w hwBlue hwF
    have hwEq : w = v := huniq w hwWhite huw
    exact hwne hwEq
  · exact hdisj x hxblue hxF

/-- Disjointness from a fort is invariant under any finite forcing sequence. -/
theorem reflTransGen_disjoint_fort_preserved [DecidableEq V]
    {G : SimpleGraph V} {blue blue' F : Finset V}
    (hF : IsFort G F)
    (hdisj : Disjoint blue F)
    (hsteps : Relation.ReflTransGen (ForceStep G) blue blue') :
    Disjoint blue' F := by
  induction hsteps with
  | refl =>
      exact hdisj
  | tail hsteps hstep ih =>
      exact ForceStep.disjoint_fort_preserved hF ih hstep

/--
Every zero-forcing set intersects every nonempty fort.

Otherwise the fort would remain completely white throughout the entire forcing
sequence, contradicting that a zero-forcing sequence reaches `Finset.univ`.
-/
theorem IsZeroForcingSet.intersects_fort [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {blue F : Finset V}
    (hZ : IsZeroForcingSet G blue)
    (hF : IsFort G F)
    (hne : F.Nonempty) :
    (blue ∩ F).Nonempty := by
  by_contra hnot
  have hdisj : Disjoint blue F := by
    rw [Finset.disjoint_left]
    intro v hvBlue hvF
    exact hnot ⟨v, by simp [hvBlue, hvF]⟩
  unfold IsZeroForcingSet at hZ
  have hfinal : Disjoint (Finset.univ : Finset V) F :=
    reflTransGen_disjoint_fort_preserved hF hdisj hZ
  rcases hne with ⟨v, hvF⟩
  exact Finset.disjoint_left.mp hfinal (Finset.mem_univ v) hvF

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
