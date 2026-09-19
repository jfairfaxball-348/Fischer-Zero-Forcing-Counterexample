import FischerZeroForcing.FischerGraph

/-!
# Computable zero-forcing closure for Fischer's graph

This file supplies the small deterministic decision procedure used by the
finite lower-bound check.  One round simultaneously collects every vertex
that is currently forceable.  The proof below shows that a round can be
sequentialized into ordinary `ForceStep` moves, and that every zero-forcing
set must reach `univ` within at most `Fintype.card Vertex` rounds.

Thus the computation is connected to the existing mathematical
`Relation.ReflTransGen` definition rather than replacing it.
-/

namespace FischerZeroForcing

/-- Explicit neighbour table for the fixed 24-vertex Fischer graph. -/
def fischerNeighbors : Vertex → Finset Vertex :=
  ![
    ([1, 2, 3] : List Vertex).toFinset,
    ([0, 2, 10] : List Vertex).toFinset,
    ([0, 1, 17] : List Vertex).toFinset,
    ([0, 4, 7] : List Vertex).toFinset,
    ([3, 5, 6] : List Vertex).toFinset,
    ([4, 6] : List Vertex).toFinset,
    ([4, 5] : List Vertex).toFinset,
    ([3, 8, 9] : List Vertex).toFinset,
    ([7, 9] : List Vertex).toFinset,
    ([7, 8] : List Vertex).toFinset,
    ([1, 11, 14] : List Vertex).toFinset,
    ([10, 12, 13] : List Vertex).toFinset,
    ([11, 13] : List Vertex).toFinset,
    ([11, 12] : List Vertex).toFinset,
    ([10, 15, 16] : List Vertex).toFinset,
    ([14, 16] : List Vertex).toFinset,
    ([14, 15] : List Vertex).toFinset,
    ([2, 18, 21] : List Vertex).toFinset,
    ([17, 19, 20] : List Vertex).toFinset,
    ([18, 20] : List Vertex).toFinset,
    ([18, 19] : List Vertex).toFinset,
    ([17, 22, 23] : List Vertex).toFinset,
    ([21, 23] : List Vertex).toFinset,
    ([21, 22] : List Vertex).toFinset
  ]

/-- The explicit neighbour table is exactly the graph adjacency relation. -/
@[simp] theorem mem_fischerNeighbors_iff (u v : Vertex) :
    v ∈ fischerNeighbors u ↔ fischerGraph.Adj u v := by
  fin_cases u <;> fin_cases v <;> native_decide

/-- White neighbours of `u` in the current blue set. -/
def fischerWhiteNeighbors (blue : Finset Vertex) (u : Vertex) : Finset Vertex :=
  fischerNeighbors u \ blue

/--
For the fixed graph, the mathematical forcing predicate is exactly the
statement that the forcing vertex is blue and its white-neighbour set is the
singleton containing the target.
-/
theorem canForce_iff_whiteNeighbors_eq_singleton
    {blue : Finset Vertex} {u v : Vertex} :
    CanForce fischerGraph blue u v ↔
      u ∈ blue ∧ fischerWhiteNeighbors blue u = {v} := by
  constructor
  · rintro ⟨hu, hvWhite, huv, huniq⟩
    refine ⟨hu, ?_⟩
    ext w
    constructor
    · intro hw
      have hwN : w ∈ fischerNeighbors u := (Finset.mem_sdiff.mp hw).1
      have hwWhite : w ∉ blue := (Finset.mem_sdiff.mp hw).2
      have huw : fischerGraph.Adj u w :=
        (mem_fischerNeighbors_iff u w).mp hwN
      have hwv : w = v := huniq w hwWhite huw
      subst w
      simp
    · intro hw
      have hwv : w = v := by simpa using hw
      subst w
      exact Finset.mem_sdiff.mpr
        ⟨(mem_fischerNeighbors_iff u v).mpr huv, hvWhite⟩
  · rintro ⟨hu, hwhite⟩
    have hvMem : v ∈ fischerWhiteNeighbors blue u := by
      rw [hwhite]
      simp
    have hvN : v ∈ fischerNeighbors u := (Finset.mem_sdiff.mp hvMem).1
    have hvWhite : v ∉ blue := (Finset.mem_sdiff.mp hvMem).2
    refine ⟨hu, hvWhite, (mem_fischerNeighbors_iff u v).mp hvN, ?_⟩
    intro w hwWhite huw
    have hwMem : w ∈ fischerWhiteNeighbors blue u :=
      Finset.mem_sdiff.mpr
        ⟨(mem_fischerNeighbors_iff u w).mpr huw, hwWhite⟩
    rw [hwhite] at hwMem
    simpa using hwMem

/--
A force remains legal after enlarging the blue set, provided its target is
still white.  This is the monotonicity fact used to sequentialize a round.
-/
theorem CanForce.mono {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {blue blue' : Finset V} {u v : V}
    (h : CanForce G blue u v)
    (hsub : blue ⊆ blue')
    (hvWhite : v ∉ blue') :
    CanForce G blue' u v := by
  rcases h with ⟨hu, _hv, huv, huniq⟩
  refine ⟨hsub hu, hvWhite, huv, ?_⟩
  intro w hwWhite huw
  have hwOld : w ∉ blue := by
    intro hw
    exact hwWhite (hsub hw)
  exact huniq w hwOld huw

/--
A single legal force can be simulated from any larger blue set: if its target
is already blue, no move is needed; otherwise the same force remains legal.
-/
private theorem ForceStep.lift_superset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {blue next bigger : Finset V}
    (hstep : ForceStep G blue next)
    (hsub : blue ⊆ bigger) :
    ∃ bigger',
      Relation.ReflTransGen (ForceStep G) bigger bigger' ∧
      next ⊆ bigger' := by
  rcases hstep with ⟨u, v, hforce, rfl⟩
  by_cases hv : v ∈ bigger
  · refine ⟨bigger, Relation.ReflTransGen.refl, ?_⟩
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hv
    · exact hsub hx
  · refine ⟨insert v bigger, ?_, ?_⟩
    · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        ⟨u, v, hforce.mono hsub hv, rfl⟩
    · intro x hx
      rw [Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (hsub hx)

/-- A whole forcing sequence can be replayed from any larger initial blue set. -/
private theorem reflTransGen_lift_superset {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {blue target bigger : Finset V}
    (hsteps : Relation.ReflTransGen (ForceStep G) blue target)
    (hsub : blue ⊆ bigger) :
    ∃ bigger',
      Relation.ReflTransGen (ForceStep G) bigger bigger' ∧
      target ⊆ bigger' := by
  induction hsteps generalizing bigger with
  | refl =>
      exact ⟨bigger, Relation.ReflTransGen.refl, hsub⟩
  | tail hpre hlast ih =>
      rcases ih hsub with ⟨mid, hreach, hmid⟩
      rcases ForceStep.lift_superset hlast hmid with
        ⟨finish, hfinish, hsubfinish⟩
      exact ⟨finish, hreach.trans hfinish, hsubfinish⟩

/-- Supersets of zero-forcing sets are again zero forcing. -/
theorem IsZeroForcingSet.mono {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {blue bigger : Finset V}
    (hZ : IsZeroForcingSet G blue)
    (hsub : blue ⊆ bigger) :
    IsZeroForcingSet G bigger := by
  unfold IsZeroForcingSet at hZ ⊢
  rcases reflTransGen_lift_superset hZ hsub with
    ⟨finish, hreach, huniv⟩
  have hfinish : finish = (Finset.univ : Finset V) := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    exact huniv (Finset.mem_univ x)
  simpa [hfinish] using hreach

/--
Every target forceable in the present position.  The implementation scans only
currently blue vertices and uses the explicit neighbour table.
-/
def fischerForceTargets (blue : Finset Vertex) : Finset Vertex :=
  blue.biUnion fun u =>
    let W := fischerWhiteNeighbors blue u
    if W.card = 1 then W else ∅

/-- Membership in the computed target set is exactly existence of a legal force. -/
theorem mem_fischerForceTargets_iff {blue : Finset Vertex} {v : Vertex} :
    v ∈ fischerForceTargets blue ↔
      ∃ u : Vertex, CanForce fischerGraph blue u v := by
  constructor
  · intro hv
    rw [fischerForceTargets, Finset.mem_biUnion] at hv
    rcases hv with ⟨u, hu, hv⟩
    by_cases hcard : (fischerWhiteNeighbors blue u).card = 1
    · simp [hcard] at hv
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
      have hvw : v = w := by
        rw [hw] at hv
        simpa using hv
      have hwhite : fischerWhiteNeighbors blue u = {v} := by
        simpa [hvw] using hw
      exact ⟨u, (canForce_iff_whiteNeighbors_eq_singleton).2 ⟨hu, hwhite⟩⟩
    · simp [hcard] at hv
  · rintro ⟨u, hforce⟩
    rcases (canForce_iff_whiteNeighbors_eq_singleton).1 hforce with
      ⟨hu, hwhite⟩
    rw [fischerForceTargets, Finset.mem_biUnion]
    refine ⟨u, hu, ?_⟩
    have hcard : (fischerWhiteNeighbors blue u).card = 1 := by
      rw [hwhite]
      simp
    simp [hwhite]

/-- One deterministic closure round: add all targets currently forceable. -/
def fischerForceRound (blue : Finset Vertex) : Finset Vertex :=
  blue ∪ fischerForceTargets blue

theorem blue_subset_fischerForceRound (blue : Finset Vertex) :
    blue ⊆ fischerForceRound blue :=
  Finset.subset_union_left

/--
A finite set of targets that were all forceable from the original position
can be inserted one by one by legal `ForceStep` moves.
-/
private theorem forceTargets_reachable
    (blue targets : Finset Vertex)
    (hTargets :
      ∀ v ∈ targets, ∃ u : Vertex, CanForce fischerGraph blue u v) :
    Relation.ReflTransGen (ForceStep fischerGraph)
      blue (blue ∪ targets) := by
  induction targets using Finset.induction_on with
  | empty =>
      simpa using
        (Relation.ReflTransGen.refl :
          Relation.ReflTransGen (ForceStep fischerGraph) blue blue)
  | @insert v targets hvnot ih =>
      have hvForce : ∃ u : Vertex, CanForce fischerGraph blue u v :=
        hTargets v (by simp)
      have hRest :
          ∀ w ∈ targets, ∃ u : Vertex, CanForce fischerGraph blue u w := by
        intro w hw
        exact hTargets w (by simp [hw])
      have hreach :
          Relation.ReflTransGen (ForceStep fischerGraph)
            blue (blue ∪ targets) :=
        ih hRest
      rcases hvForce with ⟨u, hforce⟩
      have hvBlue : v ∉ blue := hforce.2.1
      have hvCurrent : v ∉ blue ∪ targets := by
        simp [hvBlue, hvnot]
      have hforceCurrent :
          CanForce fischerGraph (blue ∪ targets) u v :=
        hforce.mono Finset.subset_union_left hvCurrent
      have hstep :
          ForceStep fischerGraph (blue ∪ targets)
            (insert v (blue ∪ targets)) :=
        ⟨u, v, hforceCurrent, rfl⟩
      have htail := Relation.ReflTransGen.tail hreach hstep
      simpa [Finset.ext_iff, or_assoc, or_left_comm, or_comm] using htail

/-- A simultaneous closure round is reachable by ordinary sequential forces. -/
theorem fischerForceRound_reachable (blue : Finset Vertex) :
    Relation.ReflTransGen (ForceStep fischerGraph)
      blue (fischerForceRound blue) := by
  unfold fischerForceRound
  apply forceTargets_reachable
  intro v hv
  exact (mem_fischerForceTargets_iff).1 hv

/--
Any nontrivial reflexive-transitive path has an outgoing first step from its
initial point.
-/
private theorem reflTransGen_exists_first {α : Type*} {r : α → α → Prop}
    {a b : α}
    (h : Relation.ReflTransGen r a b)
    (hne : a ≠ b) :
    ∃ c, r a c := by
  induction h with
  | refl =>
      exact (hne rfl).elim
  | @tail x y hax hxy ih =>
      by_cases haxeq : a = x
      · subst x
        exact ⟨y, hxy⟩
      · exact ih haxeq

/-- A zero-forcing nonterminal position has at least one computed force target. -/
private theorem fischerForceTargets_nonempty_of_zeroForcing
    {blue : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph blue)
    (hne : blue ≠ (Finset.univ : Finset Vertex)) :
    (fischerForceTargets blue).Nonempty := by
  unfold IsZeroForcingSet at hZ
  rcases reflTransGen_exists_first hZ hne with ⟨next, hstep⟩
  rcases hstep with ⟨u, v, hforce, _⟩
  exact ⟨v, (mem_fischerForceTargets_iff).2 ⟨u, hforce⟩⟩

/-- A zero-forcing nonterminal position strictly grows after one closure round. -/
private theorem card_lt_fischerForceRound_of_zeroForcing
    {blue : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph blue)
    (hne : blue ≠ (Finset.univ : Finset Vertex)) :
    blue.card < (fischerForceRound blue).card := by
  rcases fischerForceTargets_nonempty_of_zeroForcing hZ hne with ⟨v, hv⟩
  have hvRound : v ∈ fischerForceRound blue := by
    simp [fischerForceRound, hv]
  have hvBlue : v ∉ blue := by
    rcases (mem_fischerForceTargets_iff).1 hv with ⟨u, hforce⟩
    exact hforce.2.1
  have hproper : blue ⊂ fischerForceRound blue := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨blue_subset_fischerForceRound blue, ?_⟩
    intro heq
    apply hvBlue
    rw [heq]
    exact hvRound
  exact Finset.card_lt_card hproper

/-- Iterate deterministic simultaneous-force rounds for a fixed amount of fuel. -/
def fischerForceClosureAux : Nat → Finset Vertex → Finset Vertex
  | 0, blue => blue
  | n + 1, blue => fischerForceClosureAux n (fischerForceRound blue)

/-- Full project-local closure, with one round of fuel per graph vertex. -/
def fischerForceClosure (blue : Finset Vertex) : Finset Vertex :=
  fischerForceClosureAux (Fintype.card Vertex) blue

@[simp] theorem fischerForceRound_univ :
    fischerForceRound (Finset.univ : Finset Vertex) = Finset.univ := by
  simp [fischerForceRound]

@[simp] theorem fischerForceClosureAux_univ (n : Nat) :
    fischerForceClosureAux n (Finset.univ : Finset Vertex) = Finset.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [fischerForceClosureAux] using ih

/-- If the deterministic closure reaches all vertices, the original set is zero forcing. -/
private theorem closureAux_eq_univ_imp_zeroForcing
    {n : Nat} {blue : Finset Vertex}
    (hclosure :
      fischerForceClosureAux n blue = (Finset.univ : Finset Vertex)) :
    IsZeroForcingSet fischerGraph blue := by
  induction n generalizing blue with
  | zero =>
      simp only [fischerForceClosureAux] at hclosure
      rw [hclosure]
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      simp only [fischerForceClosureAux] at hclosure
      have hnext :
          IsZeroForcingSet fischerGraph (fischerForceRound blue) :=
        ih hclosure
      unfold IsZeroForcingSet at hnext ⊢
      exact (fischerForceRound_reachable blue).trans hnext

/--
If the original set is zero forcing, enough closure-round fuel must reach
`univ`.  The measure is the number of still-white vertices.
-/
private theorem zeroForcing_imp_closureAux_eq_univ
    {n : Nat} {blue : Finset Vertex}
    (hZ : IsZeroForcingSet fischerGraph blue)
    (hfuel : Fintype.card Vertex - blue.card ≤ n) :
    fischerForceClosureAux n blue = (Finset.univ : Finset Vertex) := by
  induction n generalizing blue with
  | zero =>
      have hle : blue.card ≤ Fintype.card Vertex :=
        Finset.card_le_univ blue
      have hcard : blue.card = Fintype.card Vertex := by
        omega
      have hblue : blue = (Finset.univ : Finset Vertex) :=
        (Finset.card_eq_iff_eq_univ blue).mp hcard
      simpa [hblue]
  | succ n ih =>
      by_cases hblue : blue = (Finset.univ : Finset Vertex)
      · subst blue
        simp
      · have hlt :
            blue.card < (fischerForceRound blue).card :=
          card_lt_fischerForceRound_of_zeroForcing hZ hblue
        have hroundle :
            (fischerForceRound blue).card ≤ Fintype.card Vertex :=
          Finset.card_le_univ _
        have hnextZ :
            IsZeroForcingSet fischerGraph (fischerForceRound blue) :=
          hZ.mono (blue_subset_fischerForceRound blue)
        have hnextFuel :
            Fintype.card Vertex - (fischerForceRound blue).card ≤ n := by
          omega
        simp only [fischerForceClosureAux]
        exact ih hnextZ hnextFuel

/-- The deterministic closure is complete for the existing zero-forcing definition. -/
theorem fischerForceClosure_eq_univ_iff (blue : Finset Vertex) :
    fischerForceClosure blue = (Finset.univ : Finset Vertex) ↔
      IsZeroForcingSet fischerGraph blue := by
  constructor
  · intro h
    exact closureAux_eq_univ_imp_zeroForcing h
  · intro hZ
    unfold fischerForceClosure
    apply zeroForcing_imp_closureAux_eq_univ hZ
    exact Nat.sub_le _ _

/-- Boolean form used by the 17,712-candidate native computation. -/
def fischerIsZeroForcingBool (blue : Finset Vertex) : Bool :=
  decide (fischerForceClosure blue = (Finset.univ : Finset Vertex))

theorem fischerIsZeroForcingBool_eq_true_iff (blue : Finset Vertex) :
    fischerIsZeroForcingBool blue = true ↔
      IsZeroForcingSet fischerGraph blue := by
  simpa [fischerIsZeroForcingBool] using fischerForceClosure_eq_univ_iff blue

end FischerZeroForcing
