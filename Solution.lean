import FischerZeroForcing.Main

/-!
# Fischer's zero-forcing counterexample: solution surface

The project proof establishes the exact invariants for Fischer's explicit
24-vertex connected subcubic graph and packages them into the advertised
existential statement.
-/

namespace FischerZeroForcing

theorem main_result :
    ∃ G : SimpleGraph (Fin 24),
      G.Connected ∧
      (∀ v : Fin 24, (G.neighborSet v).ncard ≤ 3) ∧
      G.indepNum = 9 ∧
      zeroForcingNumber G = 11 := by
  exact ⟨fischerGraph, fischerGraph_counterexample⟩

end FischerZeroForcing
