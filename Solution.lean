import FischerZeroForcing.Main

/-!
# Fischer's zero-forcing counterexample: solution surface

This file is a bootstrap placeholder. The theorem has the same intended type as
the Challenge declaration, but the proof is not yet implemented.
-/

namespace FischerZeroForcing

theorem main_result :
    ∃ G : SimpleGraph (Fin 24),
      G.Connected ∧
      (∀ v : Fin 24, G.degree v ≤ 3) ∧
      G.indepNum = 9 ∧
      zeroForcingNumber G = 11 := by
  sorry

end FischerZeroForcing
