import FischerZeroForcing.Basic

/-!
# Graph infrastructure

The project uses Mathlib's `SimpleGraph`, connectivity, finite degree, and
finite-set infrastructure directly rather than defining a second graph type.
-/

namespace FischerZeroForcing

abbrev Vertex := Fin 24

end FischerZeroForcing
