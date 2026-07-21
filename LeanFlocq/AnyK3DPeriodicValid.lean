/-
# M4-C2 validation: the 340 periodic frontier certificates are valid

One `native_decide`: every minimal-periodic frontier mask's exported
a×b×c grid passes the `rect3OK` wrapped-adjacency check. Soundness of
the checker (`rect3_sound`, in `AnyK3DCerts.lean`) then upgrades each to
a fully periodic ℤ³ tiling; monotonicity (`periodic_mono`) lifts along
mask inclusion. The Python generator is not in the trust base — this
file re-verifies the data from scratch.
-/
import Mathlib
import LeanFlocq.AnyK3DCerts
import LeanFlocq.AnyK3DPeriodicCerts

set_option maxRecDepth 100000

namespace AnyK3D

/-- All 340 minimal-periodic frontier masks carry valid rectangular-torus
certificates. -/
theorem periodic_certs_valid :
    ∀ i < minPeriodic.size,
      rect3OK (relOfMask (minPeriodic.getD i 0))
        (certDims.getD i (0, 0, 0)).1 (certDims.getD i (0, 0, 0)).2.1
        (certDims.getD i (0, 0, 0)).2.2 (certGrids.getD i 0) = true := by
  native_decide

end AnyK3D
