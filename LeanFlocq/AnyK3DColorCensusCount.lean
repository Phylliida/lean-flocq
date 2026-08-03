/-
# Color M3 cross-checks: subgroup and census counts

The independent cross-checks for the color census enumeration
(`AnyK3DColorCensus.lean`), split into their own module so the proof
chain (Bridge/Part/Complete) doesn't rebuild behind the heavy
`native_decide`s:

  * `subMasksC_count` — 10 subgroups of the 8-element color gain group
    (matches the Python feasibility probe: all 10 exact-stabilizer
    realizable, missing = 0).
  * `census_count_fastC` — THE cross-check: Lean must independently
    reproduce the Python color census count 9,341,248
    (`monotile/color_census.py` → `color3d_profiles.json`).
-/
import Mathlib
import LeanFlocq.AnyK3DColorCensus

set_option maxRecDepth 100000

namespace AnyK3D

/-- Cross-check vs Python (color_census: 10 subgroups, all feasible). -/
theorem subMasksC_count : subMasksC.size = 10 := by
  native_decide

/-- THE cross-check: Lean must independently reproduce the Python color
census count (color3d_profiles.json: 9,341,248 achievable profiles). -/
theorem census_count_fastC : censusFastC.size = 9341248 := by
  native_decide

end AnyK3D
