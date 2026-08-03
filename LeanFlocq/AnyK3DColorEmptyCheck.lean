/-
Batch checkers for the color empty frontier data
(`AnyK3DColorEmptyData.lean`): dims positivity, `maskLeB` inclusion
checker + bridge to `maskLe`, and the 130,808-pair inheritance batch.
Split from `AnyK3DColorEmpty.lean` (elaboration of the axiom module is
heavy enough on its own).
-/

import LeanFlocq.AnyK3DCerts
import LeanFlocq.AnyK3DColorEmptyData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace AnyK3D

/-- Number of frontier jobs (65,250). -/
def frontierSize : ℕ := colorFrontierJobs.size

/-- Index accessor for frontier jobs. Irreducible so that elaboration
never whnf-reduces the (append-chained) data arrays during unification;
compiled evaluation is unaffected. -/
@[irreducible]
def frontierJob (i : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  colorFrontierJobs.getD i (0, 0, 0, 0)

-- Data hygiene: every job has positive dims (used by `empty_sound`).
theorem colorFrontierJobs_dims_pos :
    (List.range frontierSize).all (fun i =>
      decide (0 < (frontierJob i).2.1) &&
      decide (0 < (frontierJob i).2.2.1) && decide (0 < (frontierJob i).2.2.2))
      = true := by
  native_decide

/-- Bool checker for mask inclusion over the 84 equation bits. -/
def maskLeB (m m' : ℕ) : Bool :=
  (List.range 84).all (fun j =>
    decide (m.testBit j = true → m'.testBit j = true))

theorem maskLe_of_maskLeB {m m' : ℕ} (hm : m < 2 ^ 84)
    (h : maskLeB m m' = true) :
    maskLe m m' := by
  intro j hj
  by_cases hj84 : j < 84
  · have hb := (List.all_eq_true.mp h) j (List.mem_range.mpr hj84)
    exact of_decide_eq_true hb hj
  · have hm' : m < 2 ^ j :=
      lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hm'] at hj
    exact absurd hj (by decide)

-- The 130,808 inheritance pairs, batch-checked: each profile mask is
-- contained in its frontier mask, fits in 84 bits, and the job index is
-- in range.
theorem colorInheritance_valid :
    colorInheritance.all (fun p =>
      decide (p.1 < 2 ^ 84) &&
      decide (p.2 < frontierSize) &&
      maskLeB p.1 (frontierJob p.2).1)
      = true := by
  native_decide

/-- Count check: 65,250 frontier jobs, 130,808 inheritance pairs. -/
theorem color_empty_counts :
    colorFrontierJobs.size = 65250 ∧ colorInheritance.size = 130808 := by
  native_decide

end AnyK3D
