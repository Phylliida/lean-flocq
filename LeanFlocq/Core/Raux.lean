/-
Port of `flocq/src/Core/Raux.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Currently provides `bpow` and a handful of facts about it. The bulk of
`Raux.v` will be ported on demand.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic.Positivity
import LeanFlocq.Core.Zaux

namespace LeanFlocq

open radix

/-- Power of the radix: `bpow beta e = beta^e` as a real number. -/
noncomputable def bpow (beta : radix) (e : ℤ) : ℝ :=
  (beta.val : ℝ) ^ e

/-- The radix is positive in ℝ. -/
theorem radix_pos (r : radix) : (0 : ℝ) < (r.val : ℝ) := by
  exact_mod_cast r.radix_gt_0

/-- `bpow` is strictly positive. -/
theorem bpow_gt_0 (beta : radix) (e : ℤ) : 0 < bpow beta e := by
  unfold bpow; exact zpow_pos (radix_pos beta) e

/-- `bpow` is non-negative. -/
theorem bpow_ge_0 (beta : radix) (e : ℤ) : 0 ≤ bpow beta e :=
  le_of_lt (bpow_gt_0 beta e)

/-- `bpow` is never zero. -/
theorem bpow_ne_0 (beta : radix) (e : ℤ) : bpow beta e ≠ 0 :=
  ne_of_gt (bpow_gt_0 beta e)

end LeanFlocq
