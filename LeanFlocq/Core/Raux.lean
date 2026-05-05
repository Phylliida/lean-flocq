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

@[simp]
theorem bpow_zero (beta : radix) : bpow beta 0 = 1 := by
  unfold bpow; simp

@[simp]
theorem bpow_one (beta : radix) : bpow beta 1 = (beta.val : ℝ) := by
  unfold bpow; simp

/-- `bpow` is additive in the exponent. -/
theorem bpow_plus (beta : radix) (e1 e2 : ℤ) :
    bpow beta (e1 + e2) = bpow beta e1 * bpow beta e2 := by
  unfold bpow
  exact zpow_add₀ (ne_of_gt (radix_pos beta)) e1 e2

/-- `bpow` is monotone in the exponent. -/
theorem bpow_le (beta : radix) {e1 e2 : ℤ} (h : e1 ≤ e2) :
    bpow beta e1 ≤ bpow beta e2 := by
  unfold bpow
  have hβ : (1 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.radix_gt_1.le
  exact zpow_le_zpow_right₀ hβ h

/-- `bpow` is strictly monotone in the exponent. -/
theorem bpow_lt (beta : radix) {e1 e2 : ℤ} (h : e1 < e2) :
    bpow beta e1 < bpow beta e2 := by
  unfold bpow
  have hβ : (1 : ℝ) < (beta.val : ℝ) := by exact_mod_cast beta.radix_gt_1
  exact zpow_lt_zpow_right₀ hβ h

/-- Converse of `bpow_le`: monotonicity is reversible. -/
theorem le_bpow (beta : radix) {e1 e2 : ℤ}
    (h : bpow beta e1 ≤ bpow beta e2) : e1 ≤ e2 := by
  by_contra hlt
  push_neg at hlt
  exact absurd (bpow_lt beta hlt) (not_lt.mpr h)

/-- Converse of `bpow_lt`. -/
theorem lt_bpow (beta : radix) {e1 e2 : ℤ}
    (h : bpow beta e1 < bpow beta e2) : e1 < e2 := by
  by_contra hle
  push_neg at hle
  exact absurd (bpow_le beta hle) (not_le.mpr h)

end LeanFlocq
