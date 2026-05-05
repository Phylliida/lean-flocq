/-
Port of `flocq/src/Core/Raux.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Currently provides `bpow` and a handful of facts about it. The bulk of
`Raux.v` will be ported on demand.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Int.Log
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

/-- Bridge between integer power and `bpow` at non-negative exponents. -/
theorem IZR_Zpower (beta : radix) {n : ℤ} (hn : 0 ≤ n) :
    ((beta.val ^ n.toNat : ℤ) : ℝ) = bpow beta n := by
  unfold bpow
  push_cast
  rw [show n = ((n.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hn).symm, zpow_natCast,
      Int.toNat_natCast]

/-! ### Truncation toward zero -/

/-- `Ztrunc x` is `⌈x⌉` for `x < 0`, `⌊x⌋` otherwise (truncation toward 0).
Matches Coq's `Ztrunc x := if Rlt_bool x 0 then Zceil x else Zfloor x`. -/
noncomputable def Ztrunc (x : ℝ) : ℤ :=
  if x < 0 then ⌈x⌉ else ⌊x⌋

theorem Ztrunc_intCast (n : ℤ) : Ztrunc (n : ℝ) = n := by
  unfold Ztrunc
  by_cases h : (n : ℝ) < 0
  · rw [if_pos h, Int.ceil_intCast]
  · rw [if_neg h, Int.floor_intCast]

theorem Ztrunc_floor {x : ℝ} (hx : 0 ≤ x) : Ztrunc x = ⌊x⌋ := by
  unfold Ztrunc
  rw [if_neg (not_lt.mpr hx)]

theorem Ztrunc_ceil {x : ℝ} (hx : x ≤ 0) : Ztrunc x = ⌈x⌉ := by
  unfold Ztrunc
  rcases lt_or_eq_of_le hx with h | h
  · rw [if_pos h]
  · rw [h]; simp

theorem Ztrunc_opp (x : ℝ) : Ztrunc (-x) = -Ztrunc x := by
  unfold Ztrunc
  by_cases h : x < 0
  · rw [if_neg (by linarith : ¬(-x) < 0), if_pos h, Int.floor_neg]
  · by_cases h0 : x = 0
    · rw [h0]; simp
    · have hpos : 0 < x := lt_of_le_of_ne (not_lt.mp h) (Ne.symm h0)
      rw [if_pos (by linarith : -x < 0), if_neg h, Int.ceil_neg]

/-! ### Magnitude (`mag`): integer e with `β^(e-1) ≤ |x| < β^e` for `x ≠ 0` -/

/-- `mag beta x` returns the integer `e` such that `β^(e-1) ≤ |x| < β^e`
when `x ≠ 0`. For `x = 0` it returns `0` (convention; theorems require `x ≠ 0`).

Coq's `mag` is a sigma type bundling the integer with its specification.
We split this into a bare function plus separate theorems (`mag_unique`,
`mag_opp`, `mag_abs`, `mag_bpow`). -/
noncomputable def mag (beta : radix) (x : ℝ) : ℤ :=
  if x = 0 then 0 else Int.log beta.val.toNat |x| + 1

@[simp]
theorem mag_zero (beta : radix) : mag beta 0 = 0 := by
  unfold mag; simp

theorem mag_opp (beta : radix) (x : ℝ) : mag beta (-x) = mag beta x := by
  unfold mag
  by_cases hx : x = 0
  · rw [hx]; simp
  · have hxn : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [if_neg hxn, if_neg hx, abs_neg]

theorem mag_abs (beta : radix) (x : ℝ) : mag beta |x| = mag beta x := by
  unfold mag
  by_cases hx : x = 0
  · rw [hx]; simp
  · have hxn : |x| ≠ 0 := abs_ne_zero.mpr hx
    rw [if_neg hxn, if_neg hx, abs_abs]

/-- Bridge: cast `(beta.val.toNat : ℕ) → ℝ` equals `(beta.val : ℤ) → ℝ`. -/
private theorem natCast_toNat_val (beta : radix) :
    ((beta.val.toNat : ℕ) : ℝ) = (beta.val : ℝ) := by
  have hnn : (0 : ℤ) ≤ beta.val := le_of_lt beta.radix_gt_0
  rw [show ((beta.val.toNat : ℕ) : ℝ) = ((beta.val.toNat : ℤ) : ℝ) from by push_cast; rfl,
      Int.toNat_of_nonneg hnn]

/-- The defining property of `mag`: if `β^(e-1) ≤ |x| < β^e`, then `mag β x = e`. -/
theorem mag_unique (beta : radix) {x : ℝ} {e : ℤ}
    (hlow : bpow beta (e - 1) ≤ |x|) (hhigh : |x| < bpow beta e) :
    mag beta x = e := by
  have hbeta : 1 < beta.val.toNat := by have := beta.prop; omega
  have hxpos : 0 < |x| := lt_of_lt_of_le (bpow_gt_0 beta (e - 1)) hlow
  have hxne : x ≠ 0 := fun hx0 => by simp [hx0] at hxpos
  unfold mag
  rw [if_neg hxne]
  -- Convert bpow expressions to use beta.val.toNat for Int.log lemmas
  have hcast := natCast_toNat_val beta
  have hlow' : ((beta.val.toNat : ℕ) : ℝ) ^ (e - 1) ≤ |x| := by
    unfold bpow at hlow; rwa [hcast]
  have hhigh' : |x| < ((beta.val.toNat : ℕ) : ℝ) ^ e := by
    unfold bpow at hhigh; rwa [hcast]
  have hge : e - 1 ≤ Int.log beta.val.toNat |x| :=
    (Int.zpow_le_iff_le_log hbeta hxpos).mp hlow'
  have hlt : Int.log beta.val.toNat |x| < e :=
    (Int.lt_zpow_iff_log_lt hbeta hxpos).mp hhigh'
  omega

/-- `mag β (β^e) = e + 1`. -/
theorem mag_bpow (beta : radix) (e : ℤ) : mag beta (bpow beta e) = e + 1 := by
  apply mag_unique
  · rw [abs_of_pos (bpow_gt_0 beta e)]
    have : e - 1 + 1 = e := by ring
    calc bpow beta (e + 1 - 1) = bpow beta e := by rw [show e + 1 - 1 = e from by ring]
      _ ≤ bpow beta e := le_refl _
  · rw [abs_of_pos (bpow_gt_0 beta e)]
    exact bpow_lt beta (by omega : e < e + 1)

end LeanFlocq
