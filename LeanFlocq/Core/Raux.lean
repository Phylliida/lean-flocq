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
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity
import LeanFlocq.Core.Zaux

namespace LeanFlocq

open radix

/-- Power of the radix: `bpow beta e = beta^e` as a real number. -/
noncomputable def bpow (beta : radix) (e : ℤ) : ℝ :=
  (beta.val : ℝ) ^ e

/-- Conditional real negation: `cond_Ropp true x = -x`, `false → x`. -/
def cond_Ropp (b : Bool) (x : ℝ) : ℝ := if b then -x else x

@[simp] theorem cond_Ropp_true (x : ℝ) : cond_Ropp true x = -x := rfl
@[simp] theorem cond_Ropp_false (x : ℝ) : cond_Ropp false x = x := rfl

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

/-- `Zaway x` is `⌊x⌋` for `x < 0`, `⌈x⌉` otherwise (rounding away from 0). -/
noncomputable def Zaway (x : ℝ) : ℤ :=
  if x < 0 then ⌊x⌋ else ⌈x⌉

theorem Ztrunc_le {x y : ℝ} (Hxy : x ≤ y) : Ztrunc x ≤ Ztrunc y := by
  unfold Ztrunc
  by_cases Hx : x < 0
  · rw [if_pos Hx]
    by_cases Hy : y < 0
    · rw [if_pos Hy]; exact Int.ceil_le_ceil Hxy
    · rw [if_neg Hy]
      have h1 : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith)
      have h2 : (0 : ℤ) ≤ ⌊y⌋ := Int.floor_nonneg.mpr (not_lt.mp Hy)
      linarith
  · rw [if_neg Hx]
    have Hy : ¬ y < 0 := fun h => Hx (lt_of_le_of_lt Hxy h)
    rw [if_neg Hy]
    exact Int.floor_le_floor Hxy

theorem Zaway_le {x y : ℝ} (Hxy : x ≤ y) : Zaway x ≤ Zaway y := by
  unfold Zaway
  by_cases Hx : x < 0
  · rw [if_pos Hx]
    by_cases Hy : y < 0
    · rw [if_pos Hy]; exact Int.floor_le_floor Hxy
    · rw [if_neg Hy]
      have h1 : ⌊x⌋ ≤ 0 := by
        have := Int.floor_le_floor (le_of_lt Hx : x ≤ 0); simpa using this
      have h2 : (0 : ℤ) ≤ ⌈y⌉ := Int.ceil_nonneg (not_lt.mp Hy)
      linarith
  · rw [if_neg Hx]
    have Hy : ¬ y < 0 := fun h => Hx (lt_of_le_of_lt Hxy h)
    rw [if_neg Hy]
    exact Int.ceil_le_ceil Hxy

theorem Zaway_intCast (n : ℤ) : Zaway (n : ℝ) = n := by
  unfold Zaway
  by_cases h : (n : ℝ) < 0
  · rw [if_pos h, Int.floor_intCast]
  · rw [if_neg h, Int.ceil_intCast]

theorem Zaway_opp (x : ℝ) : Zaway (-x) = -Zaway x := by
  unfold Zaway
  by_cases h : x < 0
  · rw [if_pos h, if_neg (by linarith : ¬(-x) < 0), Int.ceil_neg]
  · by_cases h0 : x = 0
    · rw [h0]; simp
    · have hpos : 0 < x := lt_of_le_of_ne (not_lt.mp h) (Ne.symm h0)
      rw [if_pos (by linarith : -x < 0), if_neg h, Int.floor_neg]

theorem Ztrunc_abs (x : ℝ) : Ztrunc |x| = |Ztrunc x| := by
  rw [Ztrunc_floor (abs_nonneg x)]
  by_cases h : x < 0
  · unfold Ztrunc; rw [if_pos h, abs_of_neg h, Int.floor_neg]
    have hcle : ⌈x⌉ ≤ 0 := by
      have : ⌈x⌉ ≤ ⌈(0 : ℝ)⌉ := Int.ceil_le_ceil (le_of_lt h)
      simpa using this
    rw [abs_of_nonpos hcle]
  · have hxnn : 0 ≤ x := not_lt.mp h
    unfold Ztrunc; rw [if_neg h, abs_of_nonneg hxnn]
    have hfnn : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hxnn
    rw [abs_of_nonneg hfnn]

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

/-- `|x| < β^(mag β x)`. -/
theorem bpow_mag_gt (beta : radix) (x : ℝ) : |x| < bpow beta (mag beta x) := by
  by_cases hx : x = 0
  · rw [hx, abs_zero, mag_zero, bpow_zero]; exact zero_lt_one
  · unfold mag bpow
    rw [if_neg hx]
    have hbeta : 1 < beta.val.toNat := by have := beta.prop; omega
    have hxpos : 0 < |x| := abs_pos.mpr hx
    have h := Int.lt_zpow_succ_log_self (b := beta.val.toNat) hbeta |x|
    rwa [natCast_toNat_val beta] at h

/-- `β^(mag β x - 1) ≤ |x|` for `x ≠ 0`. -/
theorem bpow_mag_le (beta : radix) {x : ℝ} (hx : x ≠ 0) :
    bpow beta (mag beta x - 1) ≤ |x| := by
  unfold mag bpow
  rw [if_neg hx]
  have hbeta : 1 < beta.val.toNat := by have := beta.prop; omega
  have hxpos : 0 < |x| := abs_pos.mpr hx
  have h := Int.zpow_log_le_self (b := beta.val.toNat) hbeta hxpos
  rw [natCast_toNat_val beta] at h
  have heq : Int.log beta.val.toNat |x| + 1 - 1 = Int.log beta.val.toNat |x| := by ring
  rw [heq]
  exact h

/-- If `|x| < β^e` and `x ≠ 0`, then `mag β x ≤ e`. -/
theorem mag_le_bpow (beta : radix) {x : ℝ} {e : ℤ}
    (hx : x ≠ 0) (h : |x| < bpow beta e) : mag beta x ≤ e := by
  have h_chain : bpow beta (mag beta x - 1) < bpow beta e :=
    lt_of_le_of_lt (bpow_mag_le beta hx) h
  have := lt_bpow beta h_chain
  omega

/-- If `β^e ≤ |x|`, then `e < mag β x`. -/
theorem mag_gt_bpow (beta : radix) {x : ℝ} {e : ℤ}
    (h : bpow beta e ≤ |x|) : e < mag beta x := by
  have h_high : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
  exact lt_bpow beta (lt_of_le_of_lt h h_high)

/-- If `β^(e-1) ≤ |x|`, then `e ≤ mag β x`. -/
theorem mag_ge_bpow (beta : radix) {x : ℝ} {e : ℤ}
    (h : bpow beta (e - 1) ≤ |x|) : e ≤ mag beta x := by
  rcases lt_or_ge (|x|) (bpow beta e) with h_lt | h_le
  · have heq : mag beta x = e := mag_unique beta h h_lt
    rw [heq]
  · exact le_of_lt (mag_gt_bpow beta h_le)

/-- `mag` is monotone in absolute value (when `x ≠ 0`). -/
theorem mag_le_abs (beta : radix) {x y : ℝ} (hx : x ≠ 0) (h : |x| ≤ |y|) :
    mag beta x ≤ mag beta y :=
  mag_ge_bpow beta (le_trans (bpow_mag_le beta hx) h)

/-- `mag` from a bound on positive `x`. -/
theorem mag_unique_pos (beta : radix) {x : ℝ} {e : ℤ}
    (h_low : bpow beta (e - 1) ≤ x) (h_high : x < bpow beta e) :
    mag beta x = e := by
  have hxpos : 0 < x := lt_of_lt_of_le (bpow_gt_0 _ _) h_low
  apply mag_unique
  · rw [abs_of_pos hxpos]; exact h_low
  · rw [abs_of_pos hxpos]; exact h_high

/-- `mag β (β^e) = e + 1`. -/
theorem mag_bpow (beta : radix) (e : ℤ) : mag beta (bpow beta e) = e + 1 := by
  apply mag_unique
  · rw [abs_of_pos (bpow_gt_0 beta e)]
    have : e - 1 + 1 = e := by ring
    calc bpow beta (e + 1 - 1) = bpow beta e := by rw [show e + 1 - 1 = e from by ring]
      _ ≤ bpow beta e := le_refl _
  · rw [abs_of_pos (bpow_gt_0 beta e)]
    exact bpow_lt beta (by omega : e < e + 1)

/-- `mag β 1 = 1`. -/
theorem mag_1 (beta : radix) : mag beta 1 = 1 := by
  have := mag_bpow beta 0
  rwa [bpow_zero] at this

/-- `mag β (x · β^e) = mag β x + e` for `x ≠ 0`. -/
theorem mag_mult_bpow (beta : radix) {x : ℝ} (hx : x ≠ 0) (e : ℤ) :
    mag beta (x * bpow beta e) = mag beta x + e := by
  apply mag_unique beta
  · have h_low := bpow_mag_le beta hx
    rw [abs_mul, abs_of_pos (bpow_gt_0 beta e)]
    calc bpow beta (mag beta x + e - 1)
        = bpow beta (mag beta x - 1) * bpow beta e := by
          rw [← bpow_plus]; congr 1; ring
      _ ≤ |x| * bpow beta e :=
          mul_le_mul_of_nonneg_right h_low (bpow_ge_0 _ _)
  · have h_high := bpow_mag_gt beta x
    rw [abs_mul, abs_of_pos (bpow_gt_0 beta e)]
    calc |x| * bpow beta e
        < bpow beta (mag beta x) * bpow beta e :=
          mul_lt_mul_of_pos_right h_high (bpow_gt_0 _ _)
      _ = bpow beta (mag beta x + e) := by rw [← bpow_plus]

/-- `mag β (x*y) ∈ {mag β x + mag β y - 1, mag β x + mag β y}` for nonzero `x`, `y`. -/
theorem mag_mult (beta : radix) {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    mag beta x + mag beta y - 1 ≤ mag beta (x * y)
    ∧ mag beta (x * y) ≤ mag beta x + mag beta y := by
  have h_x_low : bpow beta (mag beta x - 1) ≤ |x| := bpow_mag_le beta hx
  have h_x_high : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
  have h_y_low : bpow beta (mag beta y - 1) ≤ |y| := bpow_mag_le beta hy
  have h_y_high : |y| < bpow beta (mag beta y) := bpow_mag_gt beta y
  have h_x_abs_nn : 0 ≤ |x| := abs_nonneg x
  have h_y_abs_nn : 0 ≤ |y| := abs_nonneg y
  have h_bpow_x_nn : 0 ≤ bpow beta (mag beta x - 1) := bpow_ge_0 _ _
  have h_bpow_y_nn : 0 ≤ bpow beta (mag beta y - 1) := bpow_ge_0 _ _
  -- bpow(mag x + mag y - 1 - 1) ≤ |x * y|
  have h_low : bpow beta (mag beta x + mag beta y - 1 - 1) ≤ |x * y| := by
    rw [abs_mul]
    have h_split : mag beta x + mag beta y - 1 - 1
        = (mag beta x - 1) + (mag beta y - 1) := by ring
    rw [h_split, bpow_plus]
    exact mul_le_mul h_x_low h_y_low h_bpow_y_nn h_x_abs_nn
  -- |x * y| < bpow(mag x + mag y)
  have h_high : |x * y| < bpow beta (mag beta x + mag beta y) := by
    rw [abs_mul, bpow_plus]
    exact mul_lt_mul'' h_x_high h_y_high h_x_abs_nn h_y_abs_nn
  have h_xy_ne : x * y ≠ 0 := mul_ne_zero hx hy
  refine ⟨?_, ?_⟩
  · have h := mag_ge_bpow beta (e := mag beta x + mag beta y - 1) h_low
    linarith
  · exact mag_le_bpow beta h_xy_ne h_high

/-- `mag β (√x) = ⌊(mag β x + 1) / 2⌋` for `0 < x`. -/
theorem mag_sqrt (beta : radix) {x : ℝ} (hx : 0 < x) :
    mag beta (Real.sqrt x) = (mag beta x + 1) / 2 := by
  set n := mag beta x with hn
  set k := (n + 1) / 2 with hk
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_x_lower : bpow beta (n - 1) ≤ |x| := bpow_mag_le beta hx_ne
  have h_x_upper : |x| < bpow beta n := bpow_mag_gt beta x
  have h_x_pos_abs : |x| = x := abs_of_pos hx
  rw [h_x_pos_abs] at h_x_lower h_x_upper
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h_sqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt h_sqrt_pos
  apply mag_unique_pos
  · -- bpow(k - 1) ≤ sqrt x
    -- ↔ bpow(k - 1)^2 ≤ x  (since both sides nonneg)
    -- bpow(k-1)^2 = bpow(2(k-1)) = bpow(2k - 2)
    rw [show (k : ℤ) - 1 = k - 1 from rfl]
    have h_sq_eq : bpow beta (k - 1) ^ 2 = bpow beta (2 * (k - 1)) := by
      rw [show (2 : ℤ) * (k - 1) = (k - 1) + (k - 1) from by ring, bpow_plus, sq]
    rw [show (Real.sqrt x) = Real.sqrt x from rfl]
    rw [show bpow beta (k - 1) = Real.sqrt (bpow beta (k - 1) ^ 2) from
        (Real.sqrt_sq (le_of_lt (bpow_gt_0 beta _))).symm]
    apply Real.sqrt_le_sqrt
    rw [h_sq_eq]
    -- 2(k-1) ≤ n - 1: we have k = (n+1)/2 (integer div)
    have h_2k_le : 2 * (k - 1) ≤ n - 1 := by
      have h_2k : 2 * k ≤ n + 1 := by
        rw [hk]; omega
      omega
    exact le_trans (bpow_le beta h_2k_le) h_x_lower
  · -- sqrt x < bpow(k)
    rw [show Real.sqrt x = Real.sqrt x from rfl]
    rw [show bpow beta k = Real.sqrt (bpow beta k ^ 2) from
        (Real.sqrt_sq (le_of_lt (bpow_gt_0 beta _))).symm]
    apply Real.sqrt_lt_sqrt (le_of_lt hx)
    have h_sq_eq : bpow beta k ^ 2 = bpow beta (2 * k) := by
      rw [show (2 : ℤ) * k = k + k from by ring, bpow_plus, sq]
    rw [h_sq_eq]
    have h_2k_ge : n ≤ 2 * k := by
      rw [hk]; omega
    exact lt_of_lt_of_le h_x_upper (bpow_le beta h_2k_ge)

/-- `mag β (x / y)` is between `mag β x - mag β y` and `mag β x - mag β y + 1`. -/
theorem mag_div (beta : radix) {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    mag beta x - mag beta y ≤ mag beta (x / y) ∧
      mag beta (x / y) ≤ mag beta x - mag beta y + 1 := by
  have h_y_pos : 0 < |y| := abs_pos.mpr hy
  have h_y_ne : |y| ≠ 0 := ne_of_gt h_y_pos
  have h_y_lower : bpow beta (mag beta y - 1) ≤ |y| := bpow_mag_le beta hy
  have h_y_upper : |y| < bpow beta (mag beta y) := bpow_mag_gt beta y
  have h_x_lower : bpow beta (mag beta x - 1) ≤ |x| := bpow_mag_le beta hx
  have h_x_upper : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
  have h_bpow_y : 0 < bpow beta (mag beta y) := bpow_gt_0 _ _
  have h_bpow_y_lower : 0 < bpow beta (mag beta y - 1) := bpow_gt_0 _ _
  refine ⟨?_, ?_⟩
  · -- bpow(mag x - mag y - 1) ≤ |x/y|, then mag_ge_bpow.
    apply mag_ge_bpow beta
    rw [abs_div]
    rw [le_div_iff₀ h_y_pos]
    -- Goal: bpow(mag x - mag y - 1) * |y| ≤ |x|
    calc bpow beta (mag beta x - mag beta y - 1) * |y|
        ≤ bpow beta (mag beta x - mag beta y - 1) * bpow beta (mag beta y) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt h_y_upper)
          exact bpow_ge_0 _ _
      _ = bpow beta (mag beta x - 1) := by
          rw [← bpow_plus]; congr 1; ring
      _ ≤ |x| := h_x_lower
  · apply mag_le_bpow beta (div_ne_zero hx hy)
    rw [abs_div]
    rw [div_lt_iff₀ h_y_pos]
    -- Goal: |x| < bpow(mag x - mag y + 1) * |y|
    calc |x|
        < bpow beta (mag beta x) := h_x_upper
      _ = bpow beta (mag beta x - mag beta y + 1) * bpow beta (mag beta y - 1) := by
          rw [← bpow_plus]; congr 1; ring
      _ ≤ bpow beta (mag beta x - mag beta y + 1) * |y| := by
          apply mul_le_mul_of_nonneg_left h_y_lower
          exact bpow_ge_0 _ _

end LeanFlocq
