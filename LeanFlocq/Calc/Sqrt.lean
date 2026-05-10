/-
Port of `flocq/src/Calc/Sqrt.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Helper functions and theorems for computing the rounded square root of
a floating-point number. Produces a triple `(m, e, l)` where `m` is
an integer mantissa at exponent `e`, with location `l` indicating
whether the residue is below, at, or above the midpoint.
-/

import LeanFlocq.Calc.Bracket
import LeanFlocq.Core.Generic_fmt
import Mathlib.Data.Int.Sqrt

namespace LeanFlocq

variable (beta : radix) (fexp : ℤ → ℤ)

/-! ## Magnitude of a square root of `F2R` -/

/-- `mag β (√(F2R⟨m1, e1⟩)) = (Zdigits m1 + e1 + 1) / 2`. -/
theorem mag_sqrt_F2R (m1 e1 : ℤ) (Hm1 : 0 < m1) :
    mag beta (Real.sqrt (F2R (beta := beta) ⟨m1, e1⟩))
      = (Zdigits beta m1 + e1 + 1) / 2 := by
  have hm1_ne : m1 ≠ 0 := by linarith
  have h_F_pos : 0 < F2R (beta := beta) ⟨m1, e1⟩ := F2R_gt_0 ⟨m1, e1⟩ Hm1
  have h_mag_F : mag beta (F2R (beta := beta) ⟨m1, e1⟩) = Zdigits beta m1 + e1 :=
    mag_F2R_Zdigits (beta := beta) m1 e1 hm1_ne
  rw [mag_sqrt beta h_F_pos, h_mag_F]

/-! ## Fsqrt_core -/

/-- The integer-square-root remainder predicate: `q*q + r = m` and `r ≤ 2q`. -/
private theorem int_sqrtrem (m : ℤ) (Hm : 0 ≤ m) :
    let q := Int.sqrt m
    q * q ≤ m ∧ m < (q + 1) * (q + 1) ∧ 0 ≤ q := by
  refine ⟨?_, ?_, Int.sqrt_nonneg m⟩
  · show Int.sqrt m * Int.sqrt m ≤ m
    have h_nat : Nat.sqrt m.toNat * Nat.sqrt m.toNat ≤ m.toNat := Nat.sqrt_le m.toNat
    have h_lift : ((Nat.sqrt m.toNat * Nat.sqrt m.toNat : ℕ) : ℤ) ≤ ((m.toNat : ℕ) : ℤ) :=
      Int.ofNat_le.mpr h_nat
    rw [Int.toNat_of_nonneg Hm] at h_lift
    have h_lhs : Int.sqrt m * Int.sqrt m
        = ((Nat.sqrt m.toNat * Nat.sqrt m.toNat : ℕ) : ℤ) := by
      show (Nat.sqrt m.toNat : ℤ) * (Nat.sqrt m.toNat : ℤ) = _
      push_cast; ring
    rw [h_lhs]; exact h_lift
  · show m < (Int.sqrt m + 1) * (Int.sqrt m + 1)
    have h_nat : m.toNat < (Nat.sqrt m.toNat + 1) * (Nat.sqrt m.toNat + 1) := Nat.lt_succ_sqrt m.toNat
    have h_lift : ((m.toNat : ℕ) : ℤ) < (((Nat.sqrt m.toNat + 1) * (Nat.sqrt m.toNat + 1) : ℕ) : ℤ) :=
      Int.ofNat_lt.mpr h_nat
    rw [Int.toNat_of_nonneg Hm] at h_lift
    have h_rhs : (Int.sqrt m + 1) * (Int.sqrt m + 1)
        = (((Nat.sqrt m.toNat + 1) * (Nat.sqrt m.toNat + 1) : ℕ) : ℤ) := by
      show ((Nat.sqrt m.toNat : ℤ) + 1) * ((Nat.sqrt m.toNat : ℤ) + 1) = _
      push_cast; ring
    rw [h_rhs]; exact h_lift

/-- `Fsqrt_core m1 e1 e`: returns `(q, l)` where `q = ⌊sqrt(m1 * β^(e1-2e))⌋`
and `l` indicates the residue position. -/
noncomputable def Fsqrt_core (m1 e1 e : ℤ) : ℤ × location :=
  let m1' := m1 * (beta.val : ℤ) ^ (e1 - 2 * e).toNat
  let q := Int.sqrt m1'
  let r := m1' - q * q
  let l :=
    if r = 0 then location.Exact
    else if r ≤ q then location.Inexact .lt
    else location.Inexact .gt
  (q, l)

/-- Correctness of `Fsqrt_core`: brackets `√(F2R⟨m1, e1⟩)` at exponent `e`. -/
theorem Fsqrt_core_correct (m1 e1 e : ℤ) (Hm1 : 0 < m1) (He : 2 * e ≤ e1) :
    let r := Fsqrt_core beta m1 e1 e
    inbetween_float beta r.1 e (Real.sqrt (F2R (beta := beta) ⟨m1, e1⟩)) r.2 := by
  unfold Fsqrt_core
  set m' := m1 * (beta.val : ℤ) ^ (e1 - 2 * e).toNat with hm'_def
  have hd : 0 ≤ e1 - 2 * e := by omega
  have h_pow_pos : 0 < (beta.val : ℤ) ^ (e1 - 2 * e).toNat := pow_pos beta.radix_gt_0 _
  have h_m'_pos : 0 < m' := mul_pos Hm1 h_pow_pos
  have h_m'_nn : 0 ≤ m' := le_of_lt h_m'_pos
  have h_m'_real_pos : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast h_m'_pos
  have h_m'_real_nn : (0 : ℝ) ≤ (m' : ℝ) := le_of_lt h_m'_real_pos
  -- sqrt(F2R⟨m1, e1⟩) = sqrt(m') * bpow(e)
  have h_sqrt_eq : Real.sqrt (F2R (beta := beta) ⟨m1, e1⟩)
      = Real.sqrt (m' : ℝ) * bpow beta e := by
    have h_F_form : F2R (beta := beta) ⟨m1, e1⟩ = (m' : ℝ) * (bpow beta e * bpow beta e) := by
      show (m1 : ℝ) * bpow beta e1 = (m' : ℝ) * (bpow beta e * bpow beta e)
      have h_pow_real : (((beta.val : ℤ) ^ (e1 - 2 * e).toNat : ℤ) : ℝ) = bpow beta (e1 - 2 * e) :=
        IZR_Zpower beta hd
      have h_split : bpow beta e1 = bpow beta (e1 - 2 * e) * (bpow beta e * bpow beta e) := by
        rw [← bpow_plus, ← bpow_plus]
        congr 1; ring
      rw [h_split]
      show (m1 : ℝ) * (bpow beta (e1 - 2 * e) * (bpow beta e * bpow beta e))
          = ((m1 * (beta.val : ℤ) ^ (e1 - 2 * e).toNat : ℤ) : ℝ) * (bpow beta e * bpow beta e)
      rw [show ((m1 * (beta.val : ℤ) ^ (e1 - 2 * e).toNat : ℤ) : ℝ)
          = (m1 : ℝ) * (((beta.val : ℤ) ^ (e1 - 2 * e).toNat : ℤ) : ℝ) from by push_cast; ring]
      rw [h_pow_real]; ring
    rw [h_F_form]
    rw [Real.sqrt_mul h_m'_real_nn]
    have h_bpow_nn : (0 : ℝ) ≤ bpow beta e := bpow_ge_0 beta e
    rw [show bpow beta e * bpow beta e = (bpow beta e) ^ 2 from by ring,
        Real.sqrt_sq h_bpow_nn]
  rw [h_sqrt_eq]
  -- Now: inbetween_float β q e (sqrt(m') * bpow e) location.
  -- inbetween_float = inbetween (q * bpow e) ((q+1) * bpow e) (sqrt m' * bpow e) loc.
  -- Lift via inbetween_mult_compat from inbetween q (q+1) (sqrt m') loc.
  set q := Int.sqrt m' with hq_def
  set r := m' - q * q with hr_def
  have h_sq := int_sqrtrem m' h_m'_nn
  obtain ⟨h_qsq_le, h_lt_q1sq, h_q_nn⟩ := h_sq
  have h_r_nn : 0 ≤ r := by rw [hr_def]; linarith
  have h_r_lt_2q1 : r < 2 * q + 1 := by
    rw [hr_def]
    have : (q + 1) * (q + 1) = q * q + (2 * q + 1) := by ring
    linarith
  have h_q_real_nn : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h_q_nn
  have h_qq_real_nn : (0 : ℝ) ≤ ((q * q : ℤ) : ℝ) := by exact_mod_cast (mul_self_nonneg q)
  have h_q1q1_nn : (0 : ℝ) ≤ (((q + 1) * (q + 1) : ℤ) : ℝ) := by
    exact_mod_cast (mul_self_nonneg (q + 1))
  unfold inbetween_float
  show inbetween ((q : ℝ) * bpow beta e) (((q + 1 : ℤ) : ℝ) * bpow beta e)
        (Real.sqrt (m' : ℝ) * bpow beta e) _
  rw [show (((q + 1 : ℤ)) : ℝ) = (q : ℝ) + 1 from by push_cast; rfl]
  -- Step: the location depends on r. Let me get the inner inbetween (q : ℝ) (q+1) (sqrt m').
  have h_sqrt_lower : (q : ℝ) ≤ Real.sqrt (m' : ℝ) := by
    have h_qq_le : ((q * q : ℤ) : ℝ) ≤ (m' : ℝ) := by exact_mod_cast h_qsq_le
    have h_sqrt_le : Real.sqrt (((q * q : ℤ) : ℝ)) ≤ Real.sqrt (m' : ℝ) :=
      Real.sqrt_le_sqrt h_qq_le
    have h_sqrt_qq : Real.sqrt (((q * q : ℤ) : ℝ)) = (q : ℝ) := by
      have : (((q * q : ℤ) : ℝ)) = (q : ℝ) ^ 2 := by push_cast; ring
      rw [this, Real.sqrt_sq h_q_real_nn]
    rw [h_sqrt_qq] at h_sqrt_le
    exact h_sqrt_le
  have h_sqrt_upper : Real.sqrt (m' : ℝ) < (q : ℝ) + 1 := by
    have h_lt : (m' : ℝ) < ((q + 1 : ℤ) : ℝ) * ((q + 1 : ℤ) : ℝ) := by
      have h_int : (m' : ℤ) < (q + 1) * (q + 1) := h_lt_q1sq
      have : ((q + 1) * (q + 1) : ℤ) = ((q + 1 : ℤ)) * ((q + 1 : ℤ)) := by ring
      exact_mod_cast h_int
    have h_q1_nn : (0 : ℝ) ≤ ((q + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    have h_sqrt_lt : Real.sqrt (m' : ℝ) < ((q + 1 : ℤ) : ℝ) := by
      have h_sqrt_sq_q1 : Real.sqrt (((q + 1 : ℤ) : ℝ) * ((q + 1 : ℤ) : ℝ)) = ((q + 1 : ℤ) : ℝ) := by
        rw [show ((q + 1 : ℤ) : ℝ) * ((q + 1 : ℤ) : ℝ) = ((q + 1 : ℤ) : ℝ) ^ 2 from by ring]
        exact Real.sqrt_sq h_q1_nn
      have := Real.sqrt_lt_sqrt h_m'_real_nn h_lt
      rw [h_sqrt_sq_q1] at this
      exact this
    have : ((q + 1 : ℤ) : ℝ) = (q : ℝ) + 1 := by push_cast; rfl
    linarith [h_sqrt_lt]
  -- Now build the inbetween at unit scale.
  have h_inbetween_unit : inbetween (q : ℝ) ((q : ℝ) + 1) (Real.sqrt (m' : ℝ))
      (if r = 0 then location.Exact else if r ≤ q then location.Inexact .lt
       else location.Inexact .gt) := by
    by_cases hr0 : r = 0
    · -- r = 0: m' = q*q so sqrt m' = q
      simp only [if_pos hr0]
      have h_m_eq_qq : (m' : ℝ) = (q : ℝ) * (q : ℝ) := by
        have h_int_eq : m' = q * q := by linarith [hr0]
        have : ((m' : ℤ) : ℝ) = ((q * q : ℤ) : ℝ) := by exact_mod_cast h_int_eq
        push_cast at this; linarith
      rw [h_m_eq_qq, show (q : ℝ) * (q : ℝ) = (q : ℝ) ^ 2 from by ring,
          Real.sqrt_sq h_q_real_nn]
      exact .Exact rfl
    · simp only [if_neg hr0]
      -- r ≠ 0: sqrt m' is strictly between q and q+1.
      have h_sqrt_strict_lo : (q : ℝ) < Real.sqrt (m' : ℝ) := by
        rcases lt_or_eq_of_le h_sqrt_lower with h | h
        · exact h
        · -- equality case impossible: sqrt m' = q ↔ m' = q^2 ↔ r = 0
          exfalso
          apply hr0
          have h_eq : Real.sqrt (m' : ℝ) = (q : ℝ) := h.symm
          have h_sq : Real.sqrt (m' : ℝ) ^ 2 = (q : ℝ) ^ 2 := by rw [h_eq]
          rw [Real.sq_sqrt h_m'_real_nn] at h_sq
          have h_m'_eq : (m' : ℝ) = ((q * q : ℤ) : ℝ) := by
            rw [h_sq]; push_cast; ring
          have : m' = q * q := by exact_mod_cast h_m'_eq
          linarith [hr_def]
      -- Compare (sqrt m') with the midpoint (q + (q+1))/2 = q + 1/2.
      -- midpoint = (2q + 1) / 2; we have m' = q*q + r, so sqrt m' compared to (2q+1)/2.
      -- (sqrt m')^2 = q*q + r;  ((2q+1)/2)^2 = (4q^2 + 4q + 1) / 4.
      -- Compare 4(q*q + r) with 4q^2 + 4q + 1 = 4(q*q + q) + 1.
      -- Difference: 4r vs 4q + 1.
      -- r ≤ q ⟺ 4r ≤ 4q < 4q + 1, so 4(qq+r) < 4qq + 4q + 1, so (sqrt m')^2 < midpoint^2, so sqrt m' < midpoint.
      -- r > q ⟺ 4r ≥ 4q + 4 > 4q + 1, so (sqrt m')^2 > midpoint^2, so sqrt m' > midpoint.
      have h_mid : (((q : ℝ) + ((q : ℝ) + 1)) / 2) = (q : ℝ) + 1/2 := by ring
      have h_sqrt_pos : 0 < Real.sqrt (m' : ℝ) := lt_of_le_of_lt h_q_real_nn h_sqrt_strict_lo
      have h_mid_pos : (0 : ℝ) < (q : ℝ) + 1/2 := by linarith
      have h_sqrt_sq : Real.sqrt (m' : ℝ) ^ 2 = (m' : ℝ) := Real.sq_sqrt h_m'_real_nn
      have h_m'_real_eq : (m' : ℝ) = ((q : ℝ) * (q : ℝ)) + (r : ℝ) := by
        have h_int_eq : m' = q * q + r := by linarith [hr_def]
        have : ((m' : ℤ) : ℝ) = ((q * q + r : ℤ) : ℝ) := by exact_mod_cast h_int_eq
        push_cast at this; linarith
      by_cases hrq : r ≤ q
      · simp only [if_pos hrq]
        refine .Inexact .lt h_sqrt_strict_lo h_sqrt_upper ?_
        rw [h_mid]
        apply compare_lt_iff_lt.mpr
        -- sqrt m' < q + 1/2: square both sides (both positive).
        have h_sq_lt : Real.sqrt (m' : ℝ) ^ 2 < ((q : ℝ) + 1/2) ^ 2 := by
          rw [h_sqrt_sq, h_m'_real_eq]
          have : ((q : ℝ) + 1/2) ^ 2 = (q : ℝ) * (q : ℝ) + (q : ℝ) + 1/4 := by ring
          rw [this]
          have h_r_real : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
          linarith
        exact lt_of_pow_lt_pow_left₀ 2 (by linarith) h_sq_lt
      · simp only [if_neg hrq]
        push_neg at hrq
        -- r > q means r ≥ q + 1
        have hrq' : q + 1 ≤ r := by omega
        refine .Inexact .gt h_sqrt_strict_lo h_sqrt_upper ?_
        rw [h_mid]
        apply compare_gt_iff_gt.mpr
        have h_sq_gt : ((q : ℝ) + 1/2) ^ 2 < Real.sqrt (m' : ℝ) ^ 2 := by
          rw [h_sqrt_sq, h_m'_real_eq]
          have : ((q : ℝ) + 1/2) ^ 2 = (q : ℝ) * (q : ℝ) + (q : ℝ) + 1/4 := by ring
          rw [this]
          have h_r_real : (q : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hrq'
          linarith
        exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt h_sqrt_pos) h_sq_gt
  -- Apply inbetween_mult_compat to lift by bpow e.
  exact inbetween_mult_compat (q : ℝ) ((q : ℝ) + 1) (Real.sqrt (m' : ℝ))
    _ (bpow beta e) (bpow_gt_0 beta e) h_inbetween_unit

/-! ## The full Fsqrt -/

/-- Compute the rounded square root of a float: returns (mantissa, exponent, location). -/
noncomputable def Fsqrt (x : float beta) : ℤ × ℤ × location :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let e' := Zdigits beta m1 + e1 + 1
  let e := min (fexp (e' / 2)) (e1 / 2)
  let r := Fsqrt_core beta m1 e1 e
  (r.1, e, r.2)

/-- Correctness of `Fsqrt`: bracketing at exponent ≤ canonical exponent of √x. -/
theorem Fsqrt_correct (x : float beta) (Hx : 0 < F2R x) :
    let r := Fsqrt beta fexp x
    r.2.1 ≤ cexp beta fexp (Real.sqrt (F2R x)) ∧
    inbetween_float beta r.1 r.2.1 (Real.sqrt (F2R x)) r.2.2 := by
  unfold Fsqrt
  cases x with | mk m1 e1 =>
  have hm1 : 0 < m1 := gt_0_F2R Hx
  set e' := Zdigits beta m1 + e1 + 1 with he'_def
  set e := min (fexp (e' / 2)) (e1 / 2) with he_def
  have h_2e_le : 2 * e ≤ e1 := by
    have h_e_le_div2 : e ≤ e1 / 2 := min_le_right _ _
    omega
  have h_core := Fsqrt_core_correct beta m1 e1 e hm1 h_2e_le
  refine ⟨?_, h_core⟩
  show e ≤ fexp (mag beta (Real.sqrt (F2R (beta := beta) ⟨m1, e1⟩)))
  rw [mag_sqrt_F2R beta m1 e1 hm1]
  rw [show Zdigits beta m1 + e1 + 1 = e' from rfl]
  exact min_le_left _ _

end LeanFlocq
