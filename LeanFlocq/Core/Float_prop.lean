/-
Port of `flocq/src/Core/Float_prop.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Basic algebraic properties of floating-point formats: comparing F2R values,
sign facts, behaviour under negation/absolute value.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFlocq.Core.Defs

namespace LeanFlocq

variable {beta : radix}

/-! ### Comparison: ordering on the mantissa transfers to F2R -/

theorem F2R_le {m1 m2 e : ℤ} (h : m1 ≤ m2) :
    F2R (beta := beta) ⟨m1, e⟩ ≤ F2R (beta := beta) ⟨m2, e⟩ := by
  unfold F2R
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (bpow_ge_0 beta e)

theorem F2R_lt {m1 m2 e : ℤ} (h : m1 < m2) :
    F2R (beta := beta) ⟨m1, e⟩ < F2R (beta := beta) ⟨m2, e⟩ := by
  unfold F2R
  exact (mul_lt_mul_iff_of_pos_right (bpow_gt_0 beta e)).mpr (by exact_mod_cast h)

theorem le_F2R {m1 m2 e : ℤ}
    (h : F2R (beta := beta) ⟨m1, e⟩ ≤ F2R (beta := beta) ⟨m2, e⟩) :
    m1 ≤ m2 := by
  by_contra hlt
  push_neg at hlt
  exact absurd (F2R_lt (beta := beta) (e := e) hlt) (not_lt.mpr h)

theorem lt_F2R {m1 m2 e : ℤ}
    (h : F2R (beta := beta) ⟨m1, e⟩ < F2R (beta := beta) ⟨m2, e⟩) :
    m1 < m2 := by
  by_contra hle
  push_neg at hle
  exact absurd (F2R_le (beta := beta) (e := e) hle) (not_le.mpr h)

theorem F2R_eq {m1 m2 e : ℤ} (h : m1 = m2) :
    F2R (beta := beta) ⟨m1, e⟩ = F2R (beta := beta) ⟨m2, e⟩ := by
  rw [h]

theorem eq_F2R {m1 m2 e : ℤ}
    (h : F2R (beta := beta) ⟨m1, e⟩ = F2R (beta := beta) ⟨m2, e⟩) :
    m1 = m2 :=
  le_antisymm (le_F2R (beta := beta) (e := e) (le_of_eq h))
              (le_F2R (beta := beta) (e := e) (le_of_eq h.symm))

/-! ### Negation and absolute value -/

theorem F2R_Zopp (m e : ℤ) :
    F2R (beta := beta) ⟨-m, e⟩ = -F2R (beta := beta) ⟨m, e⟩ := by
  unfold F2R; push_cast; ring

theorem F2R_Zabs (m e : ℤ) :
    F2R (beta := beta) ⟨|m|, e⟩ = |F2R (beta := beta) ⟨m, e⟩| := by
  unfold F2R
  rw [abs_mul, abs_of_nonneg (bpow_ge_0 beta e)]
  push_cast
  rfl

/-! ### Sign facts -/

@[simp]
theorem F2R_0 (e : ℤ) : F2R (beta := beta) ⟨0, e⟩ = 0 := by
  unfold F2R; simp

theorem eq_0_F2R {m e : ℤ}
    (h : F2R (beta := beta) ⟨m, e⟩ = 0) : m = 0 := by
  apply eq_F2R (beta := beta) (e := e)
  rw [h, F2R_0]

theorem ge_0_F2R {m e : ℤ}
    (h : 0 ≤ F2R (beta := beta) ⟨m, e⟩) : 0 ≤ m := by
  apply le_F2R (beta := beta) (e := e)
  rwa [F2R_0]

theorem le_0_F2R {m e : ℤ}
    (h : F2R (beta := beta) ⟨m, e⟩ ≤ 0) : m ≤ 0 := by
  apply le_F2R (beta := beta) (e := e)
  rwa [F2R_0]

theorem gt_0_F2R {m e : ℤ}
    (h : 0 < F2R (beta := beta) ⟨m, e⟩) : 0 < m := by
  apply lt_F2R (beta := beta) (e := e)
  rwa [F2R_0]

theorem lt_0_F2R {m e : ℤ}
    (h : F2R (beta := beta) ⟨m, e⟩ < 0) : m < 0 := by
  apply lt_F2R (beta := beta) (e := e)
  rwa [F2R_0]

theorem F2R_ge_0 (f : float beta) (h : 0 ≤ f.Fnum) : 0 ≤ F2R f := by
  have := F2R_le (beta := beta) (e := f.Fexp) (m1 := 0) (m2 := f.Fnum) h
  rwa [F2R_0] at this

theorem F2R_le_0 (f : float beta) (h : f.Fnum ≤ 0) : F2R f ≤ 0 := by
  have := F2R_le (beta := beta) (e := f.Fexp) (m1 := f.Fnum) (m2 := 0) h
  rwa [F2R_0] at this

theorem F2R_gt_0 (f : float beta) (h : 0 < f.Fnum) : 0 < F2R f := by
  have := F2R_lt (beta := beta) (e := f.Fexp) (m1 := 0) (m2 := f.Fnum) h
  rwa [F2R_0] at this

theorem F2R_lt_0 (f : float beta) (h : f.Fnum < 0) : F2R f < 0 := by
  have := F2R_lt (beta := beta) (e := f.Fexp) (m1 := f.Fnum) (m2 := 0) h
  rwa [F2R_0] at this

theorem F2R_neq_0 (f : float beta) (h : f.Fnum ≠ 0) : F2R f ≠ 0 := by
  intro heq
  exact h (eq_0_F2R (beta := beta) (e := f.Fexp) heq)

theorem Fnum_ge_0 (f : float beta) (h : 0 ≤ F2R f) : 0 ≤ f.Fnum := by
  by_contra hlt
  push_neg at hlt
  exact absurd (F2R_lt_0 f hlt) (not_lt.mpr h)

theorem Fnum_le_0 (f : float beta) (h : F2R f ≤ 0) : f.Fnum ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  exact absurd (F2R_gt_0 f hlt) (not_lt.mpr h)

/-! ### Floats and `bpow` -/

theorem F2R_bpow (e : ℤ) : F2R (beta := beta) ⟨1, e⟩ = bpow beta e := by
  unfold F2R; simp

theorem bpow_le_F2R {m e : ℤ} (h : 0 < m) :
    bpow beta e ≤ F2R (beta := beta) ⟨m, e⟩ := by
  rw [← F2R_bpow]
  exact F2R_le (by omega)

/-- Changing the exponent of a float, scaling the mantissa to compensate. -/
theorem F2R_change_exp (e' m e : ℤ) (h : e' ≤ e) :
    F2R (beta := beta) ⟨m, e⟩
      = F2R (beta := beta) ⟨m * (beta.val : ℤ) ^ (e - e').toNat, e'⟩ := by
  unfold F2R
  have hd : 0 ≤ e - e' := by omega
  have htn : ((e - e').toNat : ℤ) = e - e' := Int.toNat_of_nonneg hd
  have hbpow : bpow beta e = (beta.val : ℝ) ^ (e - e').toNat * bpow beta e' := by
    have hsplit : bpow beta e = bpow beta (e - e') * bpow beta e' := by
      rw [← bpow_plus]; congr 1; ring
    rw [hsplit]
    congr 1
    unfold bpow
    rw [show (e - e' : ℤ) = ((e - e').toNat : ℤ) from htn.symm]
    norm_cast
  show (m : ℝ) * bpow beta e
      = ((m * beta.val ^ (e - e').toNat : ℤ) : ℝ) * bpow beta e'
  rw [hbpow, Int.cast_mul, Int.cast_pow]
  ring

end LeanFlocq
