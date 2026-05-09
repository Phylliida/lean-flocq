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

/-- F2R distributes over conditional negation. -/
theorem F2R_cond_Zopp (b : Bool) (m e : ℤ) :
    F2R (beta := beta) ⟨cond_Zopp b m, e⟩ = cond_Ropp b (F2R (beta := beta) ⟨m, e⟩) := by
  cases b
  · rfl
  · show F2R (beta := beta) ⟨-m, e⟩ = -F2R (beta := beta) ⟨m, e⟩
    exact F2R_Zopp m e

/-- Comparison of two F2R values at the same exponent reduces to comparison
of their mantissas. -/
theorem Rcompare_F2R (e m1 m2 : ℤ) :
    compare (F2R (beta := beta) ⟨m1, e⟩) (F2R (beta := beta) ⟨m2, e⟩)
      = compare m1 m2 := by
  rcases lt_trichotomy m1 m2 with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (F2R_lt h)]
  · subst h
    rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (F2R_lt h)]

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

/-- If `m * β^e1 < β^e2` and `m > 0`, then `(m+1) * β^e1 ≤ β^e2`. -/
theorem F2R_p1_le_bpow {m e1 e2 : ℤ} (hm : 0 < m)
    (h : F2R (beta := beta) ⟨m, e1⟩ < bpow beta e2) :
    F2R (beta := beta) ⟨m + 1, e1⟩ ≤ bpow beta e2 := by
  have he : e1 ≤ e2 := le_bpow beta (lt_of_le_of_lt (bpow_le_F2R hm) h).le
  have hd : 0 ≤ e2 - e1 := by omega
  have hβ1 : 0 < bpow beta e1 := bpow_gt_0 beta e1
  have hbpow : bpow beta e2
      = ((beta.val ^ (e2 - e1).toNat : ℤ) : ℝ) * bpow beta e1 := by
    rw [IZR_Zpower beta hd, ← bpow_plus]
    congr 1; omega
  have hmlt : (m : ℝ) < ((beta.val ^ (e2 - e1).toNat : ℤ) : ℝ) := by
    have hh : (m : ℝ) * bpow beta e1
        < ((beta.val ^ (e2 - e1).toNat : ℤ) : ℝ) * bpow beta e1 := by
      rw [← hbpow]; exact h
    exact (mul_lt_mul_iff_of_pos_right hβ1).mp hh
  have hmle : m + 1 ≤ (beta.val ^ (e2 - e1).toNat : ℤ) := by
    have hmlt' : m < (beta.val ^ (e2 - e1).toNat : ℤ) := by exact_mod_cast hmlt
    omega
  show ((m + 1 : ℤ) : ℝ) * bpow beta e1 ≤ bpow beta e2
  rw [hbpow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmle) hβ1.le

/-- If `β^e2 < m * β^e1` and `m > 1`, then `β^e2 ≤ (m-1) * β^e1`. -/
theorem bpow_le_F2R_m1 {m e1 e2 : ℤ} (hm : 1 < m)
    (h : bpow beta e2 < F2R (beta := beta) ⟨m, e1⟩) :
    bpow beta e2 ≤ F2R (beta := beta) ⟨m - 1, e1⟩ := by
  rcases le_or_gt e1 e2 with he | he
  · -- e1 ≤ e2: same general technique as F2R_p1_le_bpow
    have hd : 0 ≤ e2 - e1 := by omega
    have hβ1 : 0 < bpow beta e1 := bpow_gt_0 beta e1
    have hbpow : bpow beta e2
        = ((beta.val ^ (e2 - e1).toNat : ℤ) : ℝ) * bpow beta e1 := by
      rw [IZR_Zpower beta hd, ← bpow_plus]
      congr 1; omega
    have hmlt : ((beta.val ^ (e2 - e1).toNat : ℤ) : ℝ) < (m : ℝ) := by
      have hh : ((beta.val ^ (e2 - e1).toNat : ℤ) : ℝ) * bpow beta e1
          < (m : ℝ) * bpow beta e1 := by
        rw [← hbpow]; exact h
      exact (mul_lt_mul_iff_of_pos_right hβ1).mp hh
    have hmle : (beta.val ^ (e2 - e1).toNat : ℤ) ≤ m - 1 := by
      have : (beta.val ^ (e2 - e1).toNat : ℤ) < m := by exact_mod_cast hmlt
      omega
    show bpow beta e2 ≤ ((m - 1 : ℤ) : ℝ) * bpow beta e1
    rw [hbpow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmle) hβ1.le
  · -- e2 < e1: bpow e2 ≤ bpow e1 ≤ (m-1) * bpow e1
    calc bpow beta e2
        ≤ bpow beta e1 := bpow_le beta (le_of_lt he)
      _ = 1 * bpow beta e1 := (one_mul _).symm
      _ ≤ ((m - 1 : ℤ) : ℝ) * bpow beta e1 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : (1 : ℤ) ≤ m - 1))
                                     (bpow_ge_0 beta e1)

/-- Re-expressing an F2R with bounded mantissa at a chosen exponent based on
its magnitude: if `|m| < β^p` and `bpow(e' - 1) ≤ |F2R ⟨m, e⟩|`, then
`F2R ⟨m, e⟩ = F2R ⟨m * β^(e - e' + p), e' - p⟩`. -/
theorem F2R_prec_normalize (m e e' p : ℤ)
    (Hm : |m| < (beta.val : ℤ) ^ p.toNat)
    (Hf : bpow beta (e' - 1) ≤ |F2R (beta := beta) ⟨m, e⟩|) :
    F2R (beta := beta) ⟨m, e⟩
      = F2R (beta := beta) ⟨m * (beta.val : ℤ) ^ (e - e' + p).toNat, e' - p⟩ := by
  have hp : 0 ≤ p := by
    by_contra hp_neg
    push_neg at hp_neg
    have h_toNat : p.toNat = 0 := by
      have : p ≤ 0 := le_of_lt hp_neg
      omega
    rw [h_toNat, pow_zero] at Hm
    have hm_zero : m = 0 := by
      have h_abs_nn : (0 : ℤ) ≤ |m| := abs_nonneg m
      have h_abs_zero : |m| = 0 := by omega
      exact abs_eq_zero.mp h_abs_zero
    rw [hm_zero, show F2R (beta := beta) ⟨0, e⟩ = 0 from F2R_0 e, abs_zero] at Hf
    exact absurd (lt_of_le_of_lt Hf (bpow_gt_0 _ _)) (lt_irrefl _)
  have h_e'p_le : e' - p ≤ e := by
    have h_chain : bpow beta (e' - 1) < bpow beta (e + p) := by
      calc bpow beta (e' - 1)
          ≤ |F2R (beta := beta) ⟨m, e⟩| := Hf
        _ = ((|m| : ℤ) : ℝ) * bpow beta e := by
            show |((m : ℝ)) * bpow beta e| = ((|m| : ℤ) : ℝ) * bpow beta e
            rw [abs_mul, abs_of_pos (bpow_gt_0 _ _)]; push_cast; rfl
        _ < bpow beta p * bpow beta e := by
            apply mul_lt_mul_of_pos_right _ (bpow_gt_0 _ _)
            rw [← IZR_Zpower beta hp]; exact_mod_cast Hm
        _ = bpow beta (e + p) := by rw [← bpow_plus]; congr 1; ring
    have := lt_bpow beta h_chain; omega
  have h_eq : e - e' + p = e - (e' - p) := by ring
  rw [show (m * (beta.val : ℤ) ^ (e - e' + p).toNat : ℤ)
      = m * (beta.val : ℤ) ^ (e - (e' - p)).toNat from by rw [h_eq]]
  exact F2R_change_exp (e' - p) m e h_e'p_le

/-- If `|m| < β^(e' - e)`, then `|F2R ⟨m, e⟩| < β^e'`.

The hypothesis uses `(e' - e).toNat`; when `e' < e` this evaluates to
`(beta.val : ℤ)^0 = 1`, so the hypothesis forces `m = 0` and the
conclusion is immediate.

**Deviation from Coq:** Coq's `Zpower beta (e' - Fexp f)` returns `0` for
negative argument, making Coq's hypothesis vacuous when `e' < Fexp f`.
The Lean version (using `.toNat`) is therefore strictly *stronger*: it
admits the additional case `m = 0` ∧ `e' < Fexp f` and still concludes
`|F2R| < bpow e'`. -/
theorem F2R_lt_bpow (f : float beta) (e' : ℤ)
    (h : |f.Fnum| < (beta.val : ℤ) ^ (e' - f.Fexp).toNat) :
    |F2R f| < bpow beta e' := by
  rcases le_or_gt f.Fexp e' with he | he
  · have hd : 0 ≤ e' - f.Fexp := by omega
    rw [← F2R_Zabs]
    show ((|f.Fnum| : ℤ) : ℝ) * bpow beta f.Fexp < bpow beta e'
    have hβ1 : 0 < bpow beta f.Fexp := bpow_gt_0 beta f.Fexp
    have hbpow : bpow beta e'
        = ((beta.val ^ (e' - f.Fexp).toNat : ℤ) : ℝ) * bpow beta f.Fexp := by
      rw [IZR_Zpower beta hd, ← bpow_plus]
      congr 1; omega
    rw [hbpow]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast h) hβ1
  · -- e' < f.Fexp: hypothesis says |m| < beta^0 = 1, so m = 0
    have hzero : (e' - f.Fexp).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hzero, pow_zero] at h
    have hm : f.Fnum = 0 := by
      have habs : |f.Fnum| ≤ 0 := by linarith
      exact abs_nonpos_iff.mp habs
    rw [show F2R f = 0 from by unfold F2R; rw [hm]; simp]
    rw [abs_zero]
    exact bpow_gt_0 beta e'

/-! ### Magnitude of F2R values -/

/-- For `0 < m` and `F2R ⟨m, e⟩ ≤ x < F2R ⟨m+1, e⟩`, the magnitudes match:
`mag β x = mag β (F2R ⟨m, e⟩)`. The half-open interval `[F2R, next-F2R)`
sits within a single magnitude band. -/
theorem mag_F2R_bounds {x : ℝ} (m e : ℤ) (Hp : 0 < m)
    (Hx : F2R (beta := beta) ⟨m, e⟩ ≤ x ∧ x < F2R (beta := beta) ⟨m + 1, e⟩) :
    mag beta x = mag beta (F2R (beta := beta) ⟨m, e⟩) := by
  obtain ⟨Hx1, Hx2⟩ := Hx
  have hF_pos : 0 < F2R (beta := beta) ⟨m, e⟩ := F2R_gt_0 ⟨m, e⟩ Hp
  have hF_ne : F2R (beta := beta) ⟨m, e⟩ ≠ 0 := ne_of_gt hF_pos
  have hx_pos : 0 < x := lt_of_lt_of_le hF_pos Hx1
  set ex := mag beta (F2R (beta := beta) ⟨m, e⟩)
  have h_lo : bpow beta (ex - 1) ≤ F2R (beta := beta) ⟨m, e⟩ := by
    have := bpow_mag_le beta hF_ne
    rwa [abs_of_pos hF_pos] at this
  have h_hi : F2R (beta := beta) ⟨m, e⟩ < bpow beta ex := by
    have := bpow_mag_gt beta (F2R (beta := beta) ⟨m, e⟩)
    rwa [abs_of_pos hF_pos] at this
  apply mag_unique beta
  · rw [abs_of_pos hx_pos]
    exact le_trans h_lo Hx1
  · rw [abs_of_pos hx_pos]
    exact lt_of_lt_of_le Hx2 (F2R_p1_le_bpow Hp h_hi)

/-- The magnitude of `F2R ⟨m, e⟩` equals the magnitude of `m` plus `e`. -/
theorem mag_F2R (m e : ℤ) (h : m ≠ 0) :
    mag beta (F2R (beta := beta) ⟨m, e⟩) = mag beta (m : ℝ) + e := by
  show mag beta ((m : ℝ) * bpow beta e) = mag beta (m : ℝ) + e
  exact mag_mult_bpow beta (by exact_mod_cast h) e

/-- If `F2R ⟨m1, e1⟩ < F2R ⟨m2, e2⟩ < F2R ⟨m1+1, e1⟩` with `0 < m1`,
then `e2 < e1` and the magnitudes align: `e1 + mag m1 = e2 + mag m2`. -/
theorem float_distribution_pos (m1 e1 m2 e2 : ℤ) (Hp1 : 0 < m1)
    (H : F2R (beta := beta) ⟨m1, e1⟩ < F2R (beta := beta) ⟨m2, e2⟩ ∧
         F2R (beta := beta) ⟨m2, e2⟩ < F2R (beta := beta) ⟨m1 + 1, e1⟩) :
    e2 < e1 ∧ e1 + mag beta (m1 : ℝ) = e2 + mag beta (m2 : ℝ) := by
  obtain ⟨H12, H21⟩ := H
  -- Step 1: e2 < e1.
  have He : e2 < e1 := by
    by_contra h_le
    push_neg at h_le
    -- h_le : e1 ≤ e2. So F2R ⟨m2, e2⟩ = F2R ⟨m2 * β^(e2 - e1), e1⟩.
    have hF_ch : F2R (beta := beta) ⟨m2, e2⟩
        = F2R (beta := beta) ⟨m2 * (beta.val : ℤ) ^ (e2 - e1).toNat, e1⟩ :=
      F2R_change_exp e1 m2 e2 h_le
    -- From H21: F2R(m2*β^d, e1) < F2R(m1+1, e1), so m2*β^d ≤ m1.
    have h_lt_m : m2 * (beta.val : ℤ) ^ (e2 - e1).toNat < m1 + 1 := by
      apply lt_F2R (beta := beta) (e := e1)
      rw [← hF_ch]; exact H21
    have h_le_m : m2 * (beta.val : ℤ) ^ (e2 - e1).toNat ≤ m1 := by linarith
    -- Then F2R(m2*β^d, e1) ≤ F2R(m1, e1) — contradicts H12.
    have h_F_le : F2R (beta := beta) ⟨m2 * (beta.val : ℤ) ^ (e2 - e1).toNat, e1⟩
        ≤ F2R (beta := beta) ⟨m1, e1⟩ := F2R_le h_le_m
    rw [← hF_ch] at h_F_le
    linarith
  refine ⟨He, ?_⟩
  -- Step 2: magnitudes align via mag_F2R.
  -- We claim mag (F2R ⟨m1, e1⟩) = mag (F2R ⟨m2, e2⟩).
  have hF1_pos : 0 < F2R (beta := beta) ⟨m1, e1⟩ := F2R_gt_0 ⟨m1, e1⟩ Hp1
  have hF1_ne : F2R (beta := beta) ⟨m1, e1⟩ ≠ 0 := ne_of_gt hF1_pos
  have hm1_ne : m1 ≠ 0 := by linarith
  have hF2_pos : 0 < F2R (beta := beta) ⟨m2, e2⟩ := lt_trans hF1_pos H12
  have hm2_pos : 0 < m2 := gt_0_F2R hF2_pos
  have hm2_ne : m2 ≠ 0 := ne_of_gt hm2_pos
  set ex := mag beta (F2R (beta := beta) ⟨m1, e1⟩)
  have h_lo : bpow beta (ex - 1) ≤ F2R (beta := beta) ⟨m1, e1⟩ := by
    have := bpow_mag_le beta hF1_ne
    rwa [abs_of_pos hF1_pos] at this
  have h_hi : F2R (beta := beta) ⟨m1, e1⟩ < bpow beta ex := by
    have := bpow_mag_gt beta (F2R (beta := beta) ⟨m1, e1⟩)
    rwa [abs_of_pos hF1_pos] at this
  have h_F2_mag : mag beta (F2R (beta := beta) ⟨m2, e2⟩) = ex := by
    apply mag_unique beta
    · rw [abs_of_pos hF2_pos]
      exact le_trans h_lo (le_of_lt H12)
    · rw [abs_of_pos hF2_pos]
      exact lt_of_lt_of_le H21 (F2R_p1_le_bpow Hp1 h_hi)
  -- Now: ex = mag F2R(m1, e1) = mag(m1) + e1 (mag_F2R)
  --      ex = mag F2R(m2, e2) = mag(m2) + e2
  have h_F1_eq : mag beta (m1 : ℝ) + e1 = ex := (mag_F2R m1 e1 hm1_ne).symm
  have h_F2_eq : mag beta (m2 : ℝ) + e2 = ex := by
    have h := mag_F2R (beta := beta) m2 e2 hm2_ne
    rw [h_F2_mag] at h
    linarith
  linarith
