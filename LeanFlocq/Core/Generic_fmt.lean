/-
Port of `flocq/src/Core/Generic_fmt.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Generic floating-point formats parametrized by an exponent function `fexp`.
Defines `Valid_exp`, `cexp`, `canonical`, `scaled_mantissa`, `generic_format`,
and the foundational lemmas about them.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Round_pred

namespace LeanFlocq

variable {beta : radix}

/-! ### Validity of an exponent function

A `fexp : ℤ → ℤ` is `Valid_exp` iff:
* where `fexp k < k` (the "small" regime), `fexp (k+1) ≤ k` (it grows slowly);
* where `k ≤ fexp k` (the "large" regime), `fexp` stabilizes — `fexp (fexp k + 1) ≤ fexp k`
  and `fexp l = fexp k` for all `l ≤ fexp k`.
-/
def Valid_exp (fexp : ℤ → ℤ) : Prop :=
  ∀ k : ℤ,
    (fexp k < k → fexp (k + 1) ≤ k) ∧
    (k ≤ fexp k →
      fexp (fexp k + 1) ≤ fexp k ∧
      ∀ l : ℤ, l ≤ fexp k → fexp l = fexp k)

theorem valid_exp_large {fexp : ℤ → ℤ} (h : Valid_exp fexp)
    {k l : ℤ} (Hk : fexp k < k) (Hkl : k ≤ l) : fexp l < l := by
  by_contra Hl
  push_neg at Hl
  have hsta := (h l).2 Hl
  have := hsta.2 k (by linarith)
  linarith

theorem valid_exp_large' {fexp : ℤ → ℤ} (h : Valid_exp fexp)
    {k l : ℤ} (Hk : fexp k < k) (Hlk : l ≤ k) : fexp l < k := by
  by_contra Hl
  push_neg at Hl
  have hll : l ≤ fexp l := le_trans Hlk Hl
  have hsta := (h l).2 hll
  have hkfl : fexp k = fexp l := hsta.2 k Hl
  linarith

/-! ### Canonical exponent, scaled mantissa, and generic format -/

/-- The canonical exponent for `x`: `fexp` applied to `mag β x`. -/
noncomputable def cexp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℤ :=
  fexp (mag beta x)

/-- A float is canonical when its exponent equals `cexp` of its real value. -/
def canonical (beta : radix) (fexp : ℤ → ℤ) (f : float beta) : Prop :=
  f.Fexp = cexp beta fexp (F2R f)

/-- The scaled mantissa: `x * β^(-cexp x)`. -/
noncomputable def scaled_mantissa (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  x * bpow beta (-cexp beta fexp x)

/-- `x` is in the generic format iff it equals the F2R of (truncated scaled
mantissa, canonical exponent). -/
noncomputable def generic_format (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : Prop :=
  x = F2R (beta := beta) ⟨Ztrunc (scaled_mantissa beta fexp x), cexp beta fexp x⟩

/-! ### Basic facts -/

theorem generic_format_0 (beta : radix) (fexp : ℤ → ℤ) :
    generic_format beta fexp 0 := by
  unfold generic_format scaled_mantissa
  have hz : Ztrunc ((0 : ℝ) * bpow beta (-cexp beta fexp 0)) = 0 := by
    rw [zero_mul]
    unfold Ztrunc
    rw [if_neg (lt_irrefl 0), Int.floor_zero]
  rw [hz]
  show (0 : ℝ) = F2R (beta := beta) ⟨0, cexp beta fexp 0⟩
  rw [F2R_0]

theorem cexp_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    cexp beta fexp (-x) = cexp beta fexp x := by
  unfold cexp
  rw [mag_opp]

theorem cexp_abs (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    cexp beta fexp |x| = cexp beta fexp x := by
  unfold cexp
  rw [mag_abs]

theorem canonical_generic_format (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (Hx : generic_format beta fexp x) :
    ∃ f : float beta, x = F2R f ∧ canonical beta fexp f := by
  refine ⟨⟨Ztrunc (scaled_mantissa beta fexp x), cexp beta fexp x⟩, Hx, ?_⟩
  unfold canonical
  show cexp beta fexp x = cexp beta fexp (F2R _)
  rw [← Hx]

/-- `β^e` is in the format whenever `fexp (e+1) ≤ e`. -/
theorem generic_format_bpow (beta : radix) (fexp : ℤ → ℤ) (e : ℤ)
    (H : fexp (e + 1) ≤ e) : generic_format beta fexp (bpow beta e) := by
  unfold generic_format scaled_mantissa cexp
  rw [mag_bpow]
  have hd : 0 ≤ e - fexp (e + 1) := by linarith
  have h_combine : bpow beta e * bpow beta (-fexp (e + 1))
      = bpow beta (e - fexp (e + 1)) := by
    rw [← bpow_plus]; rfl
  have h_pow : bpow beta (e - fexp (e + 1))
      = ((beta.val ^ (e - fexp (e + 1)).toNat : ℤ) : ℝ) :=
    (IZR_Zpower beta hd).symm
  rw [h_combine, h_pow, Ztrunc_intCast]
  show bpow beta e
      = ((beta.val ^ (e - fexp (e + 1)).toNat : ℤ) : ℝ) * bpow beta (fexp (e + 1))
  rw [IZR_Zpower beta hd, ← bpow_plus]
  congr 1; ring

/-- Variant: `fexp e ≤ e` suffices given `Valid_exp`. -/
theorem generic_format_bpow' (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (e : ℤ) (He : fexp e ≤ e) : generic_format beta fexp (bpow beta e) := by
  apply generic_format_bpow beta fexp e
  rcases lt_or_eq_of_le He with hlt | heq
  · exact ((hValid e).1 hlt)
  · -- fexp e = e: stable regime
    have hge : e ≤ fexp e := by linarith
    have hsta := (hValid e).2 hge
    have hsta_eq := hsta.2 e heq.symm.le
    rw [show fexp (e + 1) = fexp (fexp e + 1) from by rw [heq]]
    linarith [hsta.1]

/-- An F2R with exponent at least `cexp` lies in the format. -/
theorem generic_format_F2R (beta : radix) (fexp : ℤ → ℤ) (m e : ℤ)
    (H : m ≠ 0 → cexp beta fexp (F2R (beta := beta) ⟨m, e⟩) ≤ e) :
    generic_format beta fexp (F2R (beta := beta) ⟨m, e⟩) := by
  by_cases hm : m = 0
  · rw [hm, F2R_0]
    exact generic_format_0 beta fexp
  · unfold generic_format scaled_mantissa
    set e' := cexp beta fexp (F2R (beta := beta) ⟨m, e⟩) with he'
    have He : e' ≤ e := H hm
    have hd : 0 ≤ e - e' := by linarith
    -- F2R ⟨m, e⟩ * bpow (-e') = (m * beta^(e - e')) as a real
    have h1 : F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e')
        = ((m * beta.val ^ (e - e').toNat : ℤ) : ℝ) := by
      unfold F2R
      have step1 : (m : ℝ) * bpow beta e * bpow beta (-e')
          = (m : ℝ) * bpow beta (e - e') := by
        rw [mul_assoc, ← bpow_plus]; rfl
      rw [step1, ← IZR_Zpower beta hd]
      push_cast; ring
    rw [h1, Ztrunc_intCast]
    exact F2R_change_exp e' m e He

/-! ### Canonical floats: behaviour under negation and absolute value -/

theorem canonical_opp (beta : radix) (fexp : ℤ → ℤ) (m e : ℤ)
    (h : canonical beta fexp ⟨m, e⟩) : canonical beta fexp ⟨-m, e⟩ := by
  unfold canonical at h ⊢
  show e = cexp beta fexp (F2R (beta := beta) ⟨-m, e⟩)
  rw [F2R_Zopp, cexp_opp]; exact h

theorem canonical_abs (beta : radix) (fexp : ℤ → ℤ) (m e : ℤ)
    (h : canonical beta fexp ⟨m, e⟩) : canonical beta fexp ⟨|m|, e⟩ := by
  unfold canonical at h ⊢
  show e = cexp beta fexp (F2R (beta := beta) ⟨|m|, e⟩)
  rw [F2R_Zabs, cexp_abs]; exact h

theorem canonical_0 (beta : radix) (fexp : ℤ → ℤ) :
    canonical beta fexp ⟨0, fexp (mag beta 0)⟩ := by
  unfold canonical cexp
  show fexp (mag beta 0) = fexp (mag beta (F2R (beta := beta) ⟨0, fexp (mag beta 0)⟩))
  rw [F2R_0]

theorem canonical_unique (beta : radix) (fexp : ℤ → ℤ) (f1 f2 : float beta)
    (h1 : canonical beta fexp f1) (h2 : canonical beta fexp f2)
    (h : F2R f1 = F2R f2) : f1 = f2 := by
  obtain ⟨m1, e1⟩ := f1
  obtain ⟨m2, e2⟩ := f2
  unfold canonical at h1 h2
  simp only at h1 h2
  have he : e1 = e2 := by rw [h1, h2, h]
  subst he
  have hm : m1 = m2 := eq_F2R (beta := beta) (e := e1) h
  subst hm
  rfl

/-! ### Scaled mantissa -/

theorem scaled_mantissa_generic (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (Hx : generic_format beta fexp x) :
    scaled_mantissa beta fexp x = ((Ztrunc (scaled_mantissa beta fexp x) : ℤ) : ℝ) := by
  set m := Ztrunc (scaled_mantissa beta fexp x)
  set c := cexp beta fexp x
  have Hx2 : x = (m : ℝ) * bpow beta c := by
    have := Hx; unfold generic_format F2R at this; exact this
  unfold scaled_mantissa
  show x * bpow beta (-c) = (m : ℝ)
  rw [Hx2, mul_assoc, ← bpow_plus, show (c + -c) = 0 from by ring, bpow_zero, mul_one]

theorem scaled_mantissa_mult_bpow (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    scaled_mantissa beta fexp x * bpow beta (cexp beta fexp x) = x := by
  unfold scaled_mantissa
  rw [mul_assoc, ← bpow_plus, show (-cexp beta fexp x + cexp beta fexp x) = 0 from by ring,
      bpow_zero, mul_one]

@[simp]
theorem scaled_mantissa_0 (beta : radix) (fexp : ℤ → ℤ) :
    scaled_mantissa beta fexp 0 = 0 := by
  unfold scaled_mantissa; rw [zero_mul]

theorem scaled_mantissa_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    scaled_mantissa beta fexp (-x) = -scaled_mantissa beta fexp x := by
  unfold scaled_mantissa
  rw [cexp_opp, neg_mul]

theorem scaled_mantissa_abs (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    scaled_mantissa beta fexp |x| = |scaled_mantissa beta fexp x| := by
  unfold scaled_mantissa
  rw [cexp_abs, abs_mul, abs_of_nonneg (bpow_ge_0 beta _)]

/-! ### Format under negation and absolute value -/

theorem generic_format_opp (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (Hx : generic_format beta fexp x) : generic_format beta fexp (-x) := by
  unfold generic_format at Hx ⊢
  rw [scaled_mantissa_opp, cexp_opp, Ztrunc_opp, F2R_Zopp]
  show -x = -F2R (beta := beta) ⟨Ztrunc (scaled_mantissa beta fexp x), cexp beta fexp x⟩
  rw [← Hx]

theorem generic_format_abs (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (Hx : generic_format beta fexp x) : generic_format beta fexp |x| := by
  unfold generic_format at Hx ⊢
  rw [scaled_mantissa_abs, cexp_abs, Ztrunc_abs, F2R_Zabs]
  show |x| = |F2R (beta := beta) ⟨Ztrunc (scaled_mantissa beta fexp x), cexp beta fexp x⟩|
  rw [← Hx]

theorem generic_format_abs_inv (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (h : generic_format beta fexp |x|) : generic_format beta fexp x := by
  rcases le_or_gt 0 x with hx | hx
  · rwa [abs_of_nonneg hx] at h
  · rw [abs_of_neg hx] at h
    have := generic_format_opp beta fexp h
    rwa [neg_neg] at this

/-- Variant of `generic_format_F2R` for an arbitrary float `f` with the
real value extracted as `x`. -/
theorem generic_format_F2R' (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (f : float beta) (h1 : F2R f = x)
    (h2 : x ≠ 0 → cexp beta fexp x ≤ f.Fexp) : generic_format beta fexp x := by
  subst h1
  obtain ⟨m, e⟩ := f
  apply generic_format_F2R beta fexp m e
  intro hm
  exact h2 (F2R_neq_0 ⟨m, e⟩ hm)

/-! ### Subnormal regime: mantissa is small -/

/-- For a positive `x` in `[β^(ex-1), β^ex)` and `ex ≤ fexp ex` (subnormal
regime), the scaled value `x · β^(-fexp ex)` lies strictly in `(0, 1)`. -/
theorem mantissa_small_pos (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {ex : ℤ}
    (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex)
    (He : ex ≤ fexp ex) :
    0 < x * bpow beta (-fexp ex) ∧ x * bpow beta (-fexp ex) < 1 := by
  have hxpos : 0 < x := lt_of_lt_of_le (bpow_gt_0 beta (ex - 1)) Hx.1
  refine ⟨mul_pos hxpos (bpow_gt_0 beta _), ?_⟩
  have h_bp : bpow beta ex ≤ bpow beta (fexp ex) := bpow_le beta He
  have eq1 : bpow beta (fexp ex) * bpow beta (-fexp ex) = 1 := by
    rw [← bpow_plus, show (fexp ex + -fexp ex) = 0 from by ring, bpow_zero]
  have step1 : x * bpow beta (-fexp ex) < bpow beta ex * bpow beta (-fexp ex) :=
    mul_lt_mul_of_pos_right Hx.2 (bpow_gt_0 beta _)
  have step2 : bpow beta ex * bpow beta (-fexp ex)
      ≤ bpow beta (fexp ex) * bpow beta (-fexp ex) :=
    mul_le_mul_of_nonneg_right h_bp (bpow_ge_0 beta _)
  linarith

/-- In the subnormal regime, the floor of the scaled mantissa is 0. -/
theorem mantissa_DN_small_pos (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {ex : ℤ}
    (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex)
    (He : ex ≤ fexp ex) :
    ⌊x * bpow beta (-fexp ex)⌋ = 0 := by
  have H := mantissa_small_pos beta fexp Hx He
  rw [Int.floor_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast; linarith [H.1]
  · push_cast; linarith [H.2]

/-- In the subnormal regime, the ceiling of the scaled mantissa is 1. -/
theorem mantissa_UP_small_pos (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {ex : ℤ}
    (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex)
    (He : ex ≤ fexp ex) :
    ⌈x * bpow beta (-fexp ex)⌉ = 1 := by
  have H := mantissa_small_pos beta fexp Hx He
  rw [Int.ceil_eq_iff]
  refine ⟨?_, ?_⟩
  · push_cast; linarith [H.1]
  · push_cast; linarith [H.2]

/-- When `|x| < β^ex` and `ex ≤ fexp ex`, the scaled mantissa is in `(-1, 1)`. -/
theorem scaled_mantissa_lt_1 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {ex : ℤ} (Ex : |x| < bpow beta ex) (He : ex ≤ fexp ex) :
    |scaled_mantissa beta fexp x| < 1 := by
  by_cases hx : x = 0
  · rw [hx, scaled_mantissa_0, abs_zero]; exact zero_lt_one
  rw [← scaled_mantissa_abs]
  unfold scaled_mantissa
  rw [cexp_abs]
  unfold cexp
  set ex' := mag beta x
  have h_mag_low : bpow beta (ex' - 1) ≤ |x| := bpow_mag_le beta hx
  have h_mag_high : |x| < bpow beta ex' := bpow_mag_gt beta x
  have hex'_le_ex : ex' ≤ ex := by
    have h := lt_of_le_of_lt h_mag_low Ex
    have := lt_bpow beta h
    omega
  have hex'_le_fex : ex' ≤ fexp ex := le_trans hex'_le_ex He
  have hfex_eq : fexp ex' = fexp ex := ((hValid ex).2 He).2 ex' hex'_le_fex
  have hex'_le_fex' : ex' ≤ fexp ex' := by rw [hfex_eq]; exact hex'_le_fex
  have H := mantissa_small_pos beta fexp ⟨h_mag_low, h_mag_high⟩ hex'_le_fex'
  exact H.2

/-- For values in the format, `cexp x < mag β x` (when `x ≠ 0`). -/
theorem mag_generic_gt (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (Zx : x ≠ 0) (Gx : generic_format beta fexp x) :
    cexp beta fexp x < mag beta x := by
  by_contra H
  push_neg at H
  set ex := mag beta x with hex_def
  have hH : ex ≤ fexp ex := H
  have h_mag_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have h_sm_lt_1 : |scaled_mantissa beta fexp x| < 1 :=
    scaled_mantissa_lt_1 beta fexp hValid h_mag_high hH
  have h_z_zero : Ztrunc (scaled_mantissa beta fexp x) = 0 := by
    set sm := scaled_mantissa beta fexp x
    have habs : -1 < sm ∧ sm < 1 := abs_lt.mp h_sm_lt_1
    unfold Ztrunc
    by_cases hsm_neg : sm < 0
    · rw [if_pos hsm_neg, Int.ceil_eq_iff]
      push_cast
      refine ⟨by linarith [habs.1], by linarith⟩
    · rw [if_neg hsm_neg, Int.floor_eq_iff]
      push_cast
      refine ⟨by linarith [not_lt.mp hsm_neg], by linarith [habs.2]⟩
  have hx_eq : x = F2R (beta := beta) ⟨0, cexp beta fexp x⟩ := by
    have hG := Gx
    unfold generic_format at hG
    rw [h_z_zero] at hG
    exact hG
  rw [F2R_0] at hx_eq
  exact Zx hx_eq

/-! ### No representable values strictly between adjacent mantissas -/

/-- If `x` lies strictly between `F2R ⟨m, cexp x⟩` and `F2R ⟨m+1, cexp x⟩`,
then `x` cannot be in the format. -/
theorem generic_format_discrete (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (m : ℤ)
    (Hx : F2R (beta := beta) ⟨m, cexp beta fexp x⟩ < x ∧
          x < F2R (beta := beta) ⟨m + 1, cexp beta fexp x⟩) :
    ¬ generic_format beta fexp x := by
  intro Hf
  set e := cexp beta fexp x
  set z := Ztrunc (scaled_mantissa beta fexp x)
  have h1 : F2R (beta := beta) ⟨m, e⟩ < F2R (beta := beta) ⟨z, e⟩ := by
    rw [show F2R (beta := beta) ⟨z, e⟩ = x from Hf.symm]; exact Hx.1
  have h2 : F2R (beta := beta) ⟨z, e⟩ < F2R (beta := beta) ⟨m + 1, e⟩ := by
    rw [show F2R (beta := beta) ⟨z, e⟩ = x from Hf.symm]; exact Hx.2
  have hmz : m < z := lt_F2R h1
  have hzm : z < m + 1 := lt_F2R h2
  omega

/-! ### Canonical floats are in the format -/

theorem generic_format_canonical (beta : radix) (fexp : ℤ → ℤ) {f : float beta}
    (Hf : canonical beta fexp f) : generic_format beta fexp (F2R f) := by
  obtain ⟨m, e⟩ := f
  unfold canonical at Hf
  simp only at Hf
  unfold generic_format scaled_mantissa
  -- F2R ⟨m, e⟩ * bpow (-cexp (F2R ⟨m, e⟩)) — but cexp = e via Hf
  rw [← Hf]
  -- Goal: F2R ⟨m, e⟩ = F2R ⟨Ztrunc (F2R ⟨m, e⟩ * bpow (-e)), e⟩
  apply F2R_eq
  -- Need: m = Ztrunc (F2R ⟨m, e⟩ * bpow (-e))
  show m = Ztrunc (((m : ℝ) * bpow beta e) * bpow beta (-e))
  rw [mul_assoc, ← bpow_plus, show (e + -e) = 0 from by ring, bpow_zero, mul_one]
  rw [Ztrunc_intCast]

/-- For `fexp` close to identity (`e - prec ≤ fexp e` for some `prec`),
`|x| < β^(prec + cexp x)`. -/
theorem abs_lt_bpow_prec (beta : radix) (fexp : ℤ → ℤ)
    (prec : ℤ) (Hp : ∀ e : ℤ, e - prec ≤ fexp e) (x : ℝ) :
    |x| < bpow beta (prec + cexp beta fexp x) := by
  by_cases hx : x = 0
  · rw [hx, abs_zero]; exact bpow_gt_0 beta _
  unfold cexp
  set ex := mag beta x
  have h_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have h_le : bpow beta ex ≤ bpow beta (prec + fexp ex) :=
    bpow_le beta (by have := Hp ex; omega)
  linarith

/-- If `β^e` is in the format, then `fexp (e+1) ≤ e`. -/
theorem generic_format_bpow_inv' (beta : radix) (fexp : ℤ → ℤ) (e : ℤ)
    (He : generic_format beta fexp (bpow beta e)) : fexp (e + 1) ≤ e := by
  by_contra Hgt
  push_neg at Hgt
  unfold generic_format scaled_mantissa cexp at He
  rw [mag_bpow] at He
  have h_combine : bpow beta e * bpow beta (-fexp (e + 1))
      = bpow beta (e - fexp (e + 1)) := by
    rw [← bpow_plus]; rfl
  have h_nonneg : 0 ≤ bpow beta (e - fexp (e + 1)) := bpow_ge_0 _ _
  have h_lt_1 : bpow beta (e - fexp (e + 1)) < 1 := by
    have : bpow beta (e - fexp (e + 1)) < bpow beta 0 := bpow_lt beta (by omega)
    rwa [bpow_zero] at this
  have h_ztrunc : Ztrunc (bpow beta e * bpow beta (-fexp (e + 1))) = 0 := by
    rw [h_combine, Ztrunc_floor h_nonneg, Int.floor_eq_iff]
    push_cast
    exact ⟨h_nonneg, by linarith⟩
  rw [h_ztrunc, F2R_0] at He
  exact (ne_of_gt (bpow_gt_0 beta e)) He

/-- If `β^e` is in the format, then `fexp e ≤ e`. -/
theorem generic_format_bpow_inv (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (e : ℤ) (He : generic_format beta fexp (bpow beta e)) : fexp e ≤ e := by
  have h := generic_format_bpow_inv' beta fexp e He
  by_contra hgt
  push_neg at hgt
  have := valid_exp_large' hValid (k := e + 1) (l := e) (by omega) (by omega)
  omega

/-- A positive value in the format is at least `bpow emin` whenever `emin`
is a uniform lower bound for `fexp`. -/
theorem generic_format_ge_bpow (beta : radix) (fexp : ℤ → ℤ) (emin : ℤ)
    (Emin : ∀ e : ℤ, emin ≤ fexp e) {x : ℝ}
    (Hx : 0 < x) (Fx : generic_format beta fexp x) : bpow beta emin ≤ x := by
  set z := Ztrunc (scaled_mantissa beta fexp x)
  set e := cexp beta fexp x
  have hz_pos : 0 < z := by
    apply gt_0_F2R (beta := beta) (e := e)
    rw [show F2R (beta := beta) ⟨z, e⟩ = x from Fx.symm]
    exact Hx
  rw [Fx]
  calc bpow beta emin
      ≤ bpow beta (fexp (mag beta x)) := bpow_le beta (Emin _)
    _ ≤ F2R (beta := beta) ⟨z, e⟩ := bpow_le_F2R hz_pos

/-! ### Canonical exponent equals fexp on tight bounds -/

theorem cexp_fexp (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {ex : ℤ}
    (Hx : bpow beta (ex - 1) ≤ |x| ∧ |x| < bpow beta ex) :
    cexp beta fexp x = fexp ex := by
  unfold cexp
  rw [mag_unique beta Hx.1 Hx.2]

theorem cexp_fexp_pos (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {ex : ℤ}
    (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex) :
    cexp beta fexp x = fexp ex := by
  apply cexp_fexp
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg]; exact Hx.1
    exact le_trans (bpow_ge_0 beta _) Hx.1
  · rw [abs_of_nonneg]; exact Hx.2
    exact le_trans (bpow_ge_0 beta _) Hx.1

/-! ### Rounding to integer: `Valid_rnd` class -/

/-- A valid integer-rounding function: monotone, fixes integers. -/
class Valid_rnd (rnd : ℝ → ℤ) : Prop where
  Zrnd_le : ∀ x y : ℝ, x ≤ y → rnd x ≤ rnd y
  Zrnd_intCast : ∀ n : ℤ, rnd (n : ℝ) = n

/-- Any valid rounding agrees with floor or ceiling at every point. -/
theorem Zrnd_DN_or_UP (rnd : ℝ → ℤ) [hv : Valid_rnd rnd] (x : ℝ) :
    rnd x = ⌊x⌋ ∨ rnd x = ⌈x⌉ := by
  have h_lb : ⌊x⌋ ≤ rnd x := by
    have := hv.Zrnd_le _ _ (Int.floor_le x)
    rw [hv.Zrnd_intCast] at this
    exact this
  have h_ub : rnd x ≤ ⌈x⌉ := by
    have := hv.Zrnd_le _ _ (Int.le_ceil x)
    rw [hv.Zrnd_intCast] at this
    exact this
  rcases eq_or_ne (rnd x) ⌊x⌋ with h | h
  · exact Or.inl h
  · right
    have h_lt : ⌊x⌋ < rnd x := lt_of_le_of_ne h_lb (Ne.symm h)
    have h_ceil_floor : ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
    omega

/-! ### `round`: combine `rnd` with `cexp` to define the rounded value -/

/-- `round β fexp rnd x` rounds `x` by:
1. scaling: `s := x · β^(-cexp x)`
2. integer-rounding: `m := rnd s`
3. unscaling: `m · β^(cexp x)`. -/
noncomputable def round (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) (x : ℝ) : ℝ :=
  F2R (beta := beta) ⟨rnd (scaled_mantissa beta fexp x), cexp beta fexp x⟩

@[simp]
theorem round_0 (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) [hv : Valid_rnd rnd] :
    round beta fexp rnd 0 = 0 := by
  unfold round scaled_mantissa
  rw [zero_mul]
  have hrz : rnd (0 : ℝ) = 0 := by
    have h := hv.Zrnd_intCast 0
    push_cast at h
    exact h
  rw [hrz, F2R_0]

/-- Any valid rounding agrees with `Ztrunc` or `Zaway` at every point. -/
theorem Zrnd_ZR_or_AW (rnd : ℝ → ℤ) [Valid_rnd rnd] (x : ℝ) :
    rnd x = Ztrunc x ∨ rnd x = Zaway x := by
  unfold Ztrunc Zaway
  rcases Zrnd_DN_or_UP rnd x with H | H
  · by_cases hxn : x < 0
    · rw [if_pos hxn, if_pos hxn]; right; exact H
    · rw [if_neg hxn, if_neg hxn]; left; exact H
  · by_cases hxn : x < 0
    · rw [if_pos hxn, if_pos hxn]; left; exact H
    · rw [if_neg hxn, if_neg hxn]; right; exact H

/-- Values already in the format are fixed by `round`. -/
theorem round_generic (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) [hv : Valid_rnd rnd]
    {x : ℝ} (Hx : generic_format beta fexp x) :
    round beta fexp rnd x = x := by
  unfold round
  rw [scaled_mantissa_generic beta fexp Hx, hv.Zrnd_intCast]
  exact Hx.symm

/-- `round` is determined by the rounding function pointwise. -/
theorem round_ext (beta : radix) (fexp : ℤ → ℤ) {rnd1 rnd2 : ℝ → ℤ}
    (Hext : ∀ x, rnd1 x = rnd2 x) (x : ℝ) :
    round beta fexp rnd1 x = round beta fexp rnd2 x := by
  unfold round
  rw [Hext]

/-- In the "large" regime (`fexp ex < ex`), if `x ∈ [β^(ex-1), β^ex)`,
then `round x ∈ [β^(ex-1), β^ex]`. -/
theorem round_bounded_large_pos (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ)
    [Valid_rnd rnd] {x : ℝ} {ex : ℤ} (He : fexp ex < ex)
    (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex) :
    bpow beta (ex - 1) ≤ round beta fexp rnd x ∧
    round beta fexp rnd x ≤ bpow beta ex := by
  unfold round scaled_mantissa
  rw [cexp_fexp_pos beta fexp Hx]
  set s := x * bpow beta (-fexp ex) with hs_def
  have hd1 : 0 ≤ ex - 1 - fexp ex := by omega
  have hd2 : 0 ≤ ex - fexp ex := by omega
  have hβ_fexp : 0 < bpow beta (fexp ex) := bpow_gt_0 _ _
  have hβ_neg : 0 < bpow beta (-fexp ex) := bpow_gt_0 _ _
  have h_xs : s * bpow beta (fexp ex) = x := by
    show x * bpow beta (-fexp ex) * bpow beta (fexp ex) = x
    rw [mul_assoc, ← bpow_plus, show -fexp ex + fexp ex = 0 from by ring,
        bpow_zero, mul_one]
  have hs_low : bpow beta (ex - 1 - fexp ex) ≤ s := by
    have h1 : bpow beta (ex - 1) * bpow beta (-fexp ex) ≤ s :=
      mul_le_mul_of_nonneg_right Hx.1 (bpow_ge_0 _ _)
    rwa [← bpow_plus, show ex - 1 + -fexp ex = ex - 1 - fexp ex from by ring] at h1
  have hs_high : s < bpow beta (ex - fexp ex) := by
    have h1 : s < bpow beta ex * bpow beta (-fexp ex) :=
      mul_lt_mul_of_pos_right Hx.2 hβ_neg
    rwa [← bpow_plus, show ex + -fexp ex = ex - fexp ex from by ring] at h1
  have h_pow_low_eq : bpow beta (ex - 1 - fexp ex)
      = ((beta.val ^ (ex - 1 - fexp ex).toNat : ℤ) : ℝ) := (IZR_Zpower beta hd1).symm
  have h_pow_high_eq : bpow beta (ex - fexp ex)
      = ((beta.val ^ (ex - fexp ex).toNat : ℤ) : ℝ) := (IZR_Zpower beta hd2).symm
  rcases Zrnd_DN_or_UP rnd s with Hr | Hr
  · -- DN case
    rw [Hr]
    refine ⟨?_, ?_⟩
    · show bpow beta (ex - 1) ≤ ((⌊s⌋ : ℤ) : ℝ) * bpow beta (fexp ex)
      have h_int : (beta.val ^ (ex - 1 - fexp ex).toNat : ℤ) ≤ ⌊s⌋ := by
        apply Int.le_floor.mpr
        rw [← h_pow_low_eq]; exact hs_low
      have h_real : ((beta.val ^ (ex - 1 - fexp ex).toNat : ℤ) : ℝ) ≤ ((⌊s⌋ : ℤ) : ℝ) := by
        exact_mod_cast h_int
      rw [show bpow beta (ex - 1) = bpow beta (ex - 1 - fexp ex) * bpow beta (fexp ex) from by
        rw [← bpow_plus]; congr 1; ring]
      rw [h_pow_low_eq]
      exact mul_le_mul_of_nonneg_right h_real hβ_fexp.le
    · show ((⌊s⌋ : ℤ) : ℝ) * bpow beta (fexp ex) ≤ bpow beta ex
      calc ((⌊s⌋ : ℤ) : ℝ) * bpow beta (fexp ex)
          ≤ s * bpow beta (fexp ex) :=
            mul_le_mul_of_nonneg_right (Int.floor_le s) hβ_fexp.le
        _ = x := h_xs
        _ ≤ bpow beta ex := Hx.2.le
  · -- UP case
    rw [Hr]
    refine ⟨?_, ?_⟩
    · show bpow beta (ex - 1) ≤ ((⌈s⌉ : ℤ) : ℝ) * bpow beta (fexp ex)
      calc bpow beta (ex - 1)
          ≤ x := Hx.1
        _ = s * bpow beta (fexp ex) := h_xs.symm
        _ ≤ ((⌈s⌉ : ℤ) : ℝ) * bpow beta (fexp ex) :=
            mul_le_mul_of_nonneg_right (Int.le_ceil s) hβ_fexp.le
    · show ((⌈s⌉ : ℤ) : ℝ) * bpow beta (fexp ex) ≤ bpow beta ex
      have h_int : ⌈s⌉ ≤ (beta.val ^ (ex - fexp ex).toNat : ℤ) := by
        apply Int.ceil_le.mpr
        rw [← h_pow_high_eq]; exact hs_high.le
      have h_real : ((⌈s⌉ : ℤ) : ℝ) ≤ ((beta.val ^ (ex - fexp ex).toNat : ℤ) : ℝ) := by
        exact_mod_cast h_int
      rw [show bpow beta ex = bpow beta (ex - fexp ex) * bpow beta (fexp ex) from by
        rw [← bpow_plus]; congr 1; ring]
      rw [h_pow_high_eq]
      exact mul_le_mul_of_nonneg_right h_real hβ_fexp.le

/-- In the "small" regime (`ex ≤ fexp ex`), `round x` is either `0` or `β^(fexp ex)`. -/
theorem round_bounded_small_pos (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ)
    [Valid_rnd rnd] {x : ℝ} {ex : ℤ} (He : ex ≤ fexp ex)
    (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex) :
    round beta fexp rnd x = 0 ∨ round beta fexp rnd x = bpow beta (fexp ex) := by
  unfold round scaled_mantissa
  rw [cexp_fexp_pos beta fexp Hx]
  set s := x * bpow beta (-fexp ex)
  rcases Zrnd_DN_or_UP rnd s with Hr | Hr
  · left
    rw [Hr]
    have h_floor_zero : ⌊s⌋ = 0 := mantissa_DN_small_pos beta fexp Hx He
    show ((⌊s⌋ : ℤ) : ℝ) * bpow beta (fexp ex) = 0
    rw [h_floor_zero]; push_cast; ring
  · right
    rw [Hr]
    have h_ceil_one : ⌈s⌉ = 1 := mantissa_UP_small_pos beta fexp Hx He
    show ((⌈s⌉ : ℤ) : ℝ) * bpow beta (fexp ex) = bpow beta (fexp ex)
    rw [h_ceil_one]; push_cast; ring

/-- If `round x = 0` and `x ∈ [β^(ex-1), β^ex)`, then `ex ≤ fexp ex` (subnormal). -/
theorem exp_small_round_0_pos (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} {ex : ℤ} (Hx : bpow beta (ex - 1) ≤ x ∧ x < bpow beta ex)
    (H1 : round beta fexp rnd x = 0) : ex ≤ fexp ex := by
  by_contra hgt
  push_neg at hgt
  have hbounds := round_bounded_large_pos beta fexp rnd hgt Hx
  have : 0 < bpow beta (ex - 1) := bpow_gt_0 _ _
  linarith [hbounds.1, H1]

/-- `round` is monotone on positive arguments. -/
theorem round_le_pos (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (rnd : ℝ → ℤ) [hv : Valid_rnd rnd] {x y : ℝ} (Hx : 0 < x) (Hxy : x ≤ y) :
    round beta fexp rnd x ≤ round beta fexp rnd y := by
  have Hy : 0 < y := lt_of_lt_of_le Hx Hxy
  set ex := mag beta x with hex_def
  set ey := mag beta y with hey_def
  have h_x_low : bpow beta (ex - 1) ≤ x := by
    have := bpow_mag_le beta (ne_of_gt Hx); rwa [abs_of_pos Hx] at this
  have h_x_high : x < bpow beta ex := by
    have := bpow_mag_gt beta x; rwa [abs_of_pos Hx] at this
  have h_y_low : bpow beta (ey - 1) ≤ y := by
    have := bpow_mag_le beta (ne_of_gt Hy); rwa [abs_of_pos Hy] at this
  have h_y_high : y < bpow beta ey := by
    have := bpow_mag_gt beta y; rwa [abs_of_pos Hy] at this
  have h_ex_ey : ex ≤ ey := by
    have h := lt_of_le_of_lt h_x_low (lt_of_le_of_lt Hxy h_y_high)
    have := lt_bpow beta h
    omega
  -- Helper: same fexp on ex and ey ⇒ round monotone
  have Heq : fexp ex = fexp ey →
      round beta fexp rnd x ≤ round beta fexp rnd y := by
    intro H
    unfold round scaled_mantissa cexp
    rw [show mag beta x = ex from rfl, show mag beta y = ey from rfl, H]
    apply F2R_le
    apply hv.Zrnd_le
    exact mul_le_mul_of_nonneg_right Hxy (bpow_ge_0 _ _)
  rcases le_or_gt ey (fexp ey) with Hy1 | Hy1
  · -- Subnormal y: Valid_exp gives fexp ex = fexp ey
    apply Heq
    exact ((hValid ey).2 Hy1).2 ex (le_trans h_ex_ey Hy1)
  · rcases lt_or_eq_of_le h_ex_ey with He | He
    · -- ex < ey: round x ≤ β^(ey-1) ≤ round y
      apply le_trans _ ((round_bounded_large_pos beta fexp rnd Hy1 ⟨h_y_low, h_y_high⟩).1)
      rcases le_or_gt ex (fexp ex) with Hx1 | Hx1
      · -- Subnormal x
        rcases round_bounded_small_pos beta fexp rnd Hx1 ⟨h_x_low, h_x_high⟩ with Hr | Hr
        · rw [Hr]; exact bpow_ge_0 _ _
        · rw [Hr]
          apply bpow_le beta
          by_contra h
          push_neg at h
          have hey_le : ey ≤ fexp ex := by omega
          have heq_fexp : fexp ey = fexp ex := ((hValid ex).2 Hx1).2 ey hey_le
          omega
      · -- Normal x: round x ≤ β^ex ≤ β^(ey-1)
        have := round_bounded_large_pos beta fexp rnd Hx1 ⟨h_x_low, h_x_high⟩
        apply le_trans this.2
        apply bpow_le beta; omega
    · apply Heq; rw [He]

/-- The round of a positive value is in the format. -/
theorem generic_format_round_pos (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ} (Hx0 : 0 < x) :
    generic_format beta fexp (round beta fexp rnd x) := by
  set ex := mag beta x with hex_def
  have h_low : bpow beta (ex - 1) ≤ x := by
    have := bpow_mag_le beta (ne_of_gt Hx0)
    rwa [abs_of_pos Hx0] at this
  have h_high : x < bpow beta ex := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos Hx0] at this
  rcases le_or_gt ex (fexp ex) with He | He
  · -- small regime
    rcases round_bounded_small_pos beta fexp rnd He ⟨h_low, h_high⟩ with Hr | Hr
    · rw [Hr]; exact generic_format_0 beta fexp
    · rw [Hr]
      apply generic_format_bpow beta fexp
      exact ((hValid ex).2 He).1
  · -- large regime
    obtain ⟨Hr1, Hr2⟩ := round_bounded_large_pos beta fexp rnd He ⟨h_low, h_high⟩
    rcases le_or_gt (bpow beta ex) (round beta fexp rnd x) with Hr | Hr
    · have heq : round beta fexp rnd x = bpow beta ex := le_antisymm Hr2 Hr
      rw [heq]
      apply generic_format_bpow beta fexp
      exact (hValid ex).1 He
    · unfold round
      apply generic_format_F2R beta fexp _ _
      intro _
      show cexp beta fexp (round beta fexp rnd x) ≤ cexp beta fexp x
      rw [cexp_fexp_pos beta fexp ⟨Hr1, Hr⟩, cexp_fexp_pos beta fexp ⟨h_low, h_high⟩]

/-! ### Negation: derived rounding via `-rnd(-x)` -/

/-- The negation-derived rounding: `Zrnd_opp x = -(rnd (-x))`. -/
noncomputable def Zrnd_opp (rnd : ℝ → ℤ) (x : ℝ) : ℤ := -(rnd (-x))

/-- `Zrnd_opp` is valid when `rnd` is. -/
instance valid_rnd_opp (rnd : ℝ → ℤ) [hv : Valid_rnd rnd] : Valid_rnd (Zrnd_opp rnd) where
  Zrnd_le := by
    intro x y Hxy
    unfold Zrnd_opp
    have := hv.Zrnd_le (-y) (-x) (by linarith)
    omega
  Zrnd_intCast := by
    intro n
    unfold Zrnd_opp
    have h : ((-n : ℤ) : ℝ) = -(n : ℝ) := by push_cast; rfl
    rw [show (-(n : ℝ)) = ((-n : ℤ) : ℝ) from h.symm, hv.Zrnd_intCast]
    omega

/-- `round rnd (-x) = -round (Zrnd_opp rnd) x`. -/
theorem round_opp (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℤ) (x : ℝ) :
    round beta fexp rnd (-x) = -round beta fexp (Zrnd_opp rnd) x := by
  unfold round Zrnd_opp
  rw [scaled_mantissa_opp, cexp_opp, F2R_Zopp]
  ring

end LeanFlocq
