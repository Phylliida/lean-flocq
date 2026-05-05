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

end LeanFlocq
