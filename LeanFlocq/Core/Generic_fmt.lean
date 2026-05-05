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

end LeanFlocq
