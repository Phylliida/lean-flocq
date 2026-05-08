/-
Port of `flocq/src/Core/Ulp.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

The unit in the last place: `ulp x = bpow (cexp x)` for nonzero `x` (and a
fallback for zero, which depends on whether `fexp` has a "minimal exponent").
-/

import LeanFlocq.Core.Generic_fmt

namespace LeanFlocq

variable {beta : radix}

/-! ### `negligible_exp`: minimal exponent if it exists

The "small regime" of an exponent function `fexp` is the set `{n : n ≤ fexp n}`.
In FLX it is empty (`fexp = e - prec` with `prec > 0`); in FIX/FLT it stabilizes
at `emin`. `negligible_exp fexp` is `some n` for some witness `n` in the small
regime, or `none` if the regime is empty (equivalently `fexp n < n` for all `n`). -/
noncomputable def negligible_exp (fexp : ℤ → ℤ) : Option ℤ := by
  classical
  exact if h : ∃ n : ℤ, n ≤ fexp n then some (Classical.choose h) else none

/-- Spec for the `some` case. -/
theorem negligible_exp_some {fexp : ℤ → ℤ} {n : ℤ}
    (h : negligible_exp fexp = some n) : n ≤ fexp n := by
  classical
  unfold negligible_exp at h
  by_cases hex : ∃ m : ℤ, m ≤ fexp m
  · rw [dif_pos hex] at h
    have : Classical.choose hex = n := Option.some.inj h
    rw [← this]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    exact Option.noConfusion h

/-- Spec for the `none` case. -/
theorem negligible_exp_none {fexp : ℤ → ℤ}
    (h : negligible_exp fexp = none) : ∀ n : ℤ, fexp n < n := by
  classical
  unfold negligible_exp at h
  by_cases hex : ∃ m : ℤ, m ≤ fexp m
  · rw [dif_pos hex] at h; exact Option.noConfusion h
  · push_neg at hex
    intro n
    have := hex n
    omega

/-! ### Definition of `ulp` and basic properties -/

/-- `ulp x = bpow (cexp x)` for nonzero `x`; for `x = 0`, it falls back to
`bpow (fexp n)` for some witness `n` in the small regime, or `0` if no such
witness exists. -/
noncomputable def ulp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  if x = 0 then
    match negligible_exp fexp with
    | some n => bpow beta (fexp n)
    | none => 0
  else
    bpow beta (cexp beta fexp x)

/-- For nonzero `x`, `ulp x` reduces to `bpow (cexp x)`. -/
@[simp]
theorem ulp_neq_0 (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : x ≠ 0) :
    ulp beta fexp x = bpow beta (cexp beta fexp x) := by
  unfold ulp; rw [if_neg hx]

theorem ulp_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    ulp beta fexp (-x) = ulp beta fexp x := by
  unfold ulp
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [if_neg hx, if_neg (by intro h; exact hx (neg_eq_zero.mp h)), cexp_opp]

theorem ulp_abs (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    ulp beta fexp |x| = ulp beta fexp x := by
  unfold ulp
  by_cases hx : x = 0
  · rw [hx, abs_zero]
  · rw [if_neg hx, if_neg (by simpa [abs_eq_zero] using hx), cexp_abs]

theorem ulp_ge_0 (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    0 ≤ ulp beta fexp x := by
  unfold ulp
  by_cases hx : x = 0
  · rw [if_pos hx]
    cases h : negligible_exp fexp
    · exact le_refl _
    · exact bpow_ge_0 _ _
  · rw [if_neg hx]; exact bpow_ge_0 _ _

theorem ulp_bpow (beta : radix) (fexp : ℤ → ℤ) (e : ℤ) :
    ulp beta fexp (bpow beta e) = bpow beta (fexp (e + 1)) := by
  rw [ulp_neq_0 beta fexp (ne_of_gt (bpow_gt_0 beta e))]
  congr 1
  apply cexp_fexp
  rw [abs_of_pos (bpow_gt_0 beta e)]
  refine ⟨?_, ?_⟩
  · rw [show e + 1 - 1 = e from by ring]
  · exact bpow_lt beta (by linarith)

/-- For positive `x` in the format, `ulp x ≤ x`. -/
theorem ulp_le_id (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (hx : 0 < x) (Fx : generic_format beta fexp x) :
    ulp beta fexp x ≤ x := by
  rw [ulp_neq_0 beta fexp (ne_of_gt hx)]
  -- x = F2R ⟨Ztrunc(SM), cexp x⟩ with positive mantissa
  have hxe : x = F2R (beta := beta)
      ⟨Ztrunc (scaled_mantissa beta fexp x), cexp beta fexp x⟩ := Fx
  set m := Ztrunc (scaled_mantissa beta fexp x)
  -- m > 0 since F2R = x > 0 and bpow > 0
  have hm_pos : 0 < m := by
    have h_F2R_pos : 0 < F2R (beta := beta) ⟨m, cexp beta fexp x⟩ := by
      rw [← hxe]; exact hx
    exact gt_0_F2R h_F2R_pos
  have hm_ge_1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
  calc bpow beta (cexp beta fexp x)
      = 1 * bpow beta (cexp beta fexp x) := by ring
    _ ≤ (m : ℝ) * bpow beta (cexp beta fexp x) :=
        mul_le_mul_of_nonneg_right hm_ge_1 (bpow_ge_0 _ _)
    _ = F2R (beta := beta) ⟨m, cexp beta fexp x⟩ := rfl
    _ = x := hxe.symm

/-- For nonzero `x` in the format, `ulp x ≤ |x|`. -/
theorem ulp_le_abs (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (hx : x ≠ 0) (Fx : generic_format beta fexp x) :
    ulp beta fexp x ≤ |x| := by
  rw [← ulp_abs beta fexp x]
  exact ulp_le_id beta fexp (abs_pos.mpr hx) (generic_format_abs beta fexp Fx)

/-- The keystone Ulp lemma: when `x` is *not* in the format,
`round_UP x = round_DN x + ulp x`. -/
theorem round_UP_DN_ulp (beta : radix) (fexp : ℤ → ℤ) {x : ℝ}
    (Fx : ¬ generic_format beta fexp x) :
    round beta fexp (fun y : ℝ => ⌈y⌉) x
      = round beta fexp (fun y : ℝ => ⌊y⌋) x + ulp beta fexp x := by
  -- x ≠ 0 (since 0 is in the format).
  have hx_ne : x ≠ 0 := by
    intro h0; rw [h0] at Fx; exact Fx (generic_format_0 beta fexp)
  rw [ulp_neq_0 beta fexp hx_ne]
  -- The scaled mantissa is not an integer (else x would be in the format).
  set sm := scaled_mantissa beta fexp x with hsm_def
  have h_sm_not_int : (⌊sm⌋ : ℝ) ≠ sm := by
    intro h_eq
    apply Fx
    -- x = (⌊sm⌋ : ℝ) · bpow(cexp x), so x is in the format with mantissa ⌊sm⌋.
    have h_x_eq : x = F2R (beta := beta) ⟨⌊sm⌋, cexp beta fexp x⟩ := by
      unfold F2R
      show x = ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x)
      rw [h_eq, hsm_def]
      exact (scaled_mantissa_mult_bpow beta fexp x).symm
    rw [h_x_eq]
    apply generic_format_canonical
    unfold canonical
    show cexp beta fexp x = cexp beta fexp (F2R (beta := beta) ⟨⌊sm⌋, cexp beta fexp x⟩)
    rw [← h_x_eq]
  -- Now ⌈sm⌉ = ⌊sm⌋ + 1.
  have h_floor_lt : (⌊sm⌋ : ℝ) < sm :=
    lt_of_le_of_ne (Int.floor_le sm) h_sm_not_int
  have h_floor_lt_ceil : ⌊sm⌋ < ⌈sm⌉ := Int.lt_ceil.mpr h_floor_lt
  have h_ceil_le : ⌈sm⌉ ≤ ⌊sm⌋ + 1 := Int.ceil_le_floor_add_one sm
  have h_ceil_eq : (⌈sm⌉ : ℤ) = ⌊sm⌋ + 1 := by omega
  -- Plug in.
  unfold round
  show ((⌈sm⌉ : ℤ) : ℝ) * bpow beta (cexp beta fexp x)
      = ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x)
        + bpow beta (cexp beta fexp x)
  rw [h_ceil_eq]
  push_cast
  ring

end LeanFlocq
