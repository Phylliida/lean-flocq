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

/-! ### Predecessor and successor

`pred_pos x` is `x` minus a step, where the step is `bpow (fexp (mag x - 1))`
exactly when `x = bpow (mag x - 1)` (we are at the smallest representable
of magnitude `mag x`, and the *next-down* step shrinks). Otherwise the step
is just `ulp x`.

`succ x = x + ulp x` for `x ≥ 0`, with a symmetric reflection for `x < 0`.
`pred x := -succ(-x)`. -/

/-- The "predecessor" step on the positive side: `x - step`, where the step
shrinks at exact-bpow values. -/
noncomputable def pred_pos (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  if x = bpow beta (mag beta x - 1) then
    x - bpow beta (fexp (mag beta x - 1))
  else
    x - ulp beta fexp x

/-- The successor of `x` in the format. -/
noncomputable def succ (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  if 0 ≤ x then x + ulp beta fexp x
  else -(pred_pos beta fexp (-x))

/-- The predecessor of `x` in the format. -/
noncomputable def pred (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  -(succ beta fexp (-x))

/-- For `x ≥ 0`, `pred x = pred_pos x`. -/
theorem pred_eq_pos (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : 0 ≤ x) :
    pred beta fexp x = pred_pos beta fexp x := by
  unfold pred succ
  by_cases h : 0 ≤ -x
  · -- 0 ≤ -x and 0 ≤ x means x = 0
    rw [if_pos h]
    have hx0 : x = 0 := le_antisymm (by linarith) hx
    subst hx0
    simp only [neg_zero]
    unfold pred_pos
    rw [if_neg (by
      intro heq
      have : (0 : ℝ) < bpow beta (mag beta 0 - 1) := bpow_gt_0 _ _
      linarith)]
    ring
  · rw [if_neg h]; simp only [neg_neg]

/-- For `x ≥ 0`, `succ x = x + ulp x`. -/
theorem succ_eq_pos (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : 0 ≤ x) :
    succ beta fexp x = x + ulp beta fexp x := by
  unfold succ; rw [if_pos hx]

/-- `succ (-x) = -pred x`. -/
theorem succ_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    succ beta fexp (-x) = -(pred beta fexp x) := by
  unfold pred; rw [neg_neg]

/-- `pred (-x) = -succ x`. -/
theorem pred_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    pred beta fexp (-x) = -(succ beta fexp x) := by
  unfold pred; rw [neg_neg]

/-! ### Ulp-step bounds against `bpow` -/

/-- For `0 < x` in the format and `x < bpow e`, the next-up step `x + ulp x`
still fits under `bpow e`. -/
theorem id_p_ulp_le_bpow (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {e : ℤ}
    (hx : 0 < x) (Fx : generic_format beta fexp x)
    (h : x < bpow beta e) :
    x + ulp beta fexp x ≤ bpow beta e := by
  set m := Ztrunc (scaled_mantissa beta fexp x)
  set ce := cexp beta fexp x with hce_def
  have hxe : x = F2R (beta := beta) ⟨m, ce⟩ := Fx
  have hm_pos : 0 < m := gt_0_F2R (by rw [← hxe]; exact hx)
  rw [ulp_neq_0 beta fexp (ne_of_gt hx)]
  show x + bpow beta ce ≤ bpow beta e
  have h_mp1 : x + bpow beta ce = F2R (beta := beta) ⟨m + 1, ce⟩ := by
    unfold F2R
    show x + bpow beta ce = (↑(m + 1) : ℝ) * bpow beta ce
    have hx_eq : x = (↑m : ℝ) * bpow beta ce := hxe
    push_cast; linarith
  rw [h_mp1]
  apply F2R_p1_le_bpow hm_pos
  rw [← hxe]; exact h

/-- For `x` in the format with `x ≠ ulp x` and `bpow e < x`, the next-down
step `x - ulp x` still lies above `bpow e`. -/
theorem id_m_ulp_ge_bpow (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {e : ℤ}
    (Fx : generic_format beta fexp x) (hxu : x ≠ ulp beta fexp x)
    (h : bpow beta e < x) :
    bpow beta e ≤ x - ulp beta fexp x := by
  have hx_pos : 0 < x := lt_of_le_of_lt (bpow_ge_0 _ _) h
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  set m := Ztrunc (scaled_mantissa beta fexp x)
  set ce := cexp beta fexp x with hce_def
  have hxe : x = F2R (beta := beta) ⟨m, ce⟩ := Fx
  have hm_pos : 0 < m := gt_0_F2R (by rw [← hxe]; exact hx_pos)
  have hm_ge_1 : 1 ≤ m := hm_pos
  rcases lt_or_eq_of_le hm_ge_1 with hm_gt | hm_eq
  · -- 1 < m: use bpow_le_F2R_m1
    rw [ulp_neq_0 beta fexp hx_ne]
    show bpow beta e ≤ x - bpow beta ce
    have h_mm1 : x - bpow beta ce = F2R (beta := beta) ⟨m - 1, ce⟩ := by
      unfold F2R
      show x - bpow beta ce = (↑(m - 1) : ℝ) * bpow beta ce
      have hx_eq : x = (↑m : ℝ) * bpow beta ce := hxe
      push_cast; linarith
    rw [h_mm1]
    apply bpow_le_F2R_m1 hm_gt
    rw [← hxe]; exact h
  · -- m = 1: x = bpow (cexp x) = ulp x, contradicting hxu.
    exfalso
    apply hxu
    rw [ulp_neq_0 beta fexp hx_ne]
    show x = bpow beta ce
    have hx_eq : x = (↑m : ℝ) * bpow beta ce := hxe
    rw [hx_eq, show m = 1 from hm_eq.symm]
    push_cast; ring

end LeanFlocq
