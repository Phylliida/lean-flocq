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

/-- For any two indices in the small regime of `fexp` (i.e., `n ≤ fexp n` and
`m ≤ fexp m`), `fexp n = fexp m`. The small regime stabilizes to a constant. -/
theorem fexp_negligible_exp_eq {fexp : ℤ → ℤ} (hValid : Valid_exp fexp)
    {n m : ℤ} (hn : n ≤ fexp n) (hm : m ≤ fexp m) : fexp n = fexp m := by
  rcases le_or_gt n m with hle | hgt
  · -- n ≤ m: use stabilization at m (applied to n ≤ fexp m).
    have h_stab_m := (hValid m).2 hm
    have h_n_le_fxm : n ≤ fexp m := le_trans hle hm
    exact h_stab_m.2 n h_n_le_fxm
  · -- m < n: use stabilization at n (applied to m ≤ fexp n).
    have h_stab_n := (hValid n).2 hn
    have h_m_le_fxn : m ≤ fexp n := le_trans (le_of_lt hgt) hn
    exact (h_stab_n.2 m h_m_le_fxn).symm

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

/-! ### Format preservation under ulp steps -/

/-- `ulp 0` is in the format. -/
theorem generic_format_ulp_0 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp) :
    generic_format beta fexp (ulp beta fexp 0) := by
  unfold ulp; rw [if_pos rfl]
  cases h : negligible_exp fexp with
  | none => exact generic_format_0 beta fexp
  | some n =>
    -- bpow (fexp n) is in the format because fexp (fexp n + 1) ≤ fexp n
    -- (from Valid_exp's stabilization branch, since n ≤ fexp n).
    apply generic_format_bpow beta fexp
    have hn_le : n ≤ fexp n := negligible_exp_some h
    exact ((hValid n).2 hn_le).1

/-- For positive `x` in the format, `x + ulp x` is still in the format. -/
theorem generic_format_succ_aux1 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x) :
    generic_format beta fexp (x + ulp beta fexp x) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_low : bpow beta (mag beta x - 1) ≤ x := by
    have := bpow_mag_le beta hx_ne
    rwa [abs_of_pos hx] at this
  have h_high : x < bpow beta (mag beta x) := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos hx] at this
  -- id_p_ulp_le_bpow gives x + ulp x ≤ bpow (mag x).
  have h_le := id_p_ulp_le_bpow beta fexp hx Fx h_high
  rcases lt_or_eq_of_le h_le with h_lt | h_eq
  · -- x + ulp x < bpow (mag x): same magnitude band, mantissa is m + 1.
    set m := Ztrunc (scaled_mantissa beta fexp x)
    set ce := cexp beta fexp x with hce_def
    have hxe : x = F2R (beta := beta) ⟨m, ce⟩ := Fx
    have h_sum_eq : x + ulp beta fexp x = F2R (beta := beta) ⟨m + 1, ce⟩ := by
      rw [ulp_neq_0 beta fexp hx_ne]
      show x + bpow beta ce = (↑(m + 1) : ℝ) * bpow beta ce
      have hx_eq : x = (↑m : ℝ) * bpow beta ce := hxe
      push_cast; linarith
    rw [h_sum_eq]
    apply generic_format_F2R beta fexp _ _
    intro _
    -- mag(x + ulp x) = mag x, so cexp(x + ulp x) = ce.
    have h_mag_sum : mag beta (x + ulp beta fexp x) = mag beta x := by
      apply mag_unique_pos beta
      · linarith [ulp_ge_0 beta fexp x]
      · exact h_lt
    rw [show F2R (beta := beta) ⟨m + 1, ce⟩ = x + ulp beta fexp x from h_sum_eq.symm]
    show cexp beta fexp (x + ulp beta fexp x) ≤ ce
    have h_ce_unfold : ce = fexp (mag beta x) := hce_def
    rw [h_ce_unfold]
    unfold cexp
    rw [h_mag_sum]
  · -- x + ulp x = bpow (mag x): apply generic_format_bpow' (since fexp (mag x) < mag x).
    rw [show x + ulp beta fexp x = bpow beta (mag beta x) from h_eq]
    apply generic_format_bpow' beta fexp hValid
    exact le_of_lt (mag_generic_gt beta fexp hValid hx_ne Fx)

/-- For positive `x` in the format, *not* sitting on the lower bpow boundary
of its magnitude band, `x - ulp x` is in the format. -/
theorem generic_format_pred_aux1 (beta : radix) (fexp : ℤ → ℤ) (_hValid : Valid_exp fexp)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x)
    (hbnd : x ≠ bpow beta (mag beta x - 1)) :
    generic_format beta fexp (x - ulp beta fexp x) := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_low : bpow beta (mag beta x - 1) ≤ x := by
    have := bpow_mag_le beta hx_ne
    rwa [abs_of_pos hx] at this
  have h_high : x < bpow beta (mag beta x) := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos hx] at this
  have h_low_strict : bpow beta (mag beta x - 1) < x := lt_of_le_of_ne h_low (Ne.symm hbnd)
  -- x ≠ ulp x (else `x = bpow(cexp x)` forces impossible integer relation).
  have h_x_ne_ulp : x ≠ ulp beta fexp x := by
    intro h_eq
    rw [ulp_neq_0 beta fexp hx_ne] at h_eq
    have h1 : bpow beta (mag beta x - 1) < bpow beta (cexp beta fexp x) := by
      rw [← h_eq]; exact h_low_strict
    have h2 : bpow beta (cexp beta fexp x) < bpow beta (mag beta x) := by
      rw [← h_eq]; exact h_high
    have hi1 : mag beta x - 1 < cexp beta fexp x := lt_bpow beta h1
    have hi2 : cexp beta fexp x < mag beta x := lt_bpow beta h2
    omega
  have h_x_minus_ulp_ge : bpow beta (mag beta x - 1) ≤ x - ulp beta fexp x :=
    id_m_ulp_ge_bpow beta fexp Fx h_x_ne_ulp h_low_strict
  have h_x_minus_ulp_lt : x - ulp beta fexp x < bpow beta (mag beta x) := by
    have : 0 ≤ ulp beta fexp x := ulp_ge_0 beta fexp x
    linarith
  set m := Ztrunc (scaled_mantissa beta fexp x)
  set ce := cexp beta fexp x with hce_def
  have hxe : x = F2R (beta := beta) ⟨m, ce⟩ := Fx
  have h_diff_eq : x - ulp beta fexp x = F2R (beta := beta) ⟨m - 1, ce⟩ := by
    rw [ulp_neq_0 beta fexp hx_ne]
    show x - bpow beta ce = (↑(m - 1) : ℝ) * bpow beta ce
    have hx_eq : x = (↑m : ℝ) * bpow beta ce := hxe
    push_cast; linarith
  rw [h_diff_eq]
  apply generic_format_F2R beta fexp _ _
  intro _
  rw [show F2R (beta := beta) ⟨m - 1, ce⟩ = x - ulp beta fexp x from h_diff_eq.symm]
  show cexp beta fexp (x - ulp beta fexp x) ≤ ce
  have h_mag_diff : mag beta (x - ulp beta fexp x) = mag beta x :=
    mag_unique_pos beta h_x_minus_ulp_ge h_x_minus_ulp_lt
  have h_ce_unfold : ce = fexp (mag beta x) := hce_def
  rw [h_ce_unfold]
  unfold cexp
  rw [h_mag_diff]

/-- For positive `x` in the format that *is* on the bpow lower boundary
of its magnitude band (`x = bpow (mag x - 1)`), the predecessor uses a
*shrunken* step `bpow (fexp (mag x - 1))`, and `x - bpow (fexp (mag x - 1))`
is still in the format. -/
theorem generic_format_pred_aux2 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (_hx : 0 < x) (Fx : generic_format beta fexp x)
    (hbnd : x = bpow beta (mag beta x - 1)) :
    generic_format beta fexp (x - bpow beta (fexp (mag beta x - 1))) := by
  set e := mag beta x with he_def
  have h_F_bpow : generic_format beta fexp (bpow beta (e - 1)) := by
    rw [← hbnd]; exact Fx
  have hfe_le : fexp (e - 1) ≤ e - 1 :=
    generic_format_bpow_inv beta fexp hValid (e - 1) h_F_bpow
  rcases lt_or_eq_of_le hfe_le with hfe_lt | hfe_eq
  · -- fexp(e - 1) < e - 1: f decomposes as (β^(e-1-fexp(e-1)) - 1) · bpow(fexp(e-1)).
    have hd : 0 ≤ e - 1 - fexp (e - 1) := by linarith
    have h_decomp : x - bpow beta (fexp (e - 1))
        = F2R (beta := beta)
            ⟨(beta.val : ℤ) ^ (e - 1 - fexp (e - 1)).toNat - 1, fexp (e - 1)⟩ := by
      rw [hbnd]
      unfold F2R
      show bpow beta (e - 1) - bpow beta (fexp (e - 1))
          = (((beta.val ^ (e - 1 - fexp (e - 1)).toNat : ℤ) - 1 : ℤ) : ℝ)
              * bpow beta (fexp (e - 1))
      have hcast : (((beta.val ^ (e - 1 - fexp (e - 1)).toNat : ℤ) - 1 : ℤ) : ℝ)
          = ((beta.val ^ (e - 1 - fexp (e - 1)).toNat : ℤ) : ℝ) - 1 := by push_cast; rfl
      rw [hcast, IZR_Zpower beta hd]
      have h_split : bpow beta (e - 1)
          = bpow beta (e - 1 - fexp (e - 1)) * bpow beta (fexp (e - 1)) := by
        rw [← bpow_plus]; congr 1; ring
      rw [h_split]; ring
    rw [h_decomp]
    apply generic_format_F2R beta fexp _ _
    intro _
    rw [show F2R (beta := beta)
            ⟨(beta.val : ℤ) ^ (e - 1 - fexp (e - 1)).toNat - 1, fexp (e - 1)⟩
            = x - bpow beta (fexp (e - 1)) from h_decomp.symm]
    -- Goal: cexp(x - bpow(fexp(e-1))) ≤ fexp(e-1).
    -- Show mag(x - bpow(fexp(e-1))) = e - 1.
    have h_2_le_beta : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
    have h_bpow_fe_le_e2 : bpow beta (fexp (e - 1)) ≤ bpow beta (e - 2) :=
      bpow_le beta (by linarith)
    have h_beta_eq : (beta.val : ℝ) * bpow beta (e - 2) = bpow beta (e - 1) := by
      rw [show (beta.val : ℝ) = bpow beta 1 from (bpow_one beta).symm, ← bpow_plus]
      congr 1; ring
    have h_f_lb : bpow beta (e - 2) ≤ x - bpow beta (fexp (e - 1)) := by
      have h1 : bpow beta (e - 2) + bpow beta (fexp (e - 1)) ≤ bpow beta (e - 1) := by
        calc bpow beta (e - 2) + bpow beta (fexp (e - 1))
            ≤ bpow beta (e - 2) + bpow beta (e - 2) := by linarith
          _ = 2 * bpow beta (e - 2) := by ring
          _ ≤ (beta.val : ℝ) * bpow beta (e - 2) :=
              mul_le_mul_of_nonneg_right h_2_le_beta (bpow_ge_0 _ _)
          _ = bpow beta (e - 1) := h_beta_eq
      rw [hbnd]; linarith
    have h_f_ub : x - bpow beta (fexp (e - 1)) < bpow beta (e - 1) := by
      have : 0 < bpow beta (fexp (e - 1)) := bpow_gt_0 _ _
      rw [hbnd]; linarith
    have h_mag_f : mag beta (x - bpow beta (fexp (e - 1))) = e - 1 :=
      mag_unique_pos beta (by rw [show (e - 1) - 1 = e - 2 from by ring]; exact h_f_lb) h_f_ub
    show cexp beta fexp (x - bpow beta (fexp (e - 1))) ≤ fexp (e - 1)
    unfold cexp
    rw [h_mag_f]
  · -- fexp(e-1) = e-1: f = bpow(e-1) - bpow(e-1) = 0.
    have h_zero : x - bpow beta (fexp (e - 1)) = 0 := by
      rw [hbnd, hfe_eq]; ring
    rw [h_zero]
    exact generic_format_0 beta fexp

/-- The full `pred_pos`: for positive `x` in the format, `pred_pos x` is in
the format. -/
theorem generic_format_pred_pos (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (Fx : generic_format beta fexp x) (hx : 0 < x) :
    generic_format beta fexp (pred_pos beta fexp x) := by
  unfold pred_pos
  by_cases h : x = bpow beta (mag beta x - 1)
  · rw [if_pos h]
    exact generic_format_pred_aux2 beta fexp hValid hx Fx h
  · rw [if_neg h]
    exact generic_format_pred_aux1 beta fexp hValid hx Fx h

/-- The successor of any element of the format is still in the format. -/
theorem generic_format_succ (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (Fx : generic_format beta fexp x) :
    generic_format beta fexp (succ beta fexp x) := by
  unfold succ
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    rcases lt_or_eq_of_le hx with hx_pos | hx_eq
    · exact generic_format_succ_aux1 beta fexp hValid hx_pos Fx
    · -- x = 0: succ x = 0 + ulp 0 = ulp 0.
      rw [← hx_eq, zero_add]
      exact generic_format_ulp_0 beta fexp hValid
  · rw [if_neg hx]
    push_neg at hx
    apply generic_format_opp
    exact generic_format_pred_pos beta fexp hValid
      (generic_format_opp beta fexp Fx) (by linarith)

/-- The predecessor of any element of the format is still in the format. -/
theorem generic_format_pred (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (Fx : generic_format beta fexp x) :
    generic_format beta fexp (pred beta fexp x) := by
  unfold pred
  apply generic_format_opp
  exact generic_format_succ beta fexp hValid (generic_format_opp beta fexp Fx)

/-! ### Strict and non-strict order properties of succ/pred -/

/-- `pred_pos x < x` for nonzero `x` (the step is strictly positive). -/
theorem pred_pos_lt_id (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : x ≠ 0) :
    pred_pos beta fexp x < x := by
  unfold pred_pos
  by_cases h : x = bpow beta (mag beta x - 1)
  · rw [if_pos h]
    have : 0 < bpow beta (fexp (mag beta x - 1)) := bpow_gt_0 _ _
    linarith
  · rw [if_neg h, ulp_neq_0 beta fexp hx]
    have : 0 < bpow beta (cexp beta fexp x) := bpow_gt_0 _ _
    linarith

/-- `x < succ x` for nonzero `x`. -/
theorem succ_gt_id (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : x ≠ 0) :
    x < succ beta fexp x := by
  unfold succ
  by_cases h : 0 ≤ x
  · rw [if_pos h, ulp_neq_0 beta fexp hx]
    have : 0 < bpow beta (cexp beta fexp x) := bpow_gt_0 _ _
    linarith
  · rw [if_neg h]
    push_neg at h
    have h_neg_x_ne : -x ≠ 0 := fun hh => hx (by linarith)
    have := pred_pos_lt_id beta fexp h_neg_x_ne
    linarith

/-- `pred x < x` for nonzero `x`. -/
theorem pred_lt_id (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : x ≠ 0) :
    pred beta fexp x < x := by
  unfold pred
  have h_neg_x_ne : -x ≠ 0 := fun hh => hx (by linarith)
  have := succ_gt_id beta fexp h_neg_x_ne
  linarith

/-- `x ≤ succ x` for any `x` (non-strict version covering `x = 0`). -/
theorem succ_ge_id (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    x ≤ succ beta fexp x := by
  by_cases hx : x = 0
  · rw [hx]
    unfold succ
    rw [if_pos (le_refl 0), zero_add]
    exact ulp_ge_0 beta fexp 0
  · exact le_of_lt (succ_gt_id beta fexp hx)

/-- `pred x ≤ x` for any `x`. -/
theorem pred_le_id (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    pred beta fexp x ≤ x := by
  unfold pred
  have := succ_ge_id beta fexp (-x)
  linarith

/-- For positive `x` in the format, `pred_pos x` is non-negative. -/
theorem pred_pos_ge_0 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x) :
    0 ≤ pred_pos beta fexp x := by
  unfold pred_pos
  by_cases h : x = bpow beta (mag beta x - 1)
  · rw [if_pos h]
    have h_F_bpow : generic_format beta fexp (bpow beta (mag beta x - 1)) := by
      rw [← h]; exact Fx
    have h_fe_le : fexp (mag beta x - 1) ≤ mag beta x - 1 :=
      generic_format_bpow_inv beta fexp hValid (mag beta x - 1) h_F_bpow
    have h_bpow_le : bpow beta (fexp (mag beta x - 1)) ≤ bpow beta (mag beta x - 1) :=
      bpow_le beta h_fe_le
    -- x = bpow(mag x - 1), so the step bpow(fexp(mag x - 1)) ≤ x.
    rw [show bpow beta (mag beta x - 1) = x from h.symm] at h_bpow_le
    linarith
  · rw [if_neg h]
    have : ulp beta fexp x ≤ x := ulp_le_id beta fexp hx Fx
    linarith

/-- For positive `x` in the format, `pred x` is non-negative. -/
theorem pred_ge_0 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x) :
    0 ≤ pred beta fexp x := by
  rw [pred_eq_pos beta fexp (le_of_lt hx)]
  exact pred_pos_ge_0 beta fexp hValid hx Fx

/-- `succ 0 = ulp 0`. -/
@[simp]
theorem succ_0 (beta : radix) (fexp : ℤ → ℤ) :
    succ beta fexp 0 = ulp beta fexp 0 := by
  unfold succ
  rw [if_pos (le_refl 0), zero_add]

/-- `pred 0 = -(ulp 0)`. -/
@[simp]
theorem pred_0 (beta : radix) (fexp : ℤ → ℤ) :
    pred beta fexp 0 = -(ulp beta fexp 0) := by
  unfold pred
  rw [neg_zero, succ_0]

/-- `pred (ulp 0) = 0`. -/
theorem pred_ulp_0 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp) :
    pred beta fexp (ulp beta fexp 0) = 0 := by
  rw [pred_eq_pos beta fexp (ulp_ge_0 beta fexp 0)]
  unfold pred_pos
  cases h_neg : negligible_exp fexp with
  | none =>
    -- `ulp 0 = 0` in this case.
    have h_ulp_0 : ulp beta fexp 0 = 0 := by
      unfold ulp; rw [if_pos rfl, h_neg]
    rw [h_ulp_0]
    rw [if_neg (by
      have : (0 : ℝ) < bpow beta (mag beta 0 - 1) := bpow_gt_0 _ _
      linarith)]
    rw [h_ulp_0]; ring
  | some n =>
    -- `ulp 0 = bpow (fexp n)`. The pred-pos branch hits the bpow boundary
    -- because `mag (bpow (fexp n)) = fexp n + 1`.
    have h_ulp_0 : ulp beta fexp 0 = bpow beta (fexp n) := by
      unfold ulp; rw [if_pos rfl, h_neg]
    rw [h_ulp_0]
    have h_mag : mag beta (bpow beta (fexp n)) = fexp n + 1 := mag_bpow beta (fexp n)
    rw [h_mag]
    have h_simp : (fexp n + 1 - 1 : ℤ) = fexp n := by ring
    rw [h_simp, if_pos rfl]
    -- Goal: `bpow (fexp n) - bpow (fexp (fexp n)) = 0`. Use Valid_exp's stabilization.
    have h_n_le : n ≤ fexp n := negligible_exp_some h_neg
    have h_stab := (hValid n).2 h_n_le
    have h_fxn : fexp (fexp n) = fexp n := h_stab.2 (fexp n) (le_refl _)
    rw [h_fxn]; ring

/-- `succ_gt_id` lifted to a non-strict comparison: `x ≤ y` (with `y ≠ 0`)
implies `x < succ y`. -/
theorem succ_gt_ge (beta : radix) (fexp : ℤ → ℤ) {x y : ℝ}
    (hy : y ≠ 0) (hxy : x ≤ y) : x < succ beta fexp y :=
  lt_of_le_of_lt hxy (succ_gt_id beta fexp hy)

/-- `pred_lt_id` lifted: `x ≤ y` (with `x ≠ 0`) implies `pred x < y`. -/
theorem pred_lt_le (beta : radix) (fexp : ℤ → ℤ) {x y : ℝ}
    (hx : x ≠ 0) (hxy : x ≤ y) : pred beta fexp x < y :=
  lt_of_lt_of_le (pred_lt_id beta fexp hx) hxy

/-- For positive `x` in the format *not* at the bpow boundary,
`(x - ulp x) + ulp (x - ulp x) = x`. The key fact is that the predecessor
shares its ulp with `x` (same magnitude band, same `cexp`). -/
theorem pred_pos_plus_ulp_aux1 (beta : radix) (fexp : ℤ → ℤ)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x)
    (hbnd : x ≠ bpow beta (mag beta x - 1)) :
    (x - ulp beta fexp x) + ulp beta fexp (x - ulp beta fexp x) = x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have h_low : bpow beta (mag beta x - 1) ≤ x := by
    have := bpow_mag_le beta hx_ne; rwa [abs_of_pos hx] at this
  have h_high : x < bpow beta (mag beta x) := by
    have := bpow_mag_gt beta x; rwa [abs_of_pos hx] at this
  have h_low_strict : bpow beta (mag beta x - 1) < x := lt_of_le_of_ne h_low (Ne.symm hbnd)
  have h_x_ne_ulp : x ≠ ulp beta fexp x := by
    intro h_eq
    rw [ulp_neq_0 beta fexp hx_ne] at h_eq
    have h1 : bpow beta (mag beta x - 1) < bpow beta (cexp beta fexp x) := by
      rw [← h_eq]; exact h_low_strict
    have h2 : bpow beta (cexp beta fexp x) < bpow beta (mag beta x) := by
      rw [← h_eq]; exact h_high
    have hi1 : mag beta x - 1 < cexp beta fexp x := lt_bpow beta h1
    have hi2 : cexp beta fexp x < mag beta x := lt_bpow beta h2
    omega
  have h_pred_lo : bpow beta (mag beta x - 1) ≤ x - ulp beta fexp x :=
    id_m_ulp_ge_bpow beta fexp Fx h_x_ne_ulp h_low_strict
  have h_pred_pos : 0 < x - ulp beta fexp x :=
    lt_of_lt_of_le (bpow_gt_0 _ _) h_pred_lo
  have h_pred_ne : x - ulp beta fexp x ≠ 0 := ne_of_gt h_pred_pos
  have h_pred_hi : x - ulp beta fexp x < bpow beta (mag beta x) := by
    have : 0 ≤ ulp beta fexp x := ulp_ge_0 beta fexp x
    linarith
  have h_mag : mag beta (x - ulp beta fexp x) = mag beta x :=
    mag_unique_pos beta h_pred_lo h_pred_hi
  have h_ulp_eq : ulp beta fexp (x - ulp beta fexp x) = ulp beta fexp x := by
    calc ulp beta fexp (x - ulp beta fexp x)
        = bpow beta (cexp beta fexp (x - ulp beta fexp x)) :=
          ulp_neq_0 beta fexp h_pred_ne
      _ = bpow beta (cexp beta fexp x) := by
          congr 1; unfold cexp; rw [h_mag]
      _ = ulp beta fexp x := (ulp_neq_0 beta fexp hx_ne).symm
  rw [h_ulp_eq]; ring

/-- Boundary case (non-zero): when `x = bpow(mag x - 1)` and the shrunken
predecessor is nonzero, `(x - bpow(fexp(mag x - 1))) + ulp(...) = x`. -/
theorem pred_pos_plus_ulp_aux2 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (_hx : 0 < x) (Fx : generic_format beta fexp x)
    (hbnd : x = bpow beta (mag beta x - 1))
    (hne : x - bpow beta (fexp (mag beta x - 1)) ≠ 0) :
    (x - bpow beta (fexp (mag beta x - 1)))
      + ulp beta fexp (x - bpow beta (fexp (mag beta x - 1)))
      = x := by
  set e := mag beta x with he_def
  have h_F_bpow : generic_format beta fexp (bpow beta (e - 1)) := by
    rw [← hbnd]; exact Fx
  have hfe_le : fexp (e - 1) ≤ e - 1 :=
    generic_format_bpow_inv beta fexp hValid (e - 1) h_F_bpow
  rcases lt_or_eq_of_le hfe_le with hfe_lt | hfe_eq
  · -- fexp(e-1) < e-1: f sits in [bpow(e-2), bpow(e-1)), so mag f = e-1.
    have h_2_le_beta : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
    have h_bpow_fe_le_e2 : bpow beta (fexp (e - 1)) ≤ bpow beta (e - 2) :=
      bpow_le beta (by linarith)
    have h_beta_eq : (beta.val : ℝ) * bpow beta (e - 2) = bpow beta (e - 1) := by
      rw [show (beta.val : ℝ) = bpow beta 1 from (bpow_one beta).symm, ← bpow_plus]
      congr 1; ring
    have h_f_lb : bpow beta (e - 2) ≤ x - bpow beta (fexp (e - 1)) := by
      have h1 : bpow beta (e - 2) + bpow beta (fexp (e - 1)) ≤ bpow beta (e - 1) := by
        calc bpow beta (e - 2) + bpow beta (fexp (e - 1))
            ≤ bpow beta (e - 2) + bpow beta (e - 2) := by linarith
          _ = 2 * bpow beta (e - 2) := by ring
          _ ≤ (beta.val : ℝ) * bpow beta (e - 2) :=
              mul_le_mul_of_nonneg_right h_2_le_beta (bpow_ge_0 _ _)
          _ = bpow beta (e - 1) := h_beta_eq
      rw [hbnd]; linarith
    have h_f_ub : x - bpow beta (fexp (e - 1)) < bpow beta (e - 1) := by
      have : 0 < bpow beta (fexp (e - 1)) := bpow_gt_0 _ _
      rw [hbnd]; linarith
    have h_mag_f : mag beta (x - bpow beta (fexp (e - 1))) = e - 1 :=
      mag_unique_pos beta
        (by rw [show (e - 1) - 1 = e - 2 from by ring]; exact h_f_lb) h_f_ub
    have h_ulp_eq : ulp beta fexp (x - bpow beta (fexp (e - 1)))
        = bpow beta (fexp (e - 1)) := by
      rw [ulp_neq_0 beta fexp hne]
      show bpow beta (cexp beta fexp (x - bpow beta (fexp (e - 1))))
          = bpow beta (fexp (e - 1))
      unfold cexp; rw [h_mag_f]
    rw [h_ulp_eq]; ring
  · -- fexp(e-1) = e-1: x - bpow(fexp(e-1)) = 0, contradicting hne.
    exfalso
    apply hne
    rw [hbnd, hfe_eq]; ring

/-- Boundary case (zero): when `x = bpow(mag x - 1)` and the shrunken
predecessor is zero, then `ulp 0 = x`. The shrinking step reaches all
the way down to zero, and the format's "minimal exponent" picks `x` itself. -/
theorem pred_pos_plus_ulp_aux3 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (_hx : 0 < x) (_Fx : generic_format beta fexp x)
    (hbnd : x = bpow beta (mag beta x - 1))
    (heq : x - bpow beta (fexp (mag beta x - 1)) = 0) :
    ulp beta fexp 0 = x := by
  set e := mag beta x with he_def
  -- From heq: x = bpow(fexp(e-1)). Combined with hbnd: bpow(e-1) = bpow(fexp(e-1)).
  have h_x_eq : x = bpow beta (fexp (e - 1)) := by linarith
  -- bpow injectivity (via strict monotonicity).
  have h_fexp_eq : fexp (e - 1) = e - 1 := by
    have h_bpow_eq : bpow beta (e - 1) = bpow beta (fexp (e - 1)) := by
      rw [← hbnd]; exact h_x_eq
    rcases lt_trichotomy (fexp (e - 1)) (e - 1) with hlt | heq' | hgt
    · exfalso; have := bpow_lt beta hlt; linarith
    · exact heq'
    · exfalso; have := bpow_lt beta hgt; linarith
  have h_em1_small : e - 1 ≤ fexp (e - 1) := by linarith
  cases h_neg : negligible_exp fexp with
  | none =>
    exfalso
    have := negligible_exp_none h_neg (e - 1)
    linarith
  | some n =>
    have h_n_small : n ≤ fexp n := negligible_exp_some h_neg
    have h_fexp_eq_n : fexp n = e - 1 := by
      have h_eq := fexp_negligible_exp_eq hValid h_n_small h_em1_small
      rw [h_eq, h_fexp_eq]
    show ulp beta fexp 0 = x
    unfold ulp
    rw [if_pos rfl, h_neg]
    show bpow beta (fexp n) = x
    rw [h_fexp_eq_n, ← hbnd]

/-- The predecessor-plus-ulp roundtrip: for positive `x` in the format,
`pred_pos x + ulp (pred_pos x) = x`. -/
theorem pred_pos_plus_ulp (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x) :
    pred_pos beta fexp x + ulp beta fexp (pred_pos beta fexp x) = x := by
  unfold pred_pos
  by_cases hbnd : x = bpow beta (mag beta x - 1)
  · rw [if_pos hbnd]
    by_cases h_zero : x - bpow beta (fexp (mag beta x - 1)) = 0
    · rw [h_zero, zero_add]
      exact pred_pos_plus_ulp_aux3 beta fexp hValid hx Fx hbnd h_zero
    · exact pred_pos_plus_ulp_aux2 beta fexp hValid hx Fx hbnd h_zero
  · rw [if_neg hbnd]
    exact pred_pos_plus_ulp_aux1 beta fexp hx Fx hbnd

/-- The predecessor-plus-ulp roundtrip via `pred`. -/
theorem pred_plus_ulp (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (hx : 0 < x) (Fx : generic_format beta fexp x) :
    pred beta fexp x + ulp beta fexp (pred beta fexp x) = x := by
  rw [pred_eq_pos beta fexp (le_of_lt hx)]
  exact pred_pos_plus_ulp beta fexp hValid hx Fx

/-- For positive `x` in the format, `succ` and `pred` are mutual inverses:
`succ (pred x) = x`. -/
theorem succ_pred_pos (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} (Fx : generic_format beta fexp x) (hx : 0 < x) :
    succ beta fexp (pred beta fexp x) = x := by
  rw [pred_eq_pos beta fexp (le_of_lt hx)]
  rw [succ_eq_pos beta fexp (pred_pos_ge_0 beta fexp hValid hx Fx)]
  exact pred_pos_plus_ulp beta fexp hValid hx Fx

/-! ### `Exp_not_FTZ` and ulp monotonicity -/

/-- A `fexp` is `Exp_not_FTZ` if `fexp(fexp e + 1) ≤ fexp e` for all `e`.
This excludes FTZ-like formats where the small regime maps to a fixed
larger value rather than stabilizing. -/
def Exp_not_FTZ (fexp : ℤ → ℤ) : Prop :=
  ∀ e : ℤ, fexp (fexp e + 1) ≤ fexp e

/-- A monotone `fexp` is automatically `Exp_not_FTZ`. -/
theorem monotone_exp_not_FTZ {fexp : ℤ → ℤ} (hValid : Valid_exp fexp)
    (hMon : Monotone_exp fexp) : Exp_not_FTZ fexp := by
  intro e
  rcases lt_or_ge (fexp e) e with hfe | hfe
  · -- fexp e < e: monotonicity gives fexp(fexp e + 1) ≤ fexp e.
    apply hMon; omega
  · -- e ≤ fexp e: stabilization branch.
    exact ((hValid e).2 hfe).1

/-- `ulp 0 ≤ ulp x` for any `x`, given `Exp_not_FTZ`. The "minimum unit"
of the format never exceeds the local ulp. -/
theorem ulp_ge_ulp_0 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (h_NotFTZ : Exp_not_FTZ fexp) (x : ℝ) :
    ulp beta fexp 0 ≤ ulp beta fexp x := by
  by_cases hx : x = 0
  · rw [hx]
  · cases h_neg : negligible_exp fexp with
    | none =>
      -- ulp 0 = 0, trivially.
      have h_ulp_0 : ulp beta fexp 0 = 0 := by
        unfold ulp; rw [if_pos rfl, h_neg]
      rw [h_ulp_0]
      exact ulp_ge_0 beta fexp x
    | some n =>
      have h_n_le : n ≤ fexp n := negligible_exp_some h_neg
      have h_ulp_0 : ulp beta fexp 0 = bpow beta (fexp n) := by
        unfold ulp; rw [if_pos rfl, h_neg]
      rw [h_ulp_0, ulp_neq_0 beta fexp hx]
      apply bpow_le
      show fexp n ≤ cexp beta fexp x
      unfold cexp
      set m := mag beta x with hm_def
      rcases le_or_gt m (fexp m) with hsmall | hlarge
      · -- m in small regime: fexp m = fexp n via fexp_negligible_exp_eq.
        have h_eq := fexp_negligible_exp_eq hValid h_n_le hsmall
        omega
      · -- m large: derive contradiction if fexp m < fexp n.
        by_contra hgt
        push_neg at hgt
        have h_step : fexp m + 1 ≤ fexp n := by omega
        have h_stab := (hValid n).2 h_n_le
        have h_eq : fexp (fexp m + 1) = fexp n := h_stab.2 (fexp m + 1) h_step
        have h_efm : fexp (fexp m + 1) ≤ fexp m := h_NotFTZ m
        omega

/-- For nonneg `x ≤ y` and a monotone `Exp_not_FTZ` `fexp`, `ulp x ≤ ulp y`. -/
theorem ulp_le_pos (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (hMon : Monotone_exp fexp) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ulp beta fexp x ≤ ulp beta fexp y := by
  rcases lt_or_eq_of_le hx with hx_pos | hx_eq
  · have hy_pos : 0 < y := lt_of_lt_of_le hx_pos hxy
    rw [ulp_neq_0 beta fexp (ne_of_gt hx_pos), ulp_neq_0 beta fexp (ne_of_gt hy_pos)]
    apply bpow_le
    unfold cexp
    apply hMon
    apply mag_le_abs beta (ne_of_gt hx_pos)
    rw [abs_of_pos hx_pos, abs_of_pos hy_pos]; exact hxy
  · -- x = 0: use ulp_ge_ulp_0.
    rw [← hx_eq]
    exact ulp_ge_ulp_0 beta fexp hValid (monotone_exp_not_FTZ hValid hMon) y

/-- Ulp monotonicity under absolute value: `|x| ≤ |y| → ulp x ≤ ulp y`. -/
theorem ulp_le (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (hMon : Monotone_exp fexp) {x y : ℝ} (hxy : |x| ≤ |y|) :
    ulp beta fexp x ≤ ulp beta fexp y := by
  rw [← ulp_abs beta fexp x, ← ulp_abs beta fexp y]
  exact ulp_le_pos beta fexp hValid hMon (abs_nonneg _) hxy

/-- The absolute value of a rounded value is at least any in-format
value bounded by `|y|`. Proved via `round_abs_abs`: reduce to nonneg via abs. -/
theorem abs_round_ge_generic (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x y : ℝ}
    (Hx : generic_format beta fexp x) (Hxy : x ≤ |y|) :
    x ≤ |round beta fexp rnd y| := by
  have h := round_abs_abs beta fexp hValid
    (fun a b => x ≤ a → x ≤ b)
    (fun rnd' _ _ _ h_xz => round_ge_generic beta fexp hValid rnd' Hx h_xz)
    rnd y
  exact h Hxy

/-- When `fexp` has no negligible exponent (the small regime is empty),
the rounding of `x` to 0 forces `x = 0` itself. Useful for FLX-like formats. -/
theorem eq_0_round_0_negligible_exp (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (h_neg : negligible_exp fexp = none)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ}
    (Hx : round beta fexp rnd x = 0) : x = 0 := by
  by_contra hx_ne
  -- |x| ≥ bpow (mag x - 1), and bpow (mag x - 1) is in F (no negligible exp).
  have h_lo : bpow beta (mag beta x - 1) ≤ |x| := bpow_mag_le beta hx_ne
  have h_F_bpow : generic_format beta fexp (bpow beta (mag beta x - 1)) := by
    apply generic_format_bpow
    have h_fexp_lt := negligible_exp_none h_neg (mag beta x)
    have h_simp : mag beta x - 1 + 1 = mag beta x := by ring
    rw [h_simp]
    omega
  have h_round_ge : bpow beta (mag beta x - 1) ≤ |round beta fexp rnd x| :=
    abs_round_ge_generic beta fexp hValid rnd h_F_bpow h_lo
  rw [Hx, abs_zero] at h_round_ge
  have : 0 < bpow beta (mag beta x - 1) := bpow_gt_0 _ _
  linarith

/-! ### Rounding error bounds -/

/-- For `x ≠ 0`, the absolute rounding error is strictly less than `ulp x`. -/
theorem error_lt_ulp (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ} (hx : x ≠ 0) :
    |round beta fexp rnd x - x| < ulp beta fexp x := by
  by_cases hfmt : generic_format beta fexp x
  · -- x is in F: round x = x.
    rw [round_generic beta fexp rnd hfmt]
    rw [show x - x = 0 from by ring, abs_zero]
    rw [ulp_neq_0 beta fexp hx]
    exact bpow_gt_0 _ _
  · rcases round_DN_or_UP beta fexp rnd x with hDN | hUP
    · -- round x = round_DN x: error is x - round_DN x.
      rw [hDN]
      have h_DN_le : round beta fexp (fun y : ℝ => ⌊y⌋) x ≤ x :=
        (round_DN_pt beta fexp hValid x).2.1
      rw [show round beta fexp (fun y : ℝ => ⌊y⌋) x - x
          = -(x - round beta fexp (fun y : ℝ => ⌊y⌋) x) from by ring,
          abs_neg, abs_of_nonneg (by linarith)]
      have h_UP_eq := round_UP_DN_ulp beta fexp hfmt
      have h_UP_ge : x ≤ round beta fexp (fun y : ℝ => ⌈y⌉) x :=
        (round_UP_pt beta fexp hValid x).2.1
      have h_UP_strict : x < round beta fexp (fun y : ℝ => ⌈y⌉) x := by
        rcases lt_or_eq_of_le h_UP_ge with hlt | heq
        · exact hlt
        · exfalso; apply hfmt
          rw [heq]; exact generic_format_round beta fexp hValid _ x
      linarith
    · -- round x = round_UP x: error is round_UP x - x.
      rw [hUP]
      have h_UP_ge : x ≤ round beta fexp (fun y : ℝ => ⌈y⌉) x :=
        (round_UP_pt beta fexp hValid x).2.1
      rw [abs_of_nonneg (by linarith)]
      have h_UP_eq := round_UP_DN_ulp beta fexp hfmt
      have h_DN_le : round beta fexp (fun y : ℝ => ⌊y⌋) x ≤ x :=
        (round_DN_pt beta fexp hValid x).2.1
      have h_DN_strict : round beta fexp (fun y : ℝ => ⌊y⌋) x < x := by
        rcases lt_or_eq_of_le h_DN_le with hlt | heq
        · exact hlt
        · exfalso; apply hfmt
          rw [← heq]; exact generic_format_round beta fexp hValid _ x
      linarith

/-- The non-strict version: the absolute rounding error is at most `ulp x`. -/
theorem error_le_ulp (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] (x : ℝ) :
    |round beta fexp rnd x - x| ≤ ulp beta fexp x := by
  by_cases hx : x = 0
  · rw [hx, round_0, sub_zero, abs_zero]
    exact ulp_ge_0 beta fexp 0
  · exact le_of_lt (error_lt_ulp beta fexp hValid rnd hx)

/-- For round-to-nearest, the absolute error is at most `ulp x / 2`. -/
theorem error_le_half_ulp (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (choice : ℤ → Bool) (x : ℝ) :
    |round beta fexp (Znearest choice) x - x| ≤ (1 / 2) * ulp beta fexp x := by
  by_cases hfmt : generic_format beta fexp x
  · rw [round_generic beta fexp _ hfmt]
    rw [show x - x = 0 from by ring, abs_zero]
    have : 0 ≤ ulp beta fexp x := ulp_ge_0 beta fexp x
    linarith
  · set d := round beta fexp (fun y : ℝ => ⌊y⌋) x with hd_def
    set u := round beta fexp (fun y : ℝ => ⌈y⌉) x with hu_def
    have h_u_eq : u = d + ulp beta fexp x := round_UP_DN_ulp beta fexp hfmt
    have h_DN_le : d ≤ x := (round_DN_pt beta fexp hValid x).2.1
    have h_UP_ge : x ≤ u := (round_UP_pt beta fexp hValid x).2.1
    have h_F_d : generic_format beta fexp d := generic_format_round beta fexp hValid _ x
    have h_F_u : generic_format beta fexp u := generic_format_round beta fexp hValid _ x
    have hRN := round_N_pt beta fexp hValid choice x
    have h_ulp : u - d = ulp beta fexp x := by rw [h_u_eq]; ring
    rcases le_or_gt (x - d) (u - x) with H | H
    · have h1 : |round beta fexp (Znearest choice) x - x| ≤ |d - x| := hRN.2 d h_F_d
      rw [abs_of_nonpos (by linarith : d - x ≤ 0)] at h1
      linarith
    · have h1 : |round beta fexp (Znearest choice) x - x| ≤ |u - x| := hRN.2 u h_F_u
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - x)] at h1
      linarith

/-- Adding `0 ≤ eps < ulp x` to a positive in-format `x` preserves the magnitude.
The ulp-step is exactly the size of the magnitude band the value sits in. -/
theorem mag_plus_eps (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} (hx : 0 < x)
    (Fx : generic_format beta fexp x)
    {eps : ℝ} (heps_nn : 0 ≤ eps) (heps_lt : eps < ulp beta fexp x) :
    mag beta (x + eps) = mag beta x := by
  apply mag_unique_pos beta
  · have h_low : bpow beta (mag beta x - 1) ≤ x := by
      have := bpow_mag_le beta (ne_of_gt hx)
      rwa [abs_of_pos hx] at this
    linarith
  · set m := Ztrunc (scaled_mantissa beta fexp x)
    set ce := cexp beta fexp x with hce_def
    have hxe : x = F2R (beta := beta) ⟨m, ce⟩ := Fx
    have hm_pos : 0 < m := gt_0_F2R (by rw [← hxe]; exact hx)
    have h_high : x < bpow beta (mag beta x) := by
      have := bpow_mag_gt beta x
      rwa [abs_of_pos hx] at this
    have h_F2R_p1 : F2R (beta := beta) ⟨m + 1, ce⟩ ≤ bpow beta (mag beta x) := by
      apply F2R_p1_le_bpow hm_pos
      rw [← hxe]; exact h_high
    have h_eq : F2R (beta := beta) ⟨m + 1, ce⟩ = x + ulp beta fexp x := by
      rw [ulp_neq_0 beta fexp (ne_of_gt hx)]
      unfold F2R
      show (↑(m + 1) : ℝ) * bpow beta ce = x + bpow beta ce
      have hx_eq : x = (↑m : ℝ) * bpow beta ce := hxe
      push_cast; linarith
    rw [h_eq] at h_F2R_p1
    linarith

end LeanFlocq
