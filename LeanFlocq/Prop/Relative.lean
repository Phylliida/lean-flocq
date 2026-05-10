/-
Lean port of Coq Flocq's `Prop/Relative.v` — relative-error bounds for
generic, FLX, and FLT formats.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FLX
import LeanFlocq.Core.FLT
import LeanFlocq.Core.Ulp

namespace LeanFlocq

open radix (radix2)

/-! ### Conversion between absolute and relative error bounds -/

/-- If the absolute error is strictly bounded by `b * |x|` whenever `x ≠ 0`,
then there is a relative error `eps` with `|eps| < b` such that
`round x = x * (1 + eps)`. -/
theorem relative_error_lt_conversion (beta : radix) (fexp : ℤ → ℤ)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} {b : ℝ} (Hb : 0 < b)
    (Hxb : x ≠ 0 → |round beta fexp rnd x - x| < b * |x|) :
    ∃ eps : ℝ, |eps| < b ∧ round beta fexp rnd x = x * (1 + eps) := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [abs_zero]; exact Hb
    · rw [hx, zero_mul, round_0]
  · have Hxb' := Hxb hx
    refine ⟨(round beta fexp rnd x - x) / x, ?_, ?_⟩
    · rw [abs_div, div_lt_iff₀ (abs_pos.mpr hx)]
      exact Hxb'
    · field_simp; ring

/-- The non-strict version. -/
theorem relative_error_le_conversion (beta : radix) (fexp : ℤ → ℤ)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} {b : ℝ} (Hb : 0 ≤ b)
    (Hxb : |round beta fexp rnd x - x| ≤ b * |x|) :
    ∃ eps : ℝ, |eps| ≤ b ∧ round beta fexp rnd x = x * (1 + eps) := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [abs_zero]; exact Hb
    · rw [hx, zero_mul, round_0]
  · refine ⟨(round beta fexp rnd x - x) / x, ?_, ?_⟩
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr hx)]
      exact Hxb
    · field_simp; ring

/-- Inverse of `_le_conversion`: a `1 + eps` form gives the absolute bound. -/
theorem relative_error_le_conversion_inv (beta : radix) (fexp : ℤ → ℤ)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (x : ℝ) (b : ℝ)
    (h : ∃ eps : ℝ, |eps| ≤ b ∧ round beta fexp rnd x = x * (1 + eps)) :
    |round beta fexp rnd x - x| ≤ b * |x| := by
  obtain ⟨eps, Beps, Heps⟩ := h
  rw [Heps, show x * (1 + eps) - x = eps * x from by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right Beps (abs_nonneg _)

/-- Variant where the relative form is expressed against the rounded value
rather than `x`. -/
theorem relative_error_le_conversion_round_inv (beta : radix) (fexp : ℤ → ℤ)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (x : ℝ) (b : ℝ)
    (h : ∃ eps : ℝ, |eps| ≤ b ∧ x = round beta fexp rnd x * (1 + eps)) :
    |round beta fexp rnd x - x| ≤ b * |round beta fexp rnd x| := by
  obtain ⟨eps, Beps, Heps⟩ := h
  set rx := round beta fexp rnd x with hrx
  have hsub : rx - x = -(eps * rx) := by rw [Heps]; ring
  rw [hsub, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_right Beps (abs_nonneg _)

/-! ### Generic-format relative-error bounds

The setup: a valid exponent function `fexp`, an integer threshold `emin`,
a precision `p`, and the hypothesis `Hmin` saying that above `emin` the
format has at least `p` significant digits.
-/

/-- Any rounding satisfies `|round x - x| < β^(-p+1) * |x|` whenever
`|x| ≥ β^emin`. -/
theorem relative_error (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} (Hx : bpow beta emin ≤ |x|) :
    |round beta fexp rnd x - x| < bpow beta (-p + 1) * |x| := by
  have hxne : x ≠ 0 := by
    intro hxz
    rw [hxz, abs_zero] at Hx
    exact absurd Hx (not_le_of_gt (bpow_gt_0 _ _))
  refine lt_of_lt_of_le (error_lt_ulp beta fexp hValid rnd hxne) ?_
  rw [ulp_neq_0 beta fexp hxne]
  unfold cexp
  set ex := mag beta x with hex_def
  have h_low : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta hxne
  have h_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have h_emin_lt : emin < ex := lt_bpow beta (lt_of_le_of_lt Hx h_high)
  have h_fexp_le : fexp ex ≤ -p + 1 + (ex - 1) := by
    have := Hmin ex h_emin_lt; linarith
  calc bpow beta (fexp ex)
      ≤ bpow beta (-p + 1 + (ex - 1)) := bpow_le beta h_fexp_le
    _ = bpow beta (-p + 1) * bpow beta (ex - 1) := bpow_plus beta _ _
    _ ≤ bpow beta (-p + 1) * |x| :=
        mul_le_mul_of_nonneg_left h_low (bpow_ge_0 _ _)

/-- The `1 + ε` form: there exists `eps` with `|eps| < β^(-p+1)` such that
`round x = x * (1 + eps)`. -/
theorem relative_error_ex (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} (Hx : bpow beta emin ≤ |x|) :
    ∃ eps : ℝ, |eps| < bpow beta (-p + 1) ∧ round beta fexp rnd x = x * (1 + eps) :=
  relative_error_lt_conversion beta fexp rnd (bpow_gt_0 _ _)
    (fun _ => relative_error beta fexp hValid emin p Hmin rnd Hx)

/-- A version where `x` is given as `F2R ⟨m, emin⟩`: any nonzero such `x`
automatically satisfies `|x| ≥ β^emin`. -/
theorem relative_error_F2R_emin (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (m : ℤ) (Hx : F2R (beta := beta) ⟨m, emin⟩ ≠ 0) :
    |round beta fexp rnd (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      < bpow beta (-p + 1) * |F2R (beta := beta) ⟨m, emin⟩| := by
  apply relative_error beta fexp hValid emin p Hmin rnd
  rw [← F2R_Zabs]
  apply bpow_le_F2R
  have h_pos : 0 < |m| := by
    rcases lt_trichotomy m 0 with hm | hm | hm
    · rw [abs_of_neg hm]; omega
    · exfalso; apply Hx; rw [hm]; exact F2R_0 emin
    · rw [abs_of_pos hm]; exact hm
  exact h_pos

/-- The `_ex` form for `F2R`-shaped inputs at the threshold. -/
theorem relative_error_F2R_emin_ex (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (m : ℤ) :
    ∃ eps : ℝ, |eps| < bpow beta (-p + 1) ∧
      round beta fexp rnd (F2R (beta := beta) ⟨m, emin⟩)
        = F2R (beta := beta) ⟨m, emin⟩ * (1 + eps) :=
  relative_error_lt_conversion beta fexp rnd (bpow_gt_0 _ _)
    (fun hne => relative_error_F2R_emin beta fexp hValid emin p Hmin rnd m hne)

/-- Bound on the rounded value: `|round x| ≥ β^(ex-1)` is preserved from `|x|`. -/
private theorem bpow_le_abs_round (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {ex : ℤ} (h_fexp_lt : fexp ex ≤ ex - 1)
    {x : ℝ} (Hx : bpow beta (ex - 1) ≤ |x|) :
    bpow beta (ex - 1) ≤ |round beta fexp rnd x| := by
  -- Apply round_abs_abs to lift the nonneg case.
  have HP : ∀ (rnd' : ℝ → ℤ) [Valid_rnd rnd'] (y : ℝ), 0 ≤ y →
      bpow beta (ex - 1) ≤ y → bpow beta (ex - 1) ≤ round beta fexp rnd' y := by
    intro rnd' _ y _ hy
    have h_fmt : generic_format beta fexp (bpow beta (ex - 1)) := by
      apply generic_format_bpow beta fexp
      have : fexp (ex - 1 + 1) = fexp ex := by ring_nf
      rw [this]; exact h_fexp_lt
    have h_eq : round beta fexp rnd' (bpow beta (ex - 1)) = bpow beta (ex - 1) :=
      round_generic beta fexp rnd' h_fmt
    rw [← h_eq]
    exact round_le beta fexp hValid rnd' hy
  exact round_abs_abs beta fexp hValid
    (fun u v => bpow beta (ex - 1) ≤ u → bpow beta (ex - 1) ≤ v) HP rnd x Hx

/-- A bound on the relative error w.r.t. the rounded value. -/
theorem relative_error_round (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] (Hp : 0 < p)
    {x : ℝ} (Hx : bpow beta emin ≤ |x|) :
    |round beta fexp rnd x - x| < bpow beta (-p + 1) * |round beta fexp rnd x| := by
  have hxne : x ≠ 0 := by
    intro hxz
    rw [hxz, abs_zero] at Hx
    exact absurd Hx (not_le_of_gt (bpow_gt_0 _ _))
  refine lt_of_lt_of_le (error_lt_ulp beta fexp hValid rnd hxne) ?_
  rw [ulp_neq_0 beta fexp hxne]
  unfold cexp
  set ex := mag beta x with hex_def
  have h_low : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta hxne
  have h_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have h_emin_lt : emin < ex := lt_bpow beta (lt_of_le_of_lt Hx h_high)
  have h_p_le : p ≤ ex - fexp ex := Hmin ex h_emin_lt
  have h_fexp_le : fexp ex ≤ -p + 1 + (ex - 1) := by linarith
  have h_fexp_lt_ex : fexp ex ≤ ex - 1 := by linarith
  have h_round_low : bpow beta (ex - 1) ≤ |round beta fexp rnd x| :=
    bpow_le_abs_round beta fexp hValid rnd h_fexp_lt_ex h_low
  calc bpow beta (fexp ex)
      ≤ bpow beta (-p + 1 + (ex - 1)) := bpow_le beta h_fexp_le
    _ = bpow beta (-p + 1) * bpow beta (ex - 1) := bpow_plus beta _ _
    _ ≤ bpow beta (-p + 1) * |round beta fexp rnd x| :=
        mul_le_mul_of_nonneg_left h_round_low (bpow_ge_0 _ _)

/-- The `_round` variant for `F2R`-shaped inputs. -/
theorem relative_error_round_F2R_emin (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] (Hp : 0 < p)
    (m : ℤ) (Hx : F2R (beta := beta) ⟨m, emin⟩ ≠ 0) :
    |round beta fexp rnd (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      < bpow beta (-p + 1)
          * |round beta fexp rnd (F2R (beta := beta) ⟨m, emin⟩)| := by
  apply relative_error_round beta fexp hValid emin p Hmin rnd Hp
  rw [← F2R_Zabs]
  apply bpow_le_F2R
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [abs_of_neg hm]; omega
  · exfalso; apply Hx; rw [hm]; exact F2R_0 emin
  · rw [abs_of_pos hm]; exact hm

/-! ### Round-to-nearest relative-error bounds -/

/-- For round-to-nearest, the error is at most `(1/2) * β^(-p+1) * |x|`. -/
theorem relative_error_N (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (choice : ℤ → Bool)
    {x : ℝ} (Hx : bpow beta emin ≤ |x|) :
    |round beta fexp (Znearest choice) x - x| ≤ (1/2) * bpow beta (-p + 1) * |x| := by
  refine le_trans (error_le_half_ulp beta fexp hValid choice x) ?_
  have hxne : x ≠ 0 := by
    intro hxz
    rw [hxz, abs_zero] at Hx
    exact absurd Hx (not_le_of_gt (bpow_gt_0 _ _))
  rw [ulp_neq_0 beta fexp hxne]
  unfold cexp
  set ex := mag beta x with hex_def
  have h_low : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta hxne
  have h_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have h_emin_lt : emin < ex := lt_bpow beta (lt_of_le_of_lt Hx h_high)
  have h_fexp_le : fexp ex ≤ -p + 1 + (ex - 1) := by
    have := Hmin ex h_emin_lt; linarith
  have h_half_nn : (0 : ℝ) ≤ 1/2 := by norm_num
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h_half_nn
  calc bpow beta (fexp ex)
      ≤ bpow beta (-p + 1 + (ex - 1)) := bpow_le beta h_fexp_le
    _ = bpow beta (-p + 1) * bpow beta (ex - 1) := bpow_plus beta _ _
    _ ≤ bpow beta (-p + 1) * |x| :=
        mul_le_mul_of_nonneg_left h_low (bpow_ge_0 _ _)

/-- The `1 + ε` form for round-to-nearest. -/
theorem relative_error_N_ex (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (choice : ℤ → Bool)
    {x : ℝ} (Hx : bpow beta emin ≤ |x|) :
    ∃ eps : ℝ, |eps| ≤ (1/2) * bpow beta (-p + 1) ∧
      round beta fexp (Znearest choice) x = x * (1 + eps) :=
  relative_error_le_conversion beta fexp (Znearest choice)
    (le_of_lt (mul_pos (by norm_num) (bpow_gt_0 _ _)))
    (relative_error_N beta fexp hValid emin p Hmin choice Hx)

/-- For round-to-nearest at an `F2R`-shaped input. -/
theorem relative_error_N_F2R_emin (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (choice : ℤ → Bool) (m : ℤ) :
    |round beta fexp (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      ≤ (1/2) * bpow beta (-p + 1) * |F2R (beta := beta) ⟨m, emin⟩| := by
  by_cases Hx : F2R (beta := beta) ⟨m, emin⟩ = 0
  · rw [Hx, round_0, sub_zero, abs_zero, mul_zero]
  · apply relative_error_N beta fexp hValid emin p Hmin choice
    rw [← F2R_Zabs]
    apply bpow_le_F2R
    rcases lt_trichotomy m 0 with hm | hm | hm
    · rw [abs_of_neg hm]; omega
    · exfalso; apply Hx; rw [hm]; exact F2R_0 emin
    · rw [abs_of_pos hm]; exact hm

/-- The `_ex` form for round-to-nearest at an `F2R`-shaped input. -/
theorem relative_error_N_F2R_emin_ex (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (choice : ℤ → Bool) (m : ℤ) :
    ∃ eps : ℝ, |eps| ≤ (1/2) * bpow beta (-p + 1) ∧
      round beta fexp (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)
        = F2R (beta := beta) ⟨m, emin⟩ * (1 + eps) :=
  relative_error_le_conversion beta fexp (Znearest choice)
    (le_of_lt (mul_pos (by norm_num) (bpow_gt_0 _ _)))
    (relative_error_N_F2R_emin beta fexp hValid emin p Hmin choice m)

/-- The bound on the rounded value for round-to-nearest. -/
theorem relative_error_N_round (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (choice : ℤ → Bool) (Hp : 0 < p)
    {x : ℝ} (Hx : bpow beta emin ≤ |x|) :
    |round beta fexp (Znearest choice) x - x|
      ≤ (1/2) * bpow beta (-p + 1) * |round beta fexp (Znearest choice) x| := by
  refine le_trans (error_le_half_ulp beta fexp hValid choice x) ?_
  have hxne : x ≠ 0 := by
    intro hxz
    rw [hxz, abs_zero] at Hx
    exact absurd Hx (not_le_of_gt (bpow_gt_0 _ _))
  rw [ulp_neq_0 beta fexp hxne]
  unfold cexp
  set ex := mag beta x with hex_def
  have h_low : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta hxne
  have h_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have h_emin_lt : emin < ex := lt_bpow beta (lt_of_le_of_lt Hx h_high)
  have h_p_le : p ≤ ex - fexp ex := Hmin ex h_emin_lt
  have h_fexp_le : fexp ex ≤ -p + 1 + (ex - 1) := by linarith
  have h_fexp_lt_ex : fexp ex ≤ ex - 1 := by linarith
  have h_round_low : bpow beta (ex - 1) ≤ |round beta fexp (Znearest choice) x| :=
    bpow_le_abs_round beta fexp hValid (Znearest choice) h_fexp_lt_ex h_low
  have h_half_nn : (0 : ℝ) ≤ 1/2 := by norm_num
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ h_half_nn
  calc bpow beta (fexp ex)
      ≤ bpow beta (-p + 1 + (ex - 1)) := bpow_le beta h_fexp_le
    _ = bpow beta (-p + 1) * bpow beta (ex - 1) := bpow_plus beta _ _
    _ ≤ bpow beta (-p + 1) * |round beta fexp (Znearest choice) x| :=
        mul_le_mul_of_nonneg_left h_round_low (bpow_ge_0 _ _)

/-- The `_round` variant for round-to-nearest at an `F2R`-shaped input. -/
theorem relative_error_N_round_F2R_emin (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    (emin p : ℤ) (Hmin : ∀ k : ℤ, emin < k → p ≤ k - fexp k)
    (choice : ℤ → Bool) (Hp : 0 < p) (m : ℤ) :
    |round beta fexp (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      ≤ (1/2) * bpow beta (-p + 1)
          * |round beta fexp (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)| := by
  by_cases Hx : F2R (beta := beta) ⟨m, emin⟩ = 0
  · rw [Hx, round_0, sub_zero, abs_zero, mul_zero]
  · apply relative_error_N_round beta fexp hValid emin p Hmin choice Hp
    rw [← F2R_Zabs]
    apply bpow_le_F2R
    rcases lt_trichotomy m 0 with hm | hm | hm
    · rw [abs_of_neg hm]; omega
    · exfalso; apply Hx; rw [hm]; exact F2R_0 emin
    · rw [abs_of_pos hm]; exact hm

/-! ### FLX-specific relative-error bounds -/

/-- Trivial inequality on FLX: `prec ≤ k - FLX_exp prec k`. -/
theorem relative_error_FLX_aux (prec : ℤ) (k : ℤ) : prec ≤ k - FLX_exp prec k := by
  unfold FLX_exp; omega

/-- FLX has a relative error of `β^(-prec+1)` for any nonzero `x`. -/
theorem relative_error_FLX (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} (Hx : x ≠ 0) :
    |round beta (FLX_exp prec) rnd x - x| < bpow beta (-prec + 1) * |x| := by
  apply relative_error beta (FLX_exp prec) (FLX_exp_valid prec Hp)
    (mag beta x - 1) prec (fun k _ => relative_error_FLX_aux prec k) rnd
  exact bpow_mag_le beta Hx

/-- The `1 + ε` form for FLX. -/
theorem relative_error_FLX_ex (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] (x : ℝ) :
    ∃ eps : ℝ, |eps| < bpow beta (-prec + 1) ∧
      round beta (FLX_exp prec) rnd x = x * (1 + eps) :=
  relative_error_lt_conversion beta (FLX_exp prec) rnd (bpow_gt_0 _ _)
    (fun hne => relative_error_FLX beta prec Hp rnd hne)

/-- The relative error w.r.t. the rounded value, in FLX. -/
theorem relative_error_FLX_round (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} (Hx : x ≠ 0) :
    |round beta (FLX_exp prec) rnd x - x|
      < bpow beta (-prec + 1) * |round beta (FLX_exp prec) rnd x| := by
  apply relative_error_round beta (FLX_exp prec) (FLX_exp_valid prec Hp)
    (mag beta x - 1) prec (fun k _ => relative_error_FLX_aux prec k) rnd Hp
  exact bpow_mag_le beta Hx

/-- Round-to-nearest relative error in FLX. -/
theorem relative_error_N_FLX (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    |round beta (FLX_exp prec) (Znearest choice) x - x|
      ≤ (1/2) * bpow beta (-prec + 1) * |x| := by
  by_cases Hx : x = 0
  · simp [Hx, round_0]
  · apply relative_error_N beta (FLX_exp prec) (FLX_exp_valid prec Hp)
      (mag beta x - 1) prec (fun k _ => relative_error_FLX_aux prec k) choice
    exact bpow_mag_le beta Hx

/-- The unit roundoff for FLX. -/
noncomputable def u_ro (beta : radix) (prec : ℤ) : ℝ :=
  (1/2) * bpow beta (-prec + 1)

theorem u_ro_pos (beta : radix) (prec : ℤ) : 0 ≤ u_ro beta prec := by
  unfold u_ro
  exact mul_nonneg (by norm_num) (bpow_ge_0 _ _)

theorem u_ro_lt_1 (beta : radix) (prec : ℤ) (Hp : 0 < prec) : u_ro beta prec < 1 := by
  unfold u_ro
  have h_bound : bpow beta (-prec + 1) ≤ bpow beta 0 := bpow_le beta (by omega)
  have h_bpow0 : bpow beta 0 = 1 := by unfold bpow; simp
  rw [h_bpow0] at h_bound
  linarith

theorem u_rod1pu_ro_pos (beta : radix) (prec : ℤ) :
    0 ≤ u_ro beta prec / (1 + u_ro beta prec) := by
  have hu := u_ro_pos beta prec
  have h_one_plus : 0 < 1 + u_ro beta prec := by linarith
  exact div_nonneg hu (le_of_lt h_one_plus)

theorem u_rod1pu_ro_le_u_ro (beta : radix) (prec : ℤ) :
    u_ro beta prec / (1 + u_ro beta prec) ≤ u_ro beta prec := by
  have hu := u_ro_pos beta prec
  have h_one_plus : 0 < 1 + u_ro beta prec := by linarith
  rw [div_le_iff₀ h_one_plus]
  have : u_ro beta prec * u_ro beta prec ≥ 0 := mul_nonneg hu hu
  nlinarith

/-- The `1 + ε` form for round-to-nearest in FLX. -/
theorem relative_error_N_FLX_ex (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    ∃ eps : ℝ, |eps| ≤ (1/2) * bpow beta (-prec + 1) ∧
      round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) :=
  relative_error_le_conversion beta (FLX_exp prec) (Znearest choice)
    (le_of_lt (mul_pos (by norm_num) (bpow_gt_0 _ _)))
    (relative_error_N_FLX beta prec Hp choice x)

/-- The relative error w.r.t. the rounded value, for round-to-nearest in FLX. -/
theorem relative_error_N_FLX_round (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    |round beta (FLX_exp prec) (Znearest choice) x - x|
      ≤ (1/2) * bpow beta (-prec + 1)
          * |round beta (FLX_exp prec) (Znearest choice) x| := by
  by_cases Hx : x = 0
  · simp [Hx, round_0]
  · apply relative_error_N_round beta (FLX_exp prec) (FLX_exp_valid prec Hp)
      (mag beta x - 1) prec (fun k _ => relative_error_FLX_aux prec k) choice Hp
    exact bpow_mag_le beta Hx

end LeanFlocq
