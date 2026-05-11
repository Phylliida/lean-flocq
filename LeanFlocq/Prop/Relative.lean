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

/-- The tighter `u_ro / (1 + u_ro)` bound for round-to-nearest in FLX.

The classic IEEE 754 "unit roundoff" estimate, sharper than the standard
`u_ro * |x|` bound. -/
theorem relative_error_N_FLX' (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    |round beta (FLX_exp prec) (Znearest choice) x - x|
      ≤ u_ro beta prec / (1 + u_ro beta prec) * |x| := by
  have Pu_ro : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  by_cases Zx : x = 0
  · simp [Zx, round_0]
  -- Set up the key quantities.
  set rx := round beta (FLX_exp prec) (Znearest choice) x with hrx_def
  set ufpx := bpow beta (mag beta x - 1) with hufpx_def
  have Pufpx : 0 ≤ ufpx := bpow_ge_0 _ _
  -- Step 1: |rx - x| ≤ u_ro * ufpx.
  -- error_le_half_ulp gives |rx - x| ≤ (1/2) * ulp x.
  -- For x ≠ 0, ulp x = bpow(cexp x) = bpow(mag x - prec).
  -- u_ro * ufpx = (1/2) * bpow(-prec+1) * bpow(mag x - 1) = (1/2) * bpow(mag x - prec). ✓
  have H_2_1 : |rx - x| ≤ u_ro beta prec * ufpx := by
    refine le_trans
      (error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec Hp) choice x) ?_
    rw [ulp_neq_0 beta (FLX_exp prec) Zx, hufpx_def]
    show 1 / 2 * bpow beta (cexp beta (FLX_exp prec) x)
        ≤ u_ro beta prec * bpow beta (mag beta x - 1)
    unfold cexp FLX_exp u_ro
    rw [mul_assoc, ← bpow_plus]
    have h_exp_eq : (-prec + 1 + (mag beta x - 1) : ℤ) = mag beta x - prec := by ring
    rw [h_exp_eq]
  -- Step 2: ufpx + |rx - x| ≤ |x|.
  -- For x ≥ 0: ufpx ∈ F, ufpx ≤ x. round_N_pt gives |rx - x| ≤ |ufpx - x| = x - ufpx.
  -- For x < 0: -ufpx ∈ F, x ≤ -ufpx. round_N_pt gives |rx - x| ≤ |-ufpx - x| = -ufpx - x.
  have H_2_3 : ufpx + |rx - x| ≤ |x| := by
    have h_ufpx_F : generic_format beta (FLX_exp prec) ufpx := by
      rw [hufpx_def]
      apply generic_format_bpow beta (FLX_exp prec)
      unfold FLX_exp; linarith
    rcases le_or_gt 0 x with Sx | Sx
    · -- x ≥ 0.
      have h_ufpx_le_x : ufpx ≤ x := by
        rw [hufpx_def]
        have := bpow_mag_le beta Zx
        rwa [abs_of_nonneg Sx] at this
      have h_round_dist : |rx - x| ≤ |ufpx - x| :=
        (round_N_pt beta (FLX_exp prec) (FLX_exp_valid prec Hp) choice x).2 ufpx h_ufpx_F
      rw [abs_of_nonneg Sx]
      rw [show ufpx - x = -(x - ufpx) from by ring, abs_neg,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - ufpx)] at h_round_dist
      linarith
    · -- x < 0.
      have h_neg_ufpx_F : generic_format beta (FLX_exp prec) (-ufpx) :=
        generic_format_opp beta (FLX_exp prec) h_ufpx_F
      have h_x_le_neg_ufpx : x ≤ -ufpx := by
        rw [hufpx_def]
        have := bpow_mag_le beta Zx
        rw [abs_of_neg Sx] at this
        linarith
      have h_round_dist : |rx - x| ≤ |(-ufpx) - x| :=
        (round_N_pt beta (FLX_exp prec) (FLX_exp_valid prec Hp) choice x).2 (-ufpx) h_neg_ufpx_F
      rw [abs_of_neg Sx]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ -ufpx - x)] at h_round_dist
      linarith
  -- Step 3: combine. |rx - x| * (1 + u_ro) ≤ u_ro * |x|.
  -- |rx - x| + u_ro * |rx - x| ≤ u_ro * ufpx + u_ro * (|x| - ufpx) = u_ro * |x|.
  have h_x_pos : 0 < |x| := abs_pos.mpr Zx
  have h_one_plus_pos : 0 < 1 + u_ro beta prec := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h_one_plus_pos]
  -- Goal: |rx - x| * (1 + u_ro) ≤ u_ro * |x|
  have h_rx_nn : 0 ≤ |rx - x| := abs_nonneg _
  -- |rx - x| + u_ro * |rx - x| ≤ |rx - x| + u_ro * (|x| - ufpx) [from H_2_3: |rx - x| ≤ |x| - ufpx]
  -- = |rx - x| - u_ro * ufpx + u_ro * |x|
  -- ≤ u_ro * ufpx - u_ro * ufpx + u_ro * |x|  [from H_2_1: |rx - x| ≤ u_ro * ufpx]
  -- = u_ro * |x|.
  nlinarith [H_2_1, H_2_3, Pu_ro, Pufpx, h_x_pos, h_rx_nn]

/-- The `1 + ε` form with the tighter `u_ro/(1+u_ro)` bound. -/
theorem relative_error_N_FLX'_ex (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    ∃ eps : ℝ, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec) ∧
      round beta (FLX_exp prec) (Znearest choice) x = x * (1 + eps) :=
  relative_error_le_conversion beta (FLX_exp prec) (Znearest choice)
    (u_rod1pu_ro_pos beta prec)
    (relative_error_N_FLX' beta prec Hp choice x)

/-- Helper: converting between the relative-to-x and relative-to-round forms.
If `rx = x * (1 + d)` with `|d| ≤ u_ro/(1+u_ro)`, then `x = rx * (1 + d')`
with `|d'| ≤ u_ro`. -/
theorem relative_error_N_round_ex_derive (beta : radix) (prec : ℤ)
    (Hp : 0 < prec)
    {x rx : ℝ}
    (h : ∃ eps : ℝ, |eps| ≤ u_ro beta prec / (1 + u_ro beta prec)
                  ∧ rx = x * (1 + eps)) :
    ∃ eps : ℝ, |eps| ≤ u_ro beta prec ∧ x = rx * (1 + eps) := by
  obtain ⟨d, Bd, Hd⟩ := h
  have Pu_ro : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  have h_abs_d := abs_le.mp Bd
  have h_one_plus_pos : 0 < 1 + u_ro beta prec := by linarith
  have h_d1 := u_rod1pu_ro_le_u_ro beta prec
  have h_d2 := u_ro_lt_1 beta prec Hp
  -- |d| ≤ u_ro/(1+u_ro) < 1, so 1 + d > 0.
  have h_d_lt_1 : |d| < 1 := lt_of_le_of_lt (le_trans Bd h_d1) h_d2
  have h_one_plus_d_pos : 0 < 1 + d := by
    have := neg_lt_of_abs_lt h_d_lt_1; linarith
  by_cases Zfx : rx = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [abs_zero]; exact Pu_ro
    · -- From Zfx : rx = 0 and Hd : rx = x * (1 + d) with 1 + d > 0, get x = 0.
      have h_x_eq_0 : x = 0 := by
        rw [Zfx] at Hd
        rcases mul_eq_zero.mp Hd.symm with hx | hd1
        · exact hx
        · exfalso; linarith
      rw [Zfx, h_x_eq_0]; ring
  by_cases Zx : x = 0
  · exfalso; apply Zfx; rw [Hd, Zx, zero_mul]
  -- General case: d' := (x - rx) / rx.
  refine ⟨(x - rx) / rx, ?_, ?_⟩
  · -- |d'| = |x - rx| / |rx| ≤ u_ro.
    have h_x_sub_rx_eq : x - rx = -(x * d) := by rw [Hd]; ring
    have h_abs_diff : |x - rx| = |x| * |d| := by
      rw [h_x_sub_rx_eq, abs_neg, abs_mul]
    have h_abs_rx : |rx| = |x| * (1 + d) := by
      rw [Hd, abs_mul, abs_of_pos h_one_plus_d_pos]
    rw [abs_div, h_abs_diff, h_abs_rx]
    have h_x_pos : 0 < |x| := abs_pos.mpr Zx
    have h_denom_pos : 0 < |x| * (1 + d) := mul_pos h_x_pos h_one_plus_d_pos
    rw [div_le_iff₀ h_denom_pos]
    -- Goal: |x| * |d| ≤ u_ro * (|x| * (1 + d))
    -- Sufficient: |d| ≤ u_ro * (1 + d).
    have h_Bd_cleared : |d| * (1 + u_ro beta prec) ≤ u_ro beta prec := by
      rw [← le_div_iff₀ h_one_plus_pos]; exact Bd
    have h_key : |d| ≤ u_ro beta prec * (1 + d) := by
      rcases le_or_lt 0 d with hd_nn | hd_neg
      · -- d ≥ 0: |d| = d. u_ro * (1 + d) ≥ u_ro * 1 = u_ro ≥ |d| (since u_ro ≥ u_ro/(1+u_ro) ≥ |d|).
        rw [abs_of_nonneg hd_nn]
        have h_uro_dist : u_ro beta prec * (1 + d) = u_ro beta prec + u_ro beta prec * d := by ring
        rw [h_uro_dist]
        nlinarith [h_Bd_cleared, hd_nn, Pu_ro, abs_of_nonneg hd_nn]
      · -- d < 0: |d| = -d. u_ro * (1 + d) = u_ro - u_ro * (-d) = u_ro - u_ro * |d|.
        rw [abs_of_neg hd_neg]
        have h_uro_dist : u_ro beta prec * (1 + d) = u_ro beta prec + u_ro beta prec * d := by ring
        rw [h_uro_dist]
        have h_abs_neg : |d| = -d := abs_of_neg hd_neg
        nlinarith [h_Bd_cleared, abs_nonneg d, h_abs_neg, Pu_ro]
    nlinarith [h_key, h_x_pos, abs_nonneg d, h_one_plus_d_pos, Pu_ro]
  · -- x = rx * (1 + (x - rx) / rx). Algebra (using rx ≠ 0).
    field_simp
    rw [Hd]; ring

/-- The tighter `1 + ε` form w.r.t. the rounded value. -/
theorem relative_error_N_FLX_round_ex (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    ∃ eps : ℝ, |eps| ≤ u_ro beta prec ∧
      x = round beta (FLX_exp prec) (Znearest choice) x * (1 + eps) :=
  relative_error_N_round_ex_derive beta prec Hp
    (relative_error_N_FLX'_ex beta prec Hp choice x)

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

/-! ### FLT-specific relative-error bounds -/

/-- For `k > emin + prec - 1`, FLT keeps at least `prec` significant digits. -/
theorem relative_error_FLT_aux (emin prec : ℤ) {k : ℤ} (Hk : emin + prec - 1 < k) :
    prec ≤ k - FLT_exp emin prec k := by
  unfold FLT_exp
  rcases le_total (k - prec) emin with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- FLT relative error above the threshold. -/
theorem relative_error_FLT (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} (Hx : bpow beta (emin + prec - 1) ≤ |x|) :
    |round beta (FLT_exp emin prec) rnd x - x| < bpow beta (-prec + 1) * |x| := by
  apply relative_error beta (FLT_exp emin prec) (FLT_exp_valid emin prec Hp)
    (emin + prec - 1) prec (fun _ Hk => relative_error_FLT_aux emin prec Hk) rnd Hx

/-- FLT relative error at `F2R ⟨m, emin⟩`: rounding is exact in the subnormal
range, and above the threshold the standard bound applies. -/
theorem relative_error_FLT_F2R_emin (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (m : ℤ) (Hx : F2R (beta := beta) ⟨m, emin⟩ ≠ 0) :
    |round beta (FLT_exp emin prec) rnd (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      < bpow beta (-prec + 1) * |F2R (beta := beta) ⟨m, emin⟩| := by
  set x := F2R (beta := beta) ⟨m, emin⟩ with hx_def
  by_cases Hx_lt : |x| < bpow beta (emin + prec - 1)
  · -- Subnormal regime: x is exact in FLT.
    have h_FIX : generic_format beta (FIX_exp emin) x := by
      apply generic_format_FIX beta emin
      exact ⟨⟨m, emin⟩, rfl, rfl⟩
    have h_le : |x| ≤ bpow beta (emin + prec) := by
      apply le_of_lt; apply lt_of_lt_of_le Hx_lt
      exact bpow_le beta (by omega)
    have h_FLT : generic_format beta (FLT_exp emin prec) x :=
      generic_format_FLT_FIX beta emin prec Hp h_le h_FIX
    rw [round_generic beta (FLT_exp emin prec) rnd h_FLT, sub_self, abs_zero]
    exact mul_pos (bpow_gt_0 _ _) (abs_pos.mpr Hx)
  · push_neg at Hx_lt
    exact relative_error_FLT beta emin prec Hp rnd Hx_lt

/-- The `1 + ε` form for FLT at `F2R ⟨m, emin⟩`. -/
theorem relative_error_FLT_F2R_emin_ex (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] (m : ℤ) :
    ∃ eps : ℝ, |eps| < bpow beta (-prec + 1) ∧
      round beta (FLT_exp emin prec) rnd (F2R (beta := beta) ⟨m, emin⟩)
        = F2R (beta := beta) ⟨m, emin⟩ * (1 + eps) :=
  relative_error_lt_conversion beta (FLT_exp emin prec) rnd (bpow_gt_0 _ _)
    (fun hne => relative_error_FLT_F2R_emin beta emin prec Hp rnd m hne)

/-- The `1 + ε` form for FLT above the threshold. -/
theorem relative_error_FLT_ex (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x : ℝ} (Hx : bpow beta (emin + prec - 1) ≤ |x|) :
    ∃ eps : ℝ, |eps| < bpow beta (-prec + 1) ∧
      round beta (FLT_exp emin prec) rnd x = x * (1 + eps) :=
  relative_error_lt_conversion beta (FLT_exp emin prec) rnd (bpow_gt_0 _ _)
    (fun _ => relative_error_FLT beta emin prec Hp rnd Hx)

/-- Round-to-nearest relative error in FLT, above the threshold. -/
theorem relative_error_N_FLT (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {x : ℝ} (Hx : bpow beta (emin + prec - 1) ≤ |x|) :
    |round beta (FLT_exp emin prec) (Znearest choice) x - x|
      ≤ (1/2) * bpow beta (-prec + 1) * |x| := by
  apply relative_error_N beta (FLT_exp emin prec) (FLT_exp_valid emin prec Hp)
    (emin + prec - 1) prec (fun _ Hk => relative_error_FLT_aux emin prec Hk) choice Hx

/-- The `1 + ε` form for round-to-nearest in FLT, above the threshold. -/
theorem relative_error_N_FLT_ex (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {x : ℝ} (Hx : bpow beta (emin + prec - 1) ≤ |x|) :
    ∃ eps : ℝ, |eps| ≤ (1/2) * bpow beta (-prec + 1) ∧
      round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) :=
  relative_error_le_conversion beta (FLT_exp emin prec) (Znearest choice)
    (le_of_lt (mul_pos (by norm_num) (bpow_gt_0 _ _)))
    (relative_error_N_FLT beta emin prec Hp choice Hx)

/-- The relative error w.r.t. the rounded value, for round-to-nearest in FLT. -/
theorem relative_error_N_FLT_round (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {x : ℝ} (Hx : bpow beta (emin + prec - 1) ≤ |x|) :
    |round beta (FLT_exp emin prec) (Znearest choice) x - x|
      ≤ (1/2) * bpow beta (-prec + 1)
          * |round beta (FLT_exp emin prec) (Znearest choice) x| := by
  apply relative_error_N_round beta (FLT_exp emin prec) (FLT_exp_valid emin prec Hp)
    (emin + prec - 1) prec (fun _ Hk => relative_error_FLT_aux emin prec Hk)
    choice Hp Hx

/-- Round-to-nearest at `F2R ⟨m, emin⟩` for FLT. -/
theorem relative_error_N_FLT_F2R_emin (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (m : ℤ) :
    |round beta (FLT_exp emin prec) (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      ≤ (1/2) * bpow beta (-prec + 1) * |F2R (beta := beta) ⟨m, emin⟩| := by
  set x := F2R (beta := beta) ⟨m, emin⟩ with hx_def
  by_cases Hx_lt : |x| < bpow beta (emin + prec - 1)
  · have h_FIX : generic_format beta (FIX_exp emin) x := by
      apply generic_format_FIX beta emin
      exact ⟨⟨m, emin⟩, rfl, rfl⟩
    have h_le : |x| ≤ bpow beta (emin + prec) :=
      le_of_lt (lt_of_lt_of_le Hx_lt (bpow_le beta (by omega)))
    have h_FLT : generic_format beta (FLT_exp emin prec) x :=
      generic_format_FLT_FIX beta emin prec Hp h_le h_FIX
    rw [round_generic beta (FLT_exp emin prec) (Znearest choice) h_FLT,
        sub_self, abs_zero]
    refine mul_nonneg (mul_nonneg (by norm_num) (bpow_ge_0 _ _)) (abs_nonneg _)
  · push_neg at Hx_lt
    exact relative_error_N_FLT beta emin prec Hp choice Hx_lt

/-- The `1 + ε` form at `F2R ⟨m, emin⟩` for round-to-nearest in FLT. -/
theorem relative_error_N_FLT_F2R_emin_ex (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (m : ℤ) :
    ∃ eps : ℝ, |eps| ≤ (1/2) * bpow beta (-prec + 1) ∧
      round beta (FLT_exp emin prec) (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)
        = F2R (beta := beta) ⟨m, emin⟩ * (1 + eps) :=
  relative_error_le_conversion beta (FLT_exp emin prec) (Znearest choice)
    (le_of_lt (mul_pos (by norm_num) (bpow_gt_0 _ _)))
    (relative_error_N_FLT_F2R_emin beta emin prec Hp choice m)

/-- The `_round` variant at `F2R ⟨m, emin⟩` for round-to-nearest in FLT. -/
theorem relative_error_N_FLT_round_F2R_emin (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (m : ℤ) :
    |round beta (FLT_exp emin prec) (Znearest choice) (F2R (beta := beta) ⟨m, emin⟩)
        - F2R (beta := beta) ⟨m, emin⟩|
      ≤ (1/2) * bpow beta (-prec + 1)
          * |round beta (FLT_exp emin prec) (Znearest choice)
              (F2R (beta := beta) ⟨m, emin⟩)| := by
  set x := F2R (beta := beta) ⟨m, emin⟩ with hx_def
  by_cases Hx_lt : |x| < bpow beta (emin + prec - 1)
  · have h_FIX : generic_format beta (FIX_exp emin) x := by
      apply generic_format_FIX beta emin
      exact ⟨⟨m, emin⟩, rfl, rfl⟩
    have h_le : |x| ≤ bpow beta (emin + prec) :=
      le_of_lt (lt_of_lt_of_le Hx_lt (bpow_le beta (by omega)))
    have h_FLT : generic_format beta (FLT_exp emin prec) x :=
      generic_format_FLT_FIX beta emin prec Hp h_le h_FIX
    rw [round_generic beta (FLT_exp emin prec) (Znearest choice) h_FLT,
        sub_self, abs_zero]
    refine mul_nonneg (mul_nonneg (by norm_num) (bpow_ge_0 _ _)) (abs_nonneg _)
  · push_neg at Hx_lt
    exact relative_error_N_FLT_round beta emin prec Hp choice Hx_lt

/-! ### Combined relative + absolute error decomposition for FLT -/

/-- For positive `x`, the FLT round-to-nearest error decomposes into a
relative `eps` part above the threshold and an absolute `eta` part below;
exactly one is nonzero. -/
theorem error_N_FLT_aux (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) {x : ℝ} (Hx : 0 < x) :
    ∃ eps eta : ℝ,
      |eps| ≤ (1/2) * bpow beta (-prec + 1) ∧
      |eta| ≤ (1/2) * bpow beta emin ∧
      eps * eta = 0 ∧
      round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  by_cases h : bpow beta (emin + prec) ≤ x
  · -- Above threshold: use the generic relative_error_N_ex with emin' = emin + prec.
    have habs : bpow beta (emin + prec) ≤ |x| := by rw [abs_of_pos Hx]; exact h
    have Hmin' : ∀ k : ℤ, emin + prec < k → prec ≤ k - FLT_exp emin prec k := by
      intro k Hk
      unfold FLT_exp
      have hk' : emin ≤ k - prec := by omega
      rw [max_eq_left hk']; omega
    obtain ⟨eps, Heps_bound, Heps⟩ :=
      relative_error_N_ex beta (FLT_exp emin prec) (FLT_exp_valid emin prec Hp)
        (emin + prec) prec Hmin' choice habs
    refine ⟨eps, 0, Heps_bound, ?_, ?_, ?_⟩
    · rw [abs_zero]
      exact mul_nonneg (by norm_num) (bpow_ge_0 _ _)
    · ring
    · rw [Heps, add_zero]
  · -- Below threshold: eps = 0, eta = round x - x, bounded by half ulp = bpow emin / 2.
    push_neg at h
    set rx := round beta (FLT_exp emin prec) (Znearest choice) x with hrx_def
    have h_abs : |x| < bpow beta (emin + prec) := by rw [abs_of_pos Hx]; exact h
    have h_err : |rx - x| ≤ (1/2) * bpow beta emin := by
      have h_half_ulp := error_le_half_ulp beta (FLT_exp emin prec)
        (FLT_exp_valid emin prec Hp) choice x
      rw [ulp_FLT_small beta emin prec Hp h_abs] at h_half_ulp
      exact h_half_ulp
    refine ⟨0, rx - x, ?_, h_err, ?_, ?_⟩
    · rw [abs_zero]
      exact mul_nonneg (by norm_num) (bpow_ge_0 _ _)
    · ring
    · ring

/-- The full theorem: for any real `x`, FLT round-to-nearest error decomposes
into a relative part `eps` and an absolute part `eta`, exactly one nonzero. -/
theorem error_N_FLT (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    ∃ eps eta : ℝ,
      |eps| ≤ (1/2) * bpow beta (-prec + 1) ∧
      |eta| ≤ (1/2) * bpow beta emin ∧
      eps * eta = 0 ∧
      round beta (FLT_exp emin prec) (Znearest choice) x = x * (1 + eps) + eta := by
  rcases lt_trichotomy x 0 with Hx | Hx | Hx
  · -- x < 0: apply error_N_FLT_aux to (-x).
    have hpx : 0 < -x := by linarith
    obtain ⟨d, e, Hd, He, Hde, Hr⟩ :=
      error_N_FLT_aux beta emin prec Hp (fun t => !choice (-(t + 1))) hpx
    refine ⟨d, -e, Hd, ?_, ?_, ?_⟩
    · rwa [abs_neg]
    · have : d * -e = -(d * e) := by ring
      rw [this, Hde, neg_zero]
    · -- round_N (-(-x)) = -round_N (-x)  (via round_N_opp on x = -(-x)).
      have h1 : round beta (FLT_exp emin prec) (Znearest choice) x
                = -(round beta (FLT_exp emin prec)
                      (Znearest (fun t => !choice (-(t + 1)))) (-x)) := by
        conv_lhs => rw [show x = -(-x) from by ring]
        exact round_N_opp beta (FLT_exp emin prec) choice (-x)
      rw [h1, Hr]
      ring
  · -- x = 0.
    refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
    · rw [abs_zero]; exact mul_nonneg (by norm_num) (bpow_ge_0 _ _)
    · rw [abs_zero]; exact mul_nonneg (by norm_num) (bpow_ge_0 _ _)
    · ring
    · rw [Hx, round_0]; ring
  · exact error_N_FLT_aux beta emin prec Hp choice Hx

end LeanFlocq
