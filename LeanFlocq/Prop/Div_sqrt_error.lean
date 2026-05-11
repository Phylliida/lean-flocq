/-
Lean port of Coq Flocq's `Prop/Div_sqrt_error.v` — error of division
and square root in F.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.

Selected keystone theorems. Variants depending on the unit roundoff
`u_ro` family are deferred. The `format_REM` section is also deferred.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FLX
import LeanFlocq.Core.Ulp
import LeanFlocq.Calc.Operations
import LeanFlocq.Prop.Relative
import LeanFlocq.Prop.Mult_error

namespace LeanFlocq

/-! ### Sums fitting in `prec + Fexp` digits stay in F -/

/-- If `x = F2R fx`, `y = F2R fy`, and `|x + y|` is bounded by both
`β^(prec + Fexp fx)` and `β^(prec + Fexp fy)`, then `x + y` is in any format
satisfying `fexp(e) ≤ e - prec`. -/
theorem generic_format_plus_prec (beta : radix) (fexp : ℤ → ℤ) (prec : ℤ)
    (Hfexp : ∀ e : ℤ, fexp e ≤ e - prec)
    {x y : ℝ} (fx fy : float beta)
    (Hx : x = F2R fx) (Hy : y = F2R fy)
    (H1 : |x + y| < bpow beta (prec + fx.Fexp))
    (H2 : |x + y| < bpow beta (prec + fy.Fexp)) :
    generic_format beta fexp (x + y) := by
  by_cases H : x + y = 0
  · rw [H]; exact generic_format_0 _ _
  -- Express x + y = F2R (Fplus fx fy).
  have h_sum : x + y = F2R (Fplus fx fy) := by
    rw [Hx, Hy, F2R_plus]
  refine generic_format_F2R' beta fexp (Fplus fx fy) h_sum.symm (fun _ => ?_)
  -- Goal: cexp(x + y) ≤ (Fplus fx fy).Fexp.
  have h_Fexp : (Fplus fx fy).Fexp = min fx.Fexp fy.Fexp := Fexp_Fplus fx fy
  rw [h_Fexp]
  -- cexp(x+y) = fexp(mag(x+y)) ≤ mag(x+y) - prec.
  have h_cexp_le : cexp beta fexp (x + y) ≤ mag beta (x + y) - prec := by
    show fexp (mag beta (x + y)) ≤ mag beta (x + y) - prec
    exact Hfexp _
  -- mag(x+y) ≤ prec + min(Fexp fx, Fexp fy).
  have h_mag_le : mag beta (x + y) ≤ prec + min fx.Fexp fy.Fexp := by
    rcases le_total fx.Fexp fy.Fexp with hxy | hxy
    · rw [min_eq_left hxy]
      exact mag_le_bpow beta H H1
    · rw [min_eq_right hxy]
      exact mag_le_bpow beta H H2
  linarith

/-! ### Division error in FLX -/

/-- The remainder of FLX division `x - round(x/y) * y` is in FLX. -/
theorem div_error_FLX (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y) :
    generic_format beta (FLX_exp prec)
      (x - round beta (FLX_exp prec) rnd (x / y) * y) := by
  by_cases Zy : y = 0
  · rw [Zy, mul_zero, sub_zero]; exact Fx
  by_cases Hr : round beta (FLX_exp prec) rnd (x / y) = 0
  · rw [Hr, zero_mul, sub_zero]; exact Fx
  have Zx : x ≠ 0 := by
    intro hx
    apply Hr
    rw [hx, zero_div, round_0]
  obtain ⟨fx, Hx1, Hx2⟩ := canonical_generic_format beta (FLX_exp prec) Fx
  obtain ⟨fy, Hy1, Hy2⟩ := canonical_generic_format beta (FLX_exp prec) Fy
  obtain ⟨fr, Hr1, Hr2⟩ := canonical_generic_format beta (FLX_exp prec)
    (generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec Hp) rnd (x / y))
  -- Apply generic_format_plus_prec with fx and Fopp(Fmult fr fy).
  refine generic_format_plus_prec beta (FLX_exp prec) prec
    (fun _ => le_refl _)
    fx (Fopp (Fmult fr fy)) Hx1 ?_ ?_ ?_
  · -- y' = -(round(x/y) * y) = F2R (Fopp (Fmult fr fy)).
    show -(round beta (FLX_exp prec) rnd (x / y) * y) = F2R (Fopp (Fmult fr fy))
    rw [F2R_opp, F2R_mult, ← Hr1, ← Hy1]
  · -- |x + (-(round*y))| < bpow(prec + Fexp fx).
    -- = |x - round(x/y)*y|. Use relative_error_FLX_ex on (x/y).
    show |x + -(round beta (FLX_exp prec) rnd (x / y) * y)|
       < bpow beta (prec + fx.Fexp)
    obtain ⟨eps, Heps1, Heps2⟩ :=
      relative_error_FLX_ex beta prec Hp rnd (x / y)
    rw [Heps2]
    have h_eq : x + -(x / y * (1 + eps) * y) = -(x * eps) := by
      field_simp; ring
    rw [h_eq, abs_neg, abs_mul]
    -- |x| * |eps| < |x| < bpow(prec + Fexp fx).
    have h_eps_lt_1 : |eps| < 1 := by
      refine lt_of_lt_of_le Heps1 ?_
      have h_pow_le_one : bpow beta (-prec + 1) ≤ bpow beta 0 := bpow_le beta (by omega)
      rw [bpow_zero] at h_pow_le_one
      exact h_pow_le_one
    have h_x_lt : |x| < bpow beta (prec + fx.Fexp) := by
      have h_Fexp : fx.Fexp = cexp beta (FLX_exp prec) x := by
        have := Hx2
        show fx.Fexp = cexp beta (FLX_exp prec) x
        rw [Hx1]; exact this
      rw [h_Fexp]
      unfold cexp FLX_exp
      rw [show prec + (mag beta x - prec) = mag beta x from by ring]
      exact bpow_mag_gt beta x
    have h_x_pos : 0 < |x| := abs_pos.mpr Zx
    have h_eps_nn : 0 ≤ |eps| := abs_nonneg _
    nlinarith
  · -- |x + (-(round*y))| < bpow(prec + Fexp(Fopp(Fmult fr fy))).
    -- Fexp(Fopp(Fmult fr fy)) = Fexp fr + Fexp fy.
    show |x + -(round beta (FLX_exp prec) rnd (x / y) * y)|
       < bpow beta (prec + (Fopp (Fmult fr fy)).Fexp)
    have h_Fexp_eq : (Fopp (Fmult fr fy)).Fexp = fr.Fexp + fy.Fexp := by
      unfold Fopp Fmult; rfl
    rw [h_Fexp_eq]
    -- |x - round*y| = |y * -(round - x/y)| = |y| * |round - x/y|.
    have h_eq : x + -(round beta (FLX_exp prec) rnd (x / y) * y)
              = y * -(round beta (FLX_exp prec) rnd (x / y) - x / y) := by
      field_simp; ring
    rw [h_eq, abs_mul, abs_neg]
    -- |round - x/y| < ulp(round) = bpow(cexp round) = bpow(Fexp fr)
    have h_div_ne : x / y ≠ 0 := div_ne_zero Zx Zy
    have h_err : |round beta (FLX_exp prec) rnd (x / y) - x / y|
               < ulp beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x / y)) :=
      error_lt_ulp_round beta (FLX_exp prec) (FLX_exp_valid prec Hp)
        (monotone_exp_not_FTZ (FLX_exp_valid prec Hp) (FLX_exp_monotone prec))
        (FLX_exp_monotone prec) rnd h_div_ne
    have h_ulp_eq : ulp beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x / y))
                  = bpow beta fr.Fexp := by
      rw [ulp_neq_0 beta (FLX_exp prec) Hr]
      have : fr.Fexp = cexp beta (FLX_exp prec) (F2R fr) := Hr2
      rw [this, ← Hr1]
    rw [h_ulp_eq] at h_err
    -- |y| * |round - x/y| < |y| * bpow(Fexp fr) ≤ bpow(prec + Fexp fr + Fexp fy).
    have h_y_pos : 0 < |y| := abs_pos.mpr Zy
    have h_y_lt : |y| < bpow beta (prec + fy.Fexp) := by
      have h_Fexp_y : fy.Fexp = cexp beta (FLX_exp prec) y := by
        have := Hy2
        show fy.Fexp = cexp beta (FLX_exp prec) y
        rw [Hy1]; exact this
      rw [h_Fexp_y]
      unfold cexp FLX_exp
      rw [show prec + (mag beta y - prec) = mag beta y from by ring]
      exact bpow_mag_gt beta y
    have h_err_nn : 0 ≤ |round beta (FLX_exp prec) rnd (x / y) - x / y| := abs_nonneg _
    have h_pow_nn : 0 ≤ bpow beta fr.Fexp := bpow_ge_0 _ _
    rw [show prec + (fr.Fexp + fy.Fexp) = (prec + fy.Fexp) + fr.Fexp from by ring,
        bpow_plus]
    nlinarith [h_err, h_y_lt, h_y_pos, h_pow_nn, h_err_nn]

/-! ### Square root error in FLX (round-to-nearest) -/

/-- Helper: under round-to-nearest in FLX with `prec ≥ 2`,
`(1 + eps)^2 ≤ 2` where `|eps| ≤ (1/2) * β^(-prec+1)`. -/
private theorem one_plus_eps_sq_le_two (beta : radix) (prec : ℤ) (Hp1 : 1 < prec)
    {eps : ℝ} (Heps : |eps| ≤ (1/2) * bpow beta (-prec + 1)) :
    (1 + eps)^2 ≤ 2 := by
  have h_pow_le : bpow beta (-prec + 1) ≤ bpow beta (-1) :=
    bpow_le beta (by omega)
  have h_bpow_neg_1 : bpow beta (-1) ≤ 1/2 := by
    have h_bpow_neg_1_eq : bpow beta (-1) = 1 / (beta.val : ℝ) := by
      unfold bpow; simp
    rw [h_bpow_neg_1_eq]
    have h_beta_real : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
    have h_beta_pos : 0 < (beta.val : ℝ) := radix_pos beta
    rw [div_le_iff₀ h_beta_pos]
    linarith
  have h_eps_bd : |eps| ≤ 1/4 := by
    refine le_trans Heps ?_
    have h_step : (1/2) * bpow beta (-prec + 1) ≤ (1/2) * (1/2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/2)
      exact le_trans h_pow_le h_bpow_neg_1
    linarith
  have h_eps_lb : -(1/4 : ℝ) ≤ eps := neg_le_of_abs_le h_eps_bd
  have h_eps_ub : eps ≤ 1/4 := le_of_abs_le h_eps_bd
  nlinarith

/-- The FLX square root remainder `x - round(sqrt x)^2` is in FLX, given
`prec > 1` and round-to-nearest. -/
theorem sqrt_error_FLX_N (beta : radix) (prec : ℤ) (Hp1 : 1 < prec)
    (choice : ℤ → Bool) {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x) :
    generic_format beta (FLX_exp prec)
      (x - (round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))^2) := by
  have Hp : 0 < prec := by linarith
  rcases lt_trichotomy x 0 with Hxz | Hxz | Hxz
  · have h_sqrt_zero : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt Hxz)
    rw [h_sqrt_zero, round_0, pow_two, mul_zero, sub_zero]; exact Fx
  · rw [Hxz, Real.sqrt_zero, round_0, pow_two, mul_zero, sub_zero]
    exact generic_format_0 _ _
  · by_cases Hr : round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) = 0
    · rw [Hr, pow_two, mul_zero, sub_zero]; exact Fx
    obtain ⟨fx, Hx1, Hx2⟩ := canonical_generic_format beta (FLX_exp prec) Fx
    obtain ⟨fr, Hr1, Hr2⟩ := canonical_generic_format beta (FLX_exp prec)
      (generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec Hp)
        (Znearest choice) (Real.sqrt x))
    have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr Hxz
    refine generic_format_plus_prec beta (FLX_exp prec) prec
      (fun _ => le_refl _) fx (Fopp (Fmult fr fr)) Hx1 ?_ ?_ ?_
    · show -(round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))^2
          = F2R (Fopp (Fmult fr fr))
      rw [F2R_opp, F2R_mult, ← Hr1]; ring
    · show |x + -(round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))^2|
        < bpow beta (prec + fx.Fexp)
      obtain ⟨eps, Heps1, Heps2⟩ :=
        relative_error_N_FLX_ex beta prec Hp choice (Real.sqrt x)
      rw [Heps2]
      have h_sq : (Real.sqrt x * (1 + eps))^2 = x * (1 + eps)^2 := by
        rw [mul_pow]
        rw [show (Real.sqrt x)^2 = x from Real.sq_sqrt (le_of_lt Hxz)]
      rw [h_sq]
      have h_diff : x + -(x * (1 + eps)^2) = x * (1 - (1 + eps)^2) := by ring
      rw [h_diff, abs_mul, abs_of_pos Hxz]
      have h_eps_sq_le : (1 + eps)^2 ≤ 2 :=
        one_plus_eps_sq_le_two beta prec Hp1 Heps1
      have h_eps_sq_nn : 0 ≤ (1 + eps)^2 := sq_nonneg _
      have h_abs_le : |1 - (1 + eps)^2| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have h_x_lt : x < bpow beta (prec + fx.Fexp) := by
        have h_Fexp : fx.Fexp = cexp beta (FLX_exp prec) x := by
          have := Hx2
          show fx.Fexp = cexp beta (FLX_exp prec) x
          rw [Hx1]; exact this
        rw [h_Fexp]
        unfold cexp FLX_exp
        rw [show prec + (mag beta x - prec) = mag beta x from by ring]
        have := bpow_mag_gt beta x
        rw [abs_of_pos Hxz] at this
        exact this
      nlinarith
    · show |x + -(round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))^2|
        < bpow beta (prec + (Fopp (Fmult fr fr)).Fexp)
      have h_Fexp_eq : (Fopp (Fmult fr fr)).Fexp = fr.Fexp + fr.Fexp := by
        unfold Fopp Fmult; rfl
      rw [h_Fexp_eq]
      have h_factor : x + -(round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))^2
          = -((round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x)
              * (round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) + Real.sqrt x)) := by
        have h_x_sq : x = (Real.sqrt x)^2 := (Real.sq_sqrt (le_of_lt Hxz)).symm
        nth_rewrite 1 [h_x_sq]
        ring
      rw [h_factor, abs_neg, abs_mul]
      have h_err : |round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
          ≤ (1/2) * bpow beta fr.Fexp := by
        have h_half := error_le_half_ulp_round beta (FLX_exp prec)
          (FLX_exp_valid prec Hp)
          (monotone_exp_not_FTZ (FLX_exp_valid prec Hp) (FLX_exp_monotone prec))
          (FLX_exp_monotone prec) choice (Real.sqrt x)
        have h_ulp_eq : ulp beta (FLX_exp prec)
            (round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))
            = bpow beta fr.Fexp := by
          rw [ulp_neq_0 beta (FLX_exp prec) Hr]
          have : fr.Fexp = cexp beta (FLX_exp prec) (F2R fr) := Hr2
          rw [this, ← Hr1]
        rw [h_ulp_eq] at h_half
        exact h_half
      have h_round_lt : |round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)|
          < bpow beta (prec + fr.Fexp) := by
        have h_Fexp_r : fr.Fexp = cexp beta (FLX_exp prec)
            (round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)) := by
          have := Hr2
          show fr.Fexp = cexp beta (FLX_exp prec) _
          rw [Hr1]; exact this
        rw [h_Fexp_r]
        unfold cexp FLX_exp
        rw [show prec + (mag beta _ - prec) = mag beta _ from by ring]
        exact bpow_mag_gt beta _
      have h_round_pos : 0 ≤ round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) := by
        rw [show (0 : ℝ) = round beta (FLX_exp prec) (Znearest choice) 0 from
              (round_0 _ _ _).symm]
        exact round_le beta (FLX_exp prec) (FLX_exp_valid prec Hp) _ (le_of_lt h_sqrt_pos)
      have h_sqrt_lt : Real.sqrt x < bpow beta (prec + fr.Fexp) := by
        by_contra h_not
        push_neg at h_not
        have h_bpow_F : generic_format beta (FLX_exp prec)
            (bpow beta (prec + fr.Fexp)) := by
          apply generic_format_bpow beta (FLX_exp prec)
          unfold FLX_exp; omega
        have h_pow_le_abs : bpow beta (prec + fr.Fexp) ≤ |Real.sqrt x| := by
          rw [abs_of_pos h_sqrt_pos]; exact h_not
        have h_round_abs_ge :=
          abs_round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec Hp)
            (Znearest choice) h_bpow_F h_pow_le_abs
        rw [abs_of_nonneg h_round_pos] at h_round_lt
        rw [abs_of_nonneg h_round_pos] at h_round_abs_ge
        linarith
      have h_sum_lt : |round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)
          + Real.sqrt x| < 2 * bpow beta (prec + fr.Fexp) := by
        rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg h_round_pos] at h_round_lt
        linarith
      have h_pow_id : (1/2) * bpow beta fr.Fexp * (2 * bpow beta (prec + fr.Fexp))
          = bpow beta (prec + (fr.Fexp + fr.Fexp)) := by
        rw [show prec + (fr.Fexp + fr.Fexp) = fr.Fexp + (prec + fr.Fexp) from by ring]
        rw [bpow_plus beta fr.Fexp (prec + fr.Fexp)]
        ring
      have h_lhs_pos : 0 < (1/2) * bpow beta fr.Fexp :=
        mul_pos (by norm_num) (bpow_gt_0 _ _)
      have h_product : |round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
          * |round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) + Real.sqrt x|
          < (1/2) * bpow beta fr.Fexp * (2 * bpow beta (prec + fr.Fexp)) :=
        mul_lt_mul' h_err h_sum_lt (abs_nonneg _) h_lhs_pos
      linarith [h_product, h_pow_id]

/-! ### Square-root unit-roundoff helpers

These positivity and comparison lemmas about
`1 - 1 / sqrt(1 + 2·u_ro)` and `sqrt(1 + 2·u_ro) - 1` are used by
`sqrt_error_N_FLX_ex` and `sqrt_error_N_round_ex_derive`. -/

/-- `1 - 1 / sqrt(1 + 2·u_ro) ≥ 0`. -/
theorem om1ds1p2u_ro_pos (beta : radix) (prec : ℤ) :
    0 ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) := by
  have h_u_ro_nn : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  have h_arg_pos : 0 < 1 + 2 * u_ro beta prec := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (1 + 2 * u_ro beta prec) :=
    Real.sqrt_pos.mpr h_arg_pos
  have h_sqrt_ge_one : 1 ≤ Real.sqrt (1 + 2 * u_ro beta prec) := by
    have h_one_eq : (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    calc (1 : ℝ) = Real.sqrt 1 := h_one_eq
      _ ≤ Real.sqrt (1 + 2 * u_ro beta prec) :=
          Real.sqrt_le_sqrt (by linarith)
  have h_inv_le : 1 / Real.sqrt (1 + 2 * u_ro beta prec) ≤ 1 := by
    rw [div_le_one h_sqrt_pos]; exact h_sqrt_ge_one
  linarith

/-- `sqrt(1 + 2·u_ro) - 1 ≥ 0`. -/
theorem s1p2u_rom1_pos (beta : radix) (prec : ℤ) :
    0 ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 := by
  have h_u_ro_nn : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  have h_sqrt_ge_one : 1 ≤ Real.sqrt (1 + 2 * u_ro beta prec) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + 2 * u_ro beta prec) :=
          Real.sqrt_le_sqrt (by linarith)
  linarith

/-- `1 - 1 / sqrt(1 + 2·u_ro) ≤ u_ro / (1 + u_ro)`. -/
theorem om1ds1p2u_ro_le_u_rod1pu_ro (beta : radix) (prec : ℤ) :
    1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)
      ≤ u_ro beta prec / (1 + u_ro beta prec) := by
  set ε := u_ro beta prec with hε_def
  have h_u_ro_nn : 0 ≤ ε := u_ro_pos beta prec
  have h_arg_pos : 0 < 1 + 2 * ε := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (1 + 2 * ε) := Real.sqrt_pos.mpr h_arg_pos
  have h_one_plus_pos : 0 < 1 + ε := by linarith
  -- Key algebraic step: sqrt(1 + 2ε) ≤ 1 + ε  (squaring both sides).
  have h_sqrt_le : Real.sqrt (1 + 2 * ε) ≤ 1 + ε := by
    calc Real.sqrt (1 + 2 * ε)
        ≤ Real.sqrt ((1 + ε)^2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
      _ = 1 + ε := Real.sqrt_sq (le_of_lt h_one_plus_pos)
  -- 1 / sqrt(1 + 2ε) ≥ 1 / (1 + ε)
  have h_inv_ge : 1 / (1 + ε) ≤ 1 / Real.sqrt (1 + 2 * ε) :=
    one_div_le_one_div_of_le h_sqrt_pos h_sqrt_le
  -- 1 - 1/(1+ε) = ε/(1+ε), so 1 - 1/sqrt(...) ≤ 1 - 1/(1+ε) = ε/(1+ε)
  have h_eq : 1 - 1 / (1 + ε) = ε / (1 + ε) := by
    field_simp; ring
  linarith [h_inv_ge, h_eq]

/-! ### sqrt of bpow at even exponent -/

/-- `√(β^(2e)) = β^e`. -/
theorem sqrt_bpow_even (beta : radix) (e : ℤ) :
    Real.sqrt (bpow beta (2 * e)) = bpow beta e := by
  have h_pos : 0 ≤ bpow beta e := le_of_lt (bpow_gt_0 beta e)
  rw [show (2 * e : ℤ) = e + e from by ring, bpow_plus, ← sq]
  exact Real.sqrt_sq h_pos

/-! ### Auxiliary: factoring a positive FLX value as `μ · β^(2e)` -/

/-- For positive `x ∈ FLX`, there exist `μ ∈ FLX` and `e ∈ ℤ` with
`x = μ · β^(2e)` and `1 ≤ μ < β²`. -/
theorem sqrt_error_N_FLX_aux1 (beta : radix) (prec : ℤ)
    {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x) (Px : 0 < x) :
    ∃ (mu : ℝ) (e : ℤ),
      generic_format beta (FLX_exp prec) mu ∧
      x = mu * bpow beta (2 * e) ∧
      1 ≤ mu ∧ mu < bpow beta 2 := by
  set e := (mag beta x - 1) / 2 with he_def
  set mu := x * bpow beta (-2 * e) with hmu_def
  -- β^(-2e) * β^(2e) = 1
  have h_bpow_inv : bpow beta (-2 * e) * bpow beta (2 * e) = 1 := by
    rw [← bpow_plus, show (-2 * e + 2 * e : ℤ) = 0 from by ring]
    rfl
  -- μ ∈ FLX (multiplying an FLX value by β^k stays in FLX)
  have Fmu : generic_format beta (FLX_exp prec) mu :=
    mult_bpow_exact_FLX beta prec (-2 * e) Fx
  refine ⟨mu, e, Fmu, ?_, ?_, ?_⟩
  · -- x = μ * β^(2e)
    show x = (x * bpow beta (-2 * e)) * bpow beta (2 * e)
    rw [mul_assoc, h_bpow_inv, mul_one]
  · -- 1 ≤ μ
    -- 1 ≤ μ ⟺ β^(2e) ≤ x ⟸ β^(2e) ≤ β^(mag x - 1) ≤ |x| = x.
    show 1 ≤ x * bpow beta (-2 * e)
    have h_neg2e_pos : 0 < bpow beta (-2 * e + 0) := bpow_gt_0 _ _
    have h_bpow_2e_pos : 0 < bpow beta (2 * e) := bpow_gt_0 _ _
    have h_two_e_le : 2 * e ≤ mag beta x - 1 := by
      -- 2 * ((mag β x - 1) / 2) ≤ mag β x - 1 (Euclidean ediv property)
      have h := Int.mul_ediv_add_emod (mag beta x - 1) 2
      have hmod_nn : 0 ≤ (mag beta x - 1) % 2 := Int.emod_nonneg _ (by decide)
      omega
    have h_step1 : bpow beta (2 * e) ≤ bpow beta (mag beta x - 1) :=
      bpow_le beta h_two_e_le
    have h_step2 : bpow beta (mag beta x - 1) ≤ |x| := by
      have h_x_ne : x ≠ 0 := ne_of_gt Px
      exact (bpow_mag_le beta h_x_ne)
    have h_abs : |x| = x := abs_of_pos Px
    have h_le : bpow beta (2 * e) ≤ x := by
      rw [← h_abs]; linarith [h_step1, h_step2]
    -- Now want 1 ≤ x * β^(-2e). Multiply both sides of h_le by β^(-2e):
    have := mul_le_mul_of_nonneg_right h_le (le_of_lt (bpow_gt_0 beta (-2 * e)))
    rw [show bpow beta (2 * e) * bpow beta (-2 * e)
          = bpow beta (-2 * e) * bpow beta (2 * e) from by ring,
        h_bpow_inv] at this
    exact this
  · -- μ < β²
    -- μ < β² ⟺ x < β^(2 + 2e). Note: x < β^(mag x), and mag x ≤ 2 + 2e since
    -- 2 * ((mag - 1) / 2) ≥ (mag - 1) - 1 = mag - 2.
    show x * bpow beta (-2 * e) < bpow beta 2
    have h_two_e_ge : mag beta x ≤ 2 + 2 * e := by
      have h := Int.mul_ediv_add_emod (mag beta x - 1) 2
      have hmod_lt : (mag beta x - 1) % 2 < 2 :=
        Int.emod_lt_of_pos _ (by decide)
      have hmod_nn : 0 ≤ (mag beta x - 1) % 2 := Int.emod_nonneg _ (by decide)
      omega
    have h_step1 : x < bpow beta (mag beta x) := by
      have h_x_ne : x ≠ 0 := ne_of_gt Px
      have := bpow_mag_gt beta x
      rw [abs_of_pos Px] at this
      exact this
    have h_step2 : bpow beta (mag beta x) ≤ bpow beta (2 + 2 * e) :=
      bpow_le beta h_two_e_ge
    have h_x_lt : x < bpow beta (2 + 2 * e) := lt_of_lt_of_le h_step1 h_step2
    have h_bpow_neg_pos : 0 < bpow beta (-2 * e) := bpow_gt_0 _ _
    have h_mul_lt :=
      (mul_lt_mul_of_pos_right h_x_lt h_bpow_neg_pos)
    have h_rhs_eq : bpow beta (2 + 2 * e) * bpow beta (-2 * e) = bpow beta 2 := by
      rw [← bpow_plus, show (2 + 2 * e + -2 * e : ℤ) = 2 from by ring]
    rw [h_rhs_eq] at h_mul_lt
    exact h_mul_lt

/-! ### Auxiliary: case analysis on `μ ∈ FLX` with `μ ≥ 1` -/

/-- For `μ ∈ FLX` with `1 ≤ μ` (and `prec > 1`), one of three cases holds:
`μ = 1`, `μ = 1 + 2·u_ro`, or `μ ≥ 1 + 4·u_ro`. -/
theorem sqrt_error_N_FLX_aux2 (beta : radix) (prec : ℤ) (Hp1 : 1 < prec)
    {mu : ℝ} (Fmu : generic_format beta (FLX_exp prec) mu)
    (HmuGe1 : 1 ≤ mu) :
    mu = 1 ∨ mu = 1 + 2 * u_ro beta prec ∨ 1 + 4 * u_ro beta prec ≤ mu := by
  have Hp : 0 < prec := by linarith
  have Pu_ro : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  -- 2 * u_ro = bpow(-prec + 1) = bpow(1 - prec).
  have h_2u_ro : 2 * u_ro beta prec = bpow beta (1 - prec) := by
    unfold u_ro
    rw [show (1 - prec : ℤ) = -prec + 1 from by ring]
    ring
  -- 2 * u_ro < 1, since 1 - prec < 0.
  have h_2u_lt_1 : 2 * u_ro beta prec < 1 := by
    rw [h_2u_ro]
    have h_bpow_0 : bpow beta 0 = 1 := by unfold bpow; simp
    rw [show (1 : ℝ) = bpow beta 0 from h_bpow_0.symm]
    exact bpow_lt beta (by omega)
  -- β ≥ 2.
  have h_beta_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by
    have := beta.prop
    have : (2 : ℤ) ≤ beta.val := this
    exact_mod_cast this
  -- 1 ∈ FLX
  have F1 : generic_format beta (FLX_exp prec) 1 :=
    generic_format_FLX_1 beta prec Hp
  -- Case split: μ ≤ 1 or μ > 1.
  by_cases HxLe1 : mu ≤ 1
  · left; linarith
  · push_neg at HxLe1
    right
    -- succ_FLX_1: succ 1 = 1 + bpow(1 - prec) = 1 + 2 * u_ro
    have h_succ_1 : succ beta (FLX_exp prec) 1 = 1 + 2 * u_ro beta prec := by
      rw [succ_FLX_1, h_2u_ro]
    have HmuGe1p2eps : 1 + 2 * u_ro beta prec ≤ mu := by
      rw [← h_succ_1]
      exact succ_le_lt beta (FLX_exp prec) (FLX_exp_valid prec Hp) F1 Fmu HxLe1
    by_cases HxLe1p2eps : mu ≤ 1 + 2 * u_ro beta prec
    · left; linarith
    · push_neg at HxLe1p2eps
      right
      -- 1 + 2u_ro is in F as succ of 1.
      have h_1p2u_ro_F : generic_format beta (FLX_exp prec)
          (1 + 2 * u_ro beta prec) := by
        rw [← h_succ_1]
        exact generic_format_succ beta (FLX_exp prec)
          (FLX_exp_valid prec Hp) F1
      -- succ(1 + 2u_ro) ≤ μ by succ_le_lt.
      have h_succ_le : succ beta (FLX_exp prec) (1 + 2 * u_ro beta prec) ≤ mu :=
        succ_le_lt beta (FLX_exp prec) (FLX_exp_valid prec Hp)
          h_1p2u_ro_F Fmu HxLe1p2eps
      -- succ(1 + 2u_ro) = 1 + 4u_ro: since 1 ≤ 1 + 2u_ro < β, mag = 1, and
      -- ulp(1 + 2u_ro) = bpow(1 - prec) = 2u_ro.
      have h_1p2u_ro_pos : 0 < 1 + 2 * u_ro beta prec := by linarith
      have h_1p2u_ro_lt_beta : 1 + 2 * u_ro beta prec < (beta.val : ℝ) := by
        linarith
      have h_mag_eq : mag beta (1 + 2 * u_ro beta prec) = 1 := by
        apply mag_unique_pos beta
        · show bpow beta (1 - 1) ≤ 1 + 2 * u_ro beta prec
          rw [show (1 - 1 : ℤ) = 0 from by ring]
          have h_bpow_0 : bpow beta 0 = 1 := by unfold bpow; simp
          rw [h_bpow_0]; linarith
        · show 1 + 2 * u_ro beta prec < bpow beta 1
          have h_bpow_1 : bpow beta 1 = (beta.val : ℝ) := by
            unfold bpow; simp
          rw [h_bpow_1]; exact h_1p2u_ro_lt_beta
      have h_ulp_eq : ulp beta (FLX_exp prec) (1 + 2 * u_ro beta prec)
          = 2 * u_ro beta prec := by
        rw [ulp_neq_0 beta (FLX_exp prec) (ne_of_gt h_1p2u_ro_pos)]
        show bpow beta (cexp beta (FLX_exp prec) (1 + 2 * u_ro beta prec))
            = 2 * u_ro beta prec
        unfold cexp FLX_exp
        rw [h_mag_eq, h_2u_ro]
      have h_succ_eq : succ beta (FLX_exp prec) (1 + 2 * u_ro beta prec)
          = 1 + 4 * u_ro beta prec := by
        rw [succ_eq_pos beta (FLX_exp prec) (le_of_lt h_1p2u_ro_pos), h_ulp_eq]
        ring
      linarith [h_succ_le, h_succ_eq]

/-! ### Auxiliary: pure analytic inequality between unit-roundoff sqrt forms -/

/-- `u_ro / √(1 + 4·u_ro) ≤ 1 - 1/√(1 + 2·u_ro)`. The mathematical kernel is
`s · (s + 1) ≤ 2t` where `s = √(1 + 2·u_ro), t = √(1 + 4·u_ro)`, which holds
since `s ∈ [1, √2]` and `t² = 2s² − 1`. -/
theorem sqrt_error_N_FLX_aux3 (beta : radix) (prec : ℤ) (Hp : 0 < prec) :
    u_ro beta prec / Real.sqrt (1 + 4 * u_ro beta prec)
      ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) := by
  set ε := u_ro beta prec with hε_def
  have hε_nn : 0 ≤ ε := u_ro_pos beta prec
  -- ε ≤ 1/2.
  have hε_le : ε ≤ 1/2 := by
    show u_ro beta prec ≤ 1/2
    unfold u_ro
    have h_bpow_0 : bpow beta 0 = 1 := by unfold bpow; simp
    have h_le : bpow beta (-prec + 1) ≤ bpow beta 0 := bpow_le beta (by omega)
    rw [h_bpow_0] at h_le; linarith
  set s := Real.sqrt (1 + 2 * ε) with hs_def
  set t := Real.sqrt (1 + 4 * ε) with ht_def
  have h_1p2_pos : 0 < 1 + 2 * ε := by linarith
  have h_1p4_pos : 0 < 1 + 4 * ε := by linarith
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h_1p2_pos
  have ht_pos : 0 < t := Real.sqrt_pos.mpr h_1p4_pos
  have hs_sq : s^2 = 1 + 2 * ε := Real.sq_sqrt (le_of_lt h_1p2_pos)
  have ht_sq : t^2 = 1 + 4 * ε := Real.sq_sqrt (le_of_lt h_1p4_pos)
  -- s ≥ 1.
  have hs_ge_1 : 1 ≤ s := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + 2 * ε) := Real.sqrt_le_sqrt (by linarith)
  -- s² ≤ 2 (from ε ≤ 1/2).
  have hs_sq_le_2 : s^2 ≤ 2 := by rw [hs_sq]; linarith
  -- t ≥ 1.
  have ht_ge_1 : 1 ≤ t := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + 4 * ε) := Real.sqrt_le_sqrt (by linarith)
  -- Core polynomial step: (s² + s)² ≤ 4t².
  -- Equivalent: s⁴ + 2s³ - 7s² + 4 ≤ 0.
  -- Factor: (s - 1)(s³ + 3s² - 4s - 4). For s ∈ [1, √2], (s-1) ≥ 0, but
  -- s³ + 3s² - 4s - 4 ≤ 0 (using s³ ≤ 2s and 3s² ≤ 6 and -2s+2 ≤ 0).
  have h_s_cubed_le : s^3 ≤ 2 * s := by
    have : s * s^2 ≤ s * 2 := mul_le_mul_of_nonneg_left hs_sq_le_2 (by linarith)
    have h_eq : s * s^2 = s^3 := by ring
    rw [h_eq] at this; linarith
  have h_q_le : s^3 + 3 * s^2 - 4 * s - 4 ≤ 0 := by
    -- s³ + 3s² - 4s - 4 ≤ 2s + 6 - 4s - 4 = 2 - 2s ≤ 0
    nlinarith [h_s_cubed_le, hs_sq_le_2, hs_ge_1]
  have h_poly_le : s^4 + 2 * s^3 - 7 * s^2 + 4 ≤ 0 := by
    -- = (s - 1) · (s³ + 3s² - 4s - 4)
    have h_factor : s^4 + 2 * s^3 - 7 * s^2 + 4
                  = (s - 1) * (s^3 + 3 * s^2 - 4 * s - 4) := by ring
    rw [h_factor]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) h_q_le
  -- Therefore (s² + s)² ≤ 4t².
  -- t² = 1 + 4ε = 2s² - 1, so 4t² - (s² + s)² = 8s² - 4 - s⁴ - 2s³ - s²
  --                                             = -(s⁴ + 2s³ - 7s² + 4) ≥ 0.
  have h_t_eq : t^2 = 2 * s^2 - 1 := by rw [ht_sq, hs_sq]; ring
  have h_sq_bound : (s^2 + s)^2 ≤ 4 * t^2 := by
    nlinarith [h_poly_le, h_t_eq, sq_nonneg s]
  -- s² + s ≤ 2t (both nonneg).
  have h_s_plus_sq_nn : 0 ≤ s^2 + s := by nlinarith [hs_ge_1]
  have h_2t_nn : 0 ≤ 2 * t := by linarith
  have h_linear : s^2 + s ≤ 2 * t := by
    have h_sq_bound' : (s^2 + s)^2 ≤ (2 * t)^2 := by
      have : (2 * t)^2 = 4 * t^2 := by ring
      linarith [h_sq_bound]
    -- abs_le_of_sq_le_sq: |a| ≤ b if a² ≤ b² and b ≥ 0
    exact abs_le_of_sq_le_sq' h_sq_bound' h_2t_nn |>.2
  -- Final algebraic step.
  -- Cross-multiplied form: ε · s ≤ t · (s - 1).
  -- From s² - 1 = 2ε: 2ε = (s-1)(s+1), so ε = (s-1)(s+1)/2.
  -- ε · s = (s-1)(s+1) · s / 2 ≤ (s-1) · t (using h_linear).
  have h_2ε : 2 * ε = s^2 - 1 := by rw [hs_sq]; ring
  have h_2ε_fact : 2 * ε = (s - 1) * (s + 1) := by rw [h_2ε]; ring
  have h_mul_le : (s - 1) * (s^2 + s) ≤ (s - 1) * (2 * t) :=
    mul_le_mul_of_nonneg_left h_linear (by linarith)
  -- (s - 1) · (s² + s) = (s - 1) · s · (s + 1) = 2ε · s
  have h_lhs_eq : (s - 1) * (s^2 + s) = 2 * ε * s := by
    rw [h_2ε_fact]; ring
  -- (s - 1) · (2 · t) = 2 · t · (s - 1)
  have h_rhs_eq : (s - 1) * (2 * t) = 2 * (t * (s - 1)) := by ring
  -- So 2ε · s ≤ 2 · t · (s - 1), i.e., ε · s ≤ t · (s - 1).
  have h_eps_s : ε * s ≤ t * (s - 1) := by
    have := h_mul_le
    rw [h_lhs_eq, h_rhs_eq] at this
    linarith
  -- Convert to the desired form: ε/t ≤ 1 - 1/s.
  have h_one_sub_inv : 1 - 1/s = (s - 1)/s := by
    field_simp
  rw [h_one_sub_inv]
  rw [div_le_div_iff₀ ht_pos hs_pos]
  linarith [h_eps_s]

/-! ### Main theorem: sqrt error bound in FLX -/

/-- For round-to-nearest in FLX, the error of `√x` is bounded by
`(1 - 1/√(1 + 2·u_ro)) · |√x|`. -/
theorem sqrt_error_N_FLX (beta : radix) (prec : ℤ) (Hp1 : 1 < prec)
    (choice : ℤ → Bool) {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x) :
    |round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) - Real.sqrt x|
      ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * |Real.sqrt x| := by
  have Hp : 0 < prec := by linarith
  have Pu_ro_nn : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  have Pu_ro_pos : 0 < u_ro beta prec := by
    unfold u_ro
    exact mul_pos (by norm_num) (bpow_gt_0 _ _)
  have Pb : 0 ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) :=
    om1ds1p2u_ro_pos beta prec
  -- Case 1: x ≤ 0.
  rcases le_or_lt x 0 with Nx | Px
  · have h_sqrt_0 : Real.sqrt x = 0 := Real.sqrt_eq_zero'.mpr Nx
    rw [h_sqrt_0, round_0, sub_zero, abs_zero, mul_zero]
  -- Case 2: x > 0.
  obtain ⟨mu, e, Fmu, Hmu, HmuGe1, HmuLtBetaSq⟩ :=
    sqrt_error_N_FLX_aux1 beta prec Fx Px
  set t := Real.sqrt x with ht_def
  have h_mu_nn : (0 : ℝ) ≤ mu := by linarith
  have h_sqrt_mu_pos : 0 < Real.sqrt mu := Real.sqrt_pos.mpr (by linarith)
  have h_bpow_e_pos : 0 < bpow beta e := bpow_gt_0 _ _
  -- t = sqrt μ · β^e.
  have Ht : t = Real.sqrt mu * bpow beta e := by
    show Real.sqrt x = Real.sqrt mu * bpow beta e
    rw [Hmu, Real.sqrt_mul h_mu_nn, sqrt_bpow_even beta e]
  have Pt : 0 < t := by rw [Ht]; exact mul_pos h_sqrt_mu_pos h_bpow_e_pos
  -- Dispatch on aux2.
  rcases sqrt_error_N_FLX_aux2 beta prec Hp1 Fmu HmuGe1 with Hmu' | Hmu' | Hmu'
  · -- Case (a): μ = 1. Then t = β^e ∈ FLX.
    have h_sqrt_mu : Real.sqrt mu = 1 := by rw [Hmu', Real.sqrt_one]
    have h_t_eq_bpow : t = bpow beta e := by
      rw [Ht, h_sqrt_mu, one_mul]
    have h_Fbpow : generic_format beta (FLX_exp prec) (bpow beta e) := by
      apply generic_format_bpow beta (FLX_exp prec)
      unfold FLX_exp; omega
    rw [h_t_eq_bpow, round_generic beta (FLX_exp prec) _ h_Fbpow,
        sub_self, abs_zero]
    exact mul_nonneg Pb (abs_nonneg _)
  · -- Case (b): μ = 1 + 2·u_ro. Then 1 ≤ √μ < 1 + u_ro.
    -- 2 * u_ro = bpow(1 - prec) (used in succ computation).
    have h_2u_ro : 2 * u_ro beta prec = bpow beta (1 - prec) := by
      unfold u_ro
      rw [show (1 - prec : ℤ) = -prec + 1 from by ring]; ring
    have h_sqrt_mu_lb : 1 ≤ Real.sqrt mu := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt mu := Real.sqrt_le_sqrt HmuGe1
    have h_sqrt_mu_ub : Real.sqrt mu < 1 + u_ro beta prec := by
      have h_one_plus_pos : 0 < 1 + u_ro beta prec := by linarith
      have h_sq_ub : mu < (1 + u_ro beta prec)^2 := by
        rw [Hmu']; nlinarith [Pu_ro_pos]
      calc Real.sqrt mu < Real.sqrt ((1 + u_ro beta prec)^2) :=
            Real.sqrt_lt_sqrt h_mu_nn h_sq_ub
        _ = 1 + u_ro beta prec := Real.sqrt_sq (le_of_lt h_one_plus_pos)
    -- β^e ∈ FLX
    have h_Fbpow : generic_format beta (FLX_exp prec) (bpow beta e) := by
      apply generic_format_bpow beta (FLX_exp prec)
      unfold FLX_exp; omega
    have h_succ_bpow : succ beta (FLX_exp prec) (bpow beta e)
        = bpow beta e * (1 + 2 * u_ro beta prec) := by
      rw [succ_eq_pos beta (FLX_exp prec) (le_of_lt h_bpow_e_pos)]
      rw [ulp_bpow]
      show bpow beta e + bpow beta (FLX_exp prec (e + 1)) =
           bpow beta e * (1 + 2 * u_ro beta prec)
      unfold FLX_exp
      rw [h_2u_ro, show (e + 1 - prec : ℤ) = e + (1 - prec) from by ring]
      rw [bpow_plus]; ring
    -- t < midpoint between β^e and succ β^e.
    have h_t_lt_midp : t < (bpow beta e + succ beta (FLX_exp prec) (bpow beta e)) / 2 := by
      rw [Ht, h_succ_bpow]
      have h_step : Real.sqrt mu * bpow beta e < (1 + u_ro beta prec) * bpow beta e :=
        mul_lt_mul_of_pos_right h_sqrt_mu_ub h_bpow_e_pos
      have h_calc : (bpow beta e + bpow beta e * (1 + 2 * u_ro beta prec)) / 2
                    = (1 + u_ro beta prec) * bpow beta e := by ring
      linarith [h_step, h_calc]
    have h_rt_le : round beta (FLX_exp prec) (Znearest choice) t ≤ bpow beta e :=
      round_N_le_midp beta (FLX_exp prec) (FLX_exp_valid prec Hp)
        choice h_Fbpow h_t_lt_midp
    have h_rt_ge : bpow beta e ≤ round beta (FLX_exp prec) (Znearest choice) t := by
      apply round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec Hp) _ h_Fbpow
      rw [Ht]
      have h_step : 1 * bpow beta e ≤ Real.sqrt mu * bpow beta e :=
        mul_le_mul_of_nonneg_right h_sqrt_mu_lb (le_of_lt h_bpow_e_pos)
      linarith [h_step]
    have Hrt : round beta (FLX_exp prec) (Znearest choice) t = bpow beta e :=
      le_antisymm h_rt_le h_rt_ge
    -- Stitch: |β^e - √μ · β^e| ≤ (1 - 1/√(1+2u_ro)) · |√μ · β^e|.
    -- Both sides equal (√μ - 1) · β^e.
    rw [Hrt, Ht]
    have h_t_pos : 0 < Real.sqrt mu * bpow beta e :=
      mul_pos h_sqrt_mu_pos h_bpow_e_pos
    have h_diff : bpow beta e - Real.sqrt mu * bpow beta e
                = -(bpow beta e * (Real.sqrt mu - 1)) := by ring
    rw [h_diff, abs_neg, abs_mul, abs_of_pos h_bpow_e_pos,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.sqrt mu - 1),
        abs_of_pos h_t_pos]
    rw [show mu = 1 + 2 * u_ro beta prec from Hmu']
    -- Goal: bpow e * (√(1+2u_ro) - 1) ≤ (1 - 1/√(1+2u_ro)) * (√(1+2u_ro) * bpow e)
    have h_s_pos : 0 < Real.sqrt (1 + 2 * u_ro beta prec) :=
      Real.sqrt_pos.mpr (by linarith)
    have h_eq_rhs : (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec))
                      * (Real.sqrt (1 + 2 * u_ro beta prec) * bpow beta e)
                  = bpow beta e * (Real.sqrt (1 + 2 * u_ro beta prec) - 1) := by
      field_simp
    linarith [h_eq_rhs]
  · -- Case (c): 1 + 4·u_ro ≤ μ. So 1 + u_ro < √μ.
    have h_2u_ro : 2 * u_ro beta prec = bpow beta (1 - prec) := by
      unfold u_ro
      rw [show (1 - prec : ℤ) = -prec + 1 from by ring]; ring
    have h_sqrt_mu_gt : 1 + u_ro beta prec < Real.sqrt mu := by
      have h_one_plus_pos : 0 < 1 + u_ro beta prec := by linarith
      have h_uro_lt_1 : u_ro beta prec < 1 := u_ro_lt_1 beta prec Hp
      have h_sq_lb : (1 + u_ro beta prec)^2 < mu := by
        nlinarith [Pu_ro_pos, h_uro_lt_1, Hmu', sq_nonneg (u_ro beta prec)]
      calc 1 + u_ro beta prec
          = Real.sqrt ((1 + u_ro beta prec)^2) :=
            (Real.sqrt_sq (le_of_lt h_one_plus_pos)).symm
        _ < Real.sqrt mu := Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_lb
    have h_mu_lt_beta_sq : mu < (beta.val : ℝ)^2 := by
      have h_bpow_2 : bpow beta 2 = (beta.val : ℝ)^2 := by
        unfold bpow; rfl
      rw [← h_bpow_2]; exact HmuLtBetaSq
    have h_sqrt_mu_lt_beta : Real.sqrt mu < beta.val := by
      have h_beta_pos : (0 : ℝ) < beta.val := radix_pos beta
      calc Real.sqrt mu < Real.sqrt ((beta.val : ℝ)^2) :=
            Real.sqrt_lt_sqrt h_mu_nn h_mu_lt_beta_sq
        _ = beta.val := Real.sqrt_sq (le_of_lt h_beta_pos)
    -- mag t = 1 + e.
    have h_mag_t : mag beta t = 1 + e := by
      apply mag_unique_pos beta
      · rw [show (1 + e - 1 : ℤ) = e from by ring, Ht]
        have h_step : 1 * bpow beta e ≤ Real.sqrt mu * bpow beta e :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h_bpow_e_pos)
        linarith [h_step]
      · rw [Ht]
        rw [show (1 + e : ℤ) = e + 1 from by ring, bpow_plus]
        rw [show bpow beta 1 = (beta.val : ℝ) from by unfold bpow; simp]
        rw [show bpow beta e * (beta.val : ℝ) = (beta.val : ℝ) * bpow beta e from
              by ring]
        exact mul_lt_mul_of_pos_right h_sqrt_mu_lt_beta h_bpow_e_pos
    have Hulpt : ulp beta (FLX_exp prec) t = 2 * u_ro beta prec * bpow beta e := by
      rw [ulp_neq_0 beta (FLX_exp prec) (ne_of_gt Pt)]
      show bpow beta (cexp beta (FLX_exp prec) t) = 2 * u_ro beta prec * bpow beta e
      unfold cexp FLX_exp
      rw [h_mag_t, h_2u_ro]
      rw [show (1 + e - prec : ℤ) = (1 - prec) + e from by ring, bpow_plus]
    have h_err_half : |round beta (FLX_exp prec) (Znearest choice) t - t|
                    ≤ (1/2) * ulp beta (FLX_exp prec) t :=
      error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec Hp) choice t
    have h_err_bound : |round beta (FLX_exp prec) (Znearest choice) t - t|
                    ≤ u_ro beta prec * bpow beta e := by
      have h_half : (1/2) * ulp beta (FLX_exp prec) t = u_ro beta prec * bpow beta e := by
        rw [Hulpt]; ring
      linarith [h_err_half, h_half]
    -- Now bound: u_ro · β^e ≤ (1 - 1/√(1+2u_ro)) · |t|.
    rw [abs_of_pos Pt]
    have h_aux3 := sqrt_error_N_FLX_aux3 beta prec Hp
    have h_sqrt_1p4_pos : 0 < Real.sqrt (1 + 4 * u_ro beta prec) :=
      Real.sqrt_pos.mpr (by linarith)
    have h_sqrt_mu_ge : Real.sqrt (1 + 4 * u_ro beta prec) ≤ Real.sqrt mu :=
      Real.sqrt_le_sqrt Hmu'
    have h_uro_div_le : u_ro beta prec / Real.sqrt mu
                      ≤ u_ro beta prec / Real.sqrt (1 + 4 * u_ro beta prec) :=
      div_le_div_of_nonneg_left Pu_ro_nn h_sqrt_1p4_pos h_sqrt_mu_ge
    have h_final_quot : u_ro beta prec / Real.sqrt mu
                      ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) :=
      le_trans h_uro_div_le h_aux3
    have h_bound_mul : u_ro beta prec * bpow beta e
                    ≤ (1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec)) * t := by
      rw [Ht]
      have h_decomp : u_ro beta prec * bpow beta e
                  = (u_ro beta prec / Real.sqrt mu) * (Real.sqrt mu * bpow beta e) := by
        field_simp
      rw [h_decomp]
      have h_mul_pos : 0 ≤ Real.sqrt mu * bpow beta e :=
        le_of_lt (mul_pos h_sqrt_mu_pos h_bpow_e_pos)
      exact mul_le_mul_of_nonneg_right h_final_quot h_mul_pos
    linarith [h_err_bound, h_bound_mul]

/-- The `1 + ε` form for round-to-nearest sqrt in FLX. -/
theorem sqrt_error_N_FLX_ex (beta : radix) (prec : ℤ) (Hp1 : 1 < prec)
    (choice : ℤ → Bool) {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x) :
    ∃ eps : ℝ, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) ∧
      round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)
        = Real.sqrt x * (1 + eps) :=
  relative_error_le_conversion beta (FLX_exp prec) (Znearest choice)
    (om1ds1p2u_ro_pos beta prec)
    (sqrt_error_N_FLX beta prec Hp1 choice Fx)

/-- The `1 + ε` form w.r.t. the rounded value: bound `sqrt(1+2·u_ro) - 1`. -/
theorem sqrt_error_N_FLX_round_ex (beta : radix) (prec : ℤ) (Hp1 : 1 < prec)
    (choice : ℤ → Bool) {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x) :
    ∃ eps : ℝ, |eps| ≤ Real.sqrt (1 + 2 * u_ro beta prec) - 1 ∧
      Real.sqrt x = round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x)
                      * (1 + eps) := by
  -- Use the sqrt analog of relative_error_N_round_ex_derive.
  obtain ⟨d, Bd, Hd⟩ := sqrt_error_N_FLX_ex beta prec Hp1 choice Fx
  have Hp : 0 < prec := by linarith
  have Pu_ro_nn : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  have h_arg_pos : 0 < 1 + 2 * u_ro beta prec := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (1 + 2 * u_ro beta prec) :=
    Real.sqrt_pos.mpr h_arg_pos
  have h_sqrt_ge_1 : 1 ≤ Real.sqrt (1 + 2 * u_ro beta prec) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + 2 * u_ro beta prec) :=
          Real.sqrt_le_sqrt (by linarith)
  have h_d_le : |d| ≤ 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) := Bd
  have h_one_minus_inv_pos : 1 - 1 / Real.sqrt (1 + 2 * u_ro beta prec) < 1 := by
    have : 0 < 1 / Real.sqrt (1 + 2 * u_ro beta prec) :=
      div_pos one_pos h_sqrt_pos
    linarith
  have h_d_abs : |d| < 1 := lt_of_le_of_lt h_d_le h_one_minus_inv_pos
  have h_abs_d := abs_le.mp h_d_le
  have h_one_plus_d_pos : 0 < 1 + d := by
    have := neg_lt_of_abs_lt h_d_abs; linarith
  by_cases Zfx : round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [abs_zero]; exact s1p2u_rom1_pos beta prec
    · rw [Zfx, zero_mul]
      rw [Zfx] at Hd
      have h_pos_imply : Real.sqrt x = 0 := by
        have := Hd
        rcases mul_eq_zero.mp this.symm with h_sqrt0 | h_d1
        · exact h_sqrt0
        · linarith
      exact h_pos_imply
  by_cases Zx : Real.sqrt x = 0
  · -- sqrt x = 0 ⟹ round 0 = 0, so Zfx is contradicted unless we exit.
    exfalso; apply Zfx
    rw [Hd, Zx, zero_mul]
  -- General case: define d' := (sqrt x - rx) / rx.
  refine ⟨(Real.sqrt x - round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x))
            / round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x), ?_, ?_⟩
  · -- |d'| = |sqrt x - rx| / |rx|. Rationalize using Hd to get -d / (1 + d).
    -- |d'| ≤ sqrt(1 + 2·u_ro) - 1.
    set rx := round beta (FLX_exp prec) (Znearest choice) (Real.sqrt x) with hrx_def
    have h_xsubrx : Real.sqrt x - rx = -(Real.sqrt x * d) := by rw [Hd]; ring
    have h_abs_diff : |Real.sqrt x - rx| = |Real.sqrt x| * |d| := by
      rw [h_xsubrx, abs_neg, abs_mul]
    have h_abs_rx : |rx| = |Real.sqrt x| * (1 + d) := by
      rw [Hd, abs_mul, abs_of_pos h_one_plus_d_pos]
    rw [abs_div, h_abs_diff, h_abs_rx]
    have h_x_pos : 0 < |Real.sqrt x| := abs_pos.mpr Zx
    have h_denom_pos : 0 < |Real.sqrt x| * (1 + d) :=
      mul_pos h_x_pos h_one_plus_d_pos
    rw [div_le_iff₀ h_denom_pos]
    -- Goal: |sqrt x| * |d| ≤ (sqrt(1+2u_ro) - 1) * (|sqrt x| * (1 + d))
    -- Sufficient: |d| ≤ (sqrt(1+2u_ro) - 1) * (1 + d).
    -- Note: 1 - 1/s = (s - 1)/s, where s = sqrt(1+2u_ro). And |d| ≤ (s-1)/s.
    -- So |d|·s ≤ s - 1, i.e., |d| ≤ (s-1) - |d|·(s-1)/... hmm, need clean form.
    -- |d| ≤ (s-1)/s = 1 - 1/s.
    -- Want: |d| ≤ (s-1) · (1+d) = (s-1) + (s-1)·d.
    set s := Real.sqrt (1 + 2 * u_ro beta prec)
    have h_d_bound : |d| ≤ (s - 1) / s := by
      have h_eq : 1 - 1/s = (s - 1)/s := by field_simp
      rw [← h_eq]; exact h_d_le
    -- |d| · s ≤ s - 1.
    have h_d_s_bound : |d| * s ≤ s - 1 := by
      rw [le_div_iff₀ h_sqrt_pos] at h_d_bound; exact h_d_bound
    -- (s - 1)(1 + d) - |d|: split on sign of d.
    have h_key : |d| ≤ (s - 1) * (1 + d) := by
      rcases le_or_lt 0 d with hd_nn | hd_neg
      · rw [abs_of_nonneg hd_nn]
        -- d ≤ (s-1)(1+d) = (s-1) + (s-1)d. From |d|·s ≤ s-1: d·s ≤ s-1.
        -- So d ≤ (s-1)/s. And (s-1)(1+d) ≥ (s-1) ≥ d/s · s = d (if s ≥ 1).
        -- Direct: (s-1)(1+d) - d = (s-1) + (s-1)d - d = (s-1) + d·(s-2).
        -- Need ≥ 0. Have s ≥ 1.
        -- For s ≥ 2: (s-1)+d(s-2) ≥ 0 since both terms ≥ 0.
        -- For 1 ≤ s < 2: (s-1) ≥ 0, d(s-2) could be negative. Use d·s ≤ s-1 ≤ d/... hmm.
        -- Alt: (s-1)(1+d) ≥ (s-1)/s · s = s - 1. And |d| · s ≤ s - 1. So |d| ≤ (s-1)/s.
        -- Want d ≤ (s-1)(1+d). Equiv: d(1 - (s-1)) ≤ s - 1, i.e., d(2-s) ≤ s-1.
        -- For s ≥ 1: |d| ≤ (s-1)/s ≤ 1.
        -- For s ≤ 2: 2-s ≥ 0, so d·(2-s) ≤ |d|·(2-s) ≤ ((s-1)/s)·(2-s).
        --   We want ((s-1)/s)(2-s) ≤ s-1. Divide by (s-1) > 0 (case s > 1): (2-s)/s ≤ 1, i.e., 2-s ≤ s, i.e., s ≥ 1. ✓
        -- For s = 1: d ≤ 0 (since |d| ≤ 0) and goal is 0 ≤ 0. ✓
        nlinarith [h_d_s_bound, hd_nn, abs_of_nonneg hd_nn, h_sqrt_ge_1,
                   sq_nonneg d, sq_nonneg (s - 1)]
      · rw [abs_of_neg hd_neg]
        -- -d ≤ (s-1)(1+d). Note d < 0, so 1+d < 1.
        -- |d| · s ≤ s - 1 gives -d·s ≤ s-1, i.e., d·s ≥ 1-s.
        -- Want -d ≤ (s-1)(1+d) = (s-1) + (s-1)d. So -d - (s-1)d ≤ s-1, i.e., -d·s ≤ s-1. ✓
        nlinarith [h_d_s_bound, hd_neg, abs_of_neg hd_neg, h_sqrt_ge_1]
    -- |sqrt x| * |d| ≤ |sqrt x| * (s-1)(1+d) = (s-1) * (|sqrt x| * (1+d)).
    have := mul_le_mul_of_nonneg_left h_key (le_of_lt h_x_pos)
    nlinarith [this, h_x_pos, h_one_plus_d_pos, h_sqrt_ge_1]
  · -- sqrt x = rx * (1 + (sqrt x - rx)/rx). Algebra (rx ≠ 0).
    field_simp
    rw [Hd]; ring

end LeanFlocq
