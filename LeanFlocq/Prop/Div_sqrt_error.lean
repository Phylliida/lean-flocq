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

end LeanFlocq
