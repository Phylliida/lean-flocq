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

end LeanFlocq
