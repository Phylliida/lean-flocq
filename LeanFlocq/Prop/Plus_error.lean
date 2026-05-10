/-
Lean port of Coq Flocq's `Prop/Plus_error.v` — error of addition is in
the format. Selected keystone theorems.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Calc.Operations
import LeanFlocq.Core.FIX
import LeanFlocq.Core.FLX
import LeanFlocq.Core.FLT
import LeanFlocq.Core.Ulp

namespace LeanFlocq

/-- Rounding `F2R(Float m e)` keeps the same exponent `e` for some new mantissa.

Useful for showing that error of an exact-exponent operation can be expressed
at the same exponent. -/
theorem round_repr_same_exp (beta : radix) (fexp : ℤ → ℤ)
    (rnd : ℝ → ℤ) [hv : Valid_rnd rnd]
    (m e : ℤ) :
    ∃ m' : ℤ, round beta fexp rnd (F2R (beta := beta) ⟨m, e⟩)
              = F2R (beta := beta) ⟨m', e⟩ := by
  set e' := cexp beta fexp (F2R (beta := beta) ⟨m, e⟩) with he'_def
  by_cases He : e' ≤ e
  · -- Sufficient precision: round leaves the integer alone.
    refine ⟨m, ?_⟩
    show ((rnd (F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e')) : ℤ) : ℝ) * bpow beta e'
        = F2R (beta := beta) ⟨m, e⟩
    have h_diff_nn : 0 ≤ e - e' := by linarith
    -- F2R * bpow(-e') = m * beta^(e - e') as an integer.
    have h_eq : F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e')
              = ((m * (beta.val : ℤ) ^ (e - e').toNat : ℤ) : ℝ) := by
      show ((m : ℝ) * bpow beta e) * bpow beta (-e') = _
      rw [mul_assoc, ← bpow_plus]
      have he : e + -e' = e - e' := by ring
      rw [he, ← IZR_Zpower beta h_diff_nn]
      push_cast; ring
    rw [h_eq, hv.Zrnd_intCast]
    -- Now: (m * beta^(e-e') : ℝ) * bpow e' = F2R ⟨m, e⟩.
    show ((m * (beta.val : ℤ) ^ (e - e').toNat : ℤ) : ℝ) * bpow beta e'
        = (m : ℝ) * bpow beta e
    rw [show ((m * (beta.val : ℤ) ^ (e - e').toNat : ℤ) : ℝ)
        = (m : ℝ) * (((beta.val : ℤ) ^ (e - e').toNat : ℤ) : ℝ) from by push_cast; ring]
    rw [IZR_Zpower beta h_diff_nn, mul_assoc, ← bpow_plus]
    have he : e - e' + e' = e := by ring
    rw [he]
  · -- Insufficient precision: m' = rnd(m * bpow(e - e')) * beta^(e' - e).
    push_neg at He
    refine ⟨rnd (F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e'))
            * (beta.val : ℤ) ^ (e' - e).toNat, ?_⟩
    show ((rnd (F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e')) : ℤ) : ℝ) * bpow beta e'
        = ((rnd (F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e'))
            * (beta.val : ℤ) ^ (e' - e).toNat : ℤ) : ℝ) * bpow beta e
    have h_diff_nn : 0 ≤ e' - e := by linarith
    set rmd := rnd (F2R (beta := beta) ⟨m, e⟩ * bpow beta (-e')) with hrmd_def
    show (rmd : ℝ) * bpow beta e'
        = ((rmd * (beta.val : ℤ) ^ (e' - e).toNat : ℤ) : ℝ) * bpow beta e
    rw [show ((rmd * (beta.val : ℤ) ^ (e' - e).toNat : ℤ) : ℝ)
        = (rmd : ℝ) * (((beta.val : ℤ) ^ (e' - e).toNat : ℤ) : ℝ) from by push_cast; ring]
    rw [IZR_Zpower beta h_diff_nn, mul_assoc, ← bpow_plus]
    have he : e' - e + e = e' := by ring
    rw [he]

/-- Helper for `plus_error`: when `cexp x ≤ cexp y`, the addition error is
exactly representable. -/
theorem plus_error_aux (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    (choice : ℤ → Bool)
    {x y : ℝ}
    (He : cexp beta fexp x ≤ cexp beta fexp y)
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y) :
    generic_format beta fexp
      (round beta fexp (Znearest choice) (x + y) - (x + y)) := by
  by_cases H0 : round beta fexp (Znearest choice) (x + y) - (x + y) = 0
  · rw [H0]; exact generic_format_0 _ _
  set ex := cexp beta fexp x with hex_def
  set ey := cexp beta fexp y with hey_def
  set mx := Ztrunc (scaled_mantissa beta fexp x) with hmx_def
  set my := Ztrunc (scaled_mantissa beta fexp y) with hmy_def
  have h_diff_nn : 0 ≤ ey - ex := by linarith
  -- x + y = F2R ⟨mx + my * beta^(ey - ex), ex⟩.
  have Hxy : x + y = F2R (beta := beta)
                      ⟨mx + my * (beta.val : ℤ) ^ (ey - ex).toNat, ex⟩ := by
    have hx : x = (mx : ℝ) * bpow beta ex := Fx
    have hy : y = (my : ℝ) * bpow beta ey := Fy
    show x + y = ((mx + my * (beta.val : ℤ) ^ (ey - ex).toNat : ℤ) : ℝ) * bpow beta ex
    rw [hx, hy]
    rw [show (ey : ℤ) = (ey - ex) + ex from by ring]
    rw [bpow_plus, ← IZR_Zpower beta h_diff_nn]
    push_cast; ring_nf
  rw [Hxy]
  obtain ⟨mxy, Hxy'⟩ := round_repr_same_exp beta fexp (Znearest choice)
                          (mx + my * (beta.val : ℤ) ^ (ey - ex).toNat) ex
  rw [Hxy']
  rw [show (F2R (beta := beta) ⟨mxy, ex⟩
        - F2R (beta := beta) ⟨mx + my * (beta.val : ℤ) ^ (ey - ex).toNat, ex⟩)
        = F2R (beta := beta)
            ⟨mxy - (mx + my * (beta.val : ℤ) ^ (ey - ex).toNat), ex⟩ from by
        rw [← F2R_minus, Fminus_same_exp]]
  apply generic_format_F2R beta fexp _ ex
  intro _
  show cexp beta fexp
        (F2R (beta := beta)
          ⟨mxy - (mx + my * (beta.val : ℤ) ^ (ey - ex).toNat), ex⟩) ≤ ex
  -- Rewrite this F2R back to round - (x + y).
  have h_eq : F2R (beta := beta)
                ⟨mxy - (mx + my * (beta.val : ℤ) ^ (ey - ex).toNat), ex⟩
            = round beta fexp (Znearest choice) (x + y) - (x + y) := by
    rw [← Fminus_same_exp, F2R_minus, ← Hxy', ← Hxy]
  rw [h_eq]
  -- Now: cexp(error) ≤ ex = cexp x. Use Monotone_exp + mag(error) ≤ mag(x).
  show cexp beta fexp (round beta fexp (Znearest choice) (x + y) - (x + y)) ≤ ex
  unfold cexp
  apply hMon
  apply mag_le_abs beta H0
  -- |error| ≤ |x|, since |round_N(x+y) - (x+y)| ≤ |y - (x+y)| = |x|.
  have h_y_dist : |round beta fexp (Znearest choice) (x + y) - (x + y)|
                ≤ |y - (x + y)| :=
    (round_N_pt beta fexp hValid choice (x + y)).2 y Fy
  rw [show y - (x + y) = -x from by ring, abs_neg] at h_y_dist
  exact h_y_dist

/-- The error of addition is exactly representable: `round_N(x + y) - (x + y) ∈ F`. -/
theorem plus_error (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    (choice : ℤ → Bool)
    {x y : ℝ}
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y) :
    generic_format beta fexp
      (round beta fexp (Znearest choice) (x + y) - (x + y)) := by
  rcases le_or_gt (cexp beta fexp x) (cexp beta fexp y) with He | He
  · exact plus_error_aux beta fexp hValid hMon choice He Fx Fy
  · rw [add_comm]
    exact plus_error_aux beta fexp hValid hMon choice (le_of_lt He) Fy Fx

/-! ### Sums in the small (subnormal) regime are exact in FLT -/

/-- If `|x + y| ≤ β^(prec + emin)` and `x, y ∈ FLT`, then `x + y ∈ FLT`. -/
theorem FLT_format_plus_small (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    {x y : ℝ}
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Hxy : |x + y| ≤ bpow beta (prec + emin)) :
    generic_format beta (FLT_exp emin prec) (x + y) := by
  apply generic_format_FLT_FIX beta emin prec Hp
  · rw [show emin + prec = prec + emin from by ring]
    exact Hxy
  · -- x + y is in FIX(emin) since x and y are.
    obtain ⟨⟨nxm, nxe⟩, hx_eq, hxe⟩ :=
      FIX_format_generic beta emin (generic_format_FIX_FLT beta emin prec Fx)
    obtain ⟨⟨nym, nye⟩, hy_eq, hye⟩ :=
      FIX_format_generic beta emin (generic_format_FIX_FLT beta emin prec Fy)
    apply generic_format_FIX
    refine ⟨⟨nxm + nym, emin⟩, ?_, rfl⟩
    show x + y = ((nxm + nym : ℤ) : ℝ) * bpow beta emin
    rw [hx_eq, hy_eq]
    show (((nxm : ℝ) * bpow beta nxe) + ((nym : ℝ) * bpow beta nye))
        = ((nxm + nym : ℤ) : ℝ) * bpow beta emin
    have hxe' : nxe = emin := hxe
    have hye' : nye = emin := hye
    rw [hxe', hye']
    push_cast; ring

/-! ### Round of a nonzero sum is nonzero (under `Exp_not_FTZ`) -/

/-- Helper: when `0 < x + y` and `cexp x ≤ cexp y`, the rounded sum is nonzero. -/
theorem round_plus_neq_0_aux (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (h_NotFTZ : Exp_not_FTZ fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (_He : cexp beta fexp x ≤ cexp beta fexp y)
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hxy : 0 < x + y) :
    round beta fexp rnd (x + y) ≠ 0 := by
  have h_xy_ne : x + y ≠ 0 := ne_of_gt Hxy
  have h_low : bpow beta (mag beta (x + y) - 1) ≤ |x + y| := bpow_mag_le beta h_xy_ne
  set exy := mag beta (x + y) with hexy_def
  by_cases He' : exy ≤ fexp exy
  · -- Subnormal regime: x + y is exactly representable at exponent fexp exy.
    have h_x_eq : x = F2R (beta := beta) ⟨Ztrunc (x * bpow beta (-fexp exy)), fexp exy⟩ :=
      subnormal_exponent beta fexp hValid h_NotFTZ exy He' Fx
    have h_y_eq : y = F2R (beta := beta) ⟨Ztrunc (y * bpow beta (-fexp exy)), fexp exy⟩ :=
      subnormal_exponent beta fexp hValid h_NotFTZ exy He' Fy
    have h_sum :
        x + y = F2R (beta := beta)
          ⟨Ztrunc (x * bpow beta (-fexp exy))
            + Ztrunc (y * bpow beta (-fexp exy)), fexp exy⟩ := by
      conv_lhs => rw [h_x_eq, h_y_eq]
      rw [← F2R_plus, Fplus_same_exp]
    have h_F : generic_format beta fexp (x + y) := by
      rw [h_sum]
      apply generic_format_F2R beta fexp _ (fexp exy)
      intro _
      show cexp beta fexp _ ≤ fexp exy
      rw [← h_sum]
      show fexp (mag beta (x + y)) ≤ fexp exy
      rfl
    rw [round_generic beta fexp rnd h_F]
    exact h_xy_ne
  · -- Normal regime: bpow(exy - 1) ≤ |x + y|, and bpow(exy - 1) ∈ F.
    push_neg at He'
    intro Hround
    have h_pos : 0 < bpow beta (exy - 1) := bpow_gt_0 _ _
    have h_F_bpow : generic_format beta fexp (bpow beta (exy - 1)) := by
      apply generic_format_bpow beta fexp
      have : exy - 1 + 1 = exy := by ring
      rw [this]; omega
    have h_round_eq : round beta fexp rnd (bpow beta (exy - 1))
                    = bpow beta (exy - 1) := round_generic beta fexp rnd h_F_bpow
    have h_xy_pos_le : bpow beta (exy - 1) ≤ x + y := by
      rw [show x + y = |x + y| from (abs_of_pos Hxy).symm]; exact h_low
    have h_round_le : round beta fexp rnd (bpow beta (exy - 1))
                    ≤ round beta fexp rnd (x + y) :=
      round_le beta fexp hValid rnd h_xy_pos_le
    rw [h_round_eq, Hround] at h_round_le
    linarith

/-- The round of a nonzero sum is nonzero, under `Exp_not_FTZ`. -/
theorem round_plus_neq_0 (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (h_NotFTZ : Exp_not_FTZ fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hxy : x + y ≠ 0) :
    round beta fexp rnd (x + y) ≠ 0 := by
  rcases lt_or_gt_of_ne Hxy with H1 | H1
  · -- x + y < 0: reduce to negation.
    have h_neg_pos : 0 < -x + -y := by linarith
    have hround_eq : round beta fexp rnd (x + y)
                  = -(round beta fexp (Zrnd_opp rnd) (-x + -y)) := by
      have hr := round_opp beta fexp rnd (-x + -y)
      rw [show -(-x + -y) = x + y from by ring] at hr
      exact hr
    rw [hround_eq]
    have h_neg_ne : (round beta fexp (Zrnd_opp rnd) (-x + -y)) ≠ 0 := by
      rcases le_or_gt (cexp beta fexp (-x)) (cexp beta fexp (-y)) with H2 | H2
      · exact round_plus_neq_0_aux beta fexp hValid h_NotFTZ (Zrnd_opp rnd) H2
              (generic_format_opp beta fexp Fx) (generic_format_opp beta fexp Fy) h_neg_pos
      · rw [add_comm]
        exact round_plus_neq_0_aux beta fexp hValid h_NotFTZ (Zrnd_opp rnd) (le_of_lt H2)
              (generic_format_opp beta fexp Fy) (generic_format_opp beta fexp Fx)
              (by linarith)
    exact fun h => h_neg_ne (neg_eq_zero.mp h)
  · -- x + y > 0.
    rcases le_or_gt (cexp beta fexp x) (cexp beta fexp y) with H2 | H2
    · exact round_plus_neq_0_aux beta fexp hValid h_NotFTZ rnd H2 Fx Fy H1
    · rw [add_comm]
      exact round_plus_neq_0_aux beta fexp hValid h_NotFTZ rnd (le_of_lt H2) Fy Fx
            (by linarith)

/-- If the rounded sum is zero, then the sum itself is zero. -/
theorem round_plus_eq_0 (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (h_NotFTZ : Exp_not_FTZ fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (H : round beta fexp rnd (x + y) = 0) :
    x + y = 0 := by
  by_contra Hne
  exact round_plus_neq_0 beta fexp hValid h_NotFTZ rnd Fx Fy Hne H

end LeanFlocq
