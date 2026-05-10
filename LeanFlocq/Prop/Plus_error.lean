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

/-! ### Trivial bounds from round-N -/

/-- Round-to-nearest error never exceeds `|x|`. -/
theorem plus_error_le_l (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (choice : ℤ → Bool)
    {x y : ℝ}
    (_Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y) :
    |round beta fexp (Znearest choice) (x + y) - (x + y)| ≤ |x| := by
  have h_dist : |round beta fexp (Znearest choice) (x + y) - (x + y)|
              ≤ |y - (x + y)| :=
    (round_N_pt beta fexp hValid choice (x + y)).2 y Fy
  rw [show y - (x + y) = -x from by ring, abs_neg] at h_dist
  exact h_dist

/-- Round-to-nearest error never exceeds `|y|`. -/
theorem plus_error_le_r (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (choice : ℤ → Bool)
    {x y : ℝ}
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y) :
    |round beta fexp (Znearest choice) (x + y) - (x + y)| ≤ |y| := by
  rw [add_comm]
  exact plus_error_le_l beta fexp hValid choice Fy Fx

/-! ### Helper lemmas for round_plus_F2R -/

/-- An F-format value can be expressed at any exponent at most its `cexp`. -/
theorem ex_shift (beta : radix) (fexp : ℤ → ℤ)
    {x : ℝ} (e : ℤ)
    (Fx : generic_format beta fexp x)
    (He : e ≤ cexp beta fexp x) :
    ∃ m : ℤ, x = (m : ℝ) * bpow beta e := by
  refine ⟨Ztrunc (scaled_mantissa beta fexp x)
        * (beta.val : ℤ) ^ (cexp beta fexp x - e).toNat, ?_⟩
  have h_diff_nn : 0 ≤ cexp beta fexp x - e := by linarith
  have h_x : x = (Ztrunc (scaled_mantissa beta fexp x) : ℝ)
              * bpow beta (cexp beta fexp x) := Fx
  conv_lhs => rw [h_x]
  rw [show ((Ztrunc (scaled_mantissa beta fexp x)
        * (beta.val : ℤ) ^ (cexp beta fexp x - e).toNat : ℤ) : ℝ)
      = (Ztrunc (scaled_mantissa beta fexp x) : ℝ)
        * (((beta.val : ℤ) ^ (cexp beta fexp x - e).toNat : ℤ) : ℝ) from by push_cast; ring]
  rw [IZR_Zpower beta h_diff_nn, mul_assoc, ← bpow_plus]
  have heq : cexp beta fexp x - e + e = cexp beta fexp x := by ring
  rw [heq]

/-- `mag(z) - 1 = mag(z / β)` for nonzero `z`. -/
theorem mag_minus1 (beta : radix) {z : ℝ} (Hz : z ≠ 0) :
    mag beta z - 1 = mag beta (z / (beta.val : ℝ)) := by
  -- z / β = z * β^(-1), so mag(z / β) = mag(z) + (-1) = mag(z) - 1.
  have h_eq : z / (beta.val : ℝ) = z * bpow beta (-1) := by
    rw [show bpow beta (-1) = ((beta.val : ℝ))⁻¹ from by
        unfold bpow; simp]
    rw [div_eq_mul_inv]
  rw [h_eq, mag_mult_bpow beta Hz]; ring

/-- `lt_mag`: if `0 < y` and `mag x < mag y`, then `x < y`. -/
theorem lt_mag (beta : radix) {x y : ℝ} (Py : 0 < y) (H : mag beta x < mag beta y) :
    x < y := by
  rcases le_or_gt x 0 with hx | hx
  · linarith
  · have hx_ne : x ≠ 0 := ne_of_gt hx
    have hy_ne : y ≠ 0 := ne_of_gt Py
    have h_x_lt : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
    have h_y_low : bpow beta (mag beta y - 1) ≤ |y| := bpow_mag_le beta hy_ne
    have h_pow_le : bpow beta (mag beta x) ≤ bpow beta (mag beta y - 1) :=
      bpow_le beta (by omega)
    rw [abs_of_pos hx] at h_x_lt
    rw [abs_of_pos Py] at h_y_low
    linarith

/-- `mag_minus_lb`: if `0 < x`, `0 < y`, and `mag y ≤ mag x - 2`, then
`mag x - 1 ≤ mag(x - y)`. -/
theorem mag_minus_lb (beta : radix) {x y : ℝ}
    (Px : 0 < x) (Py : 0 < y) (Hln : mag beta y ≤ mag beta x - 2) :
    mag beta x - 1 ≤ mag beta (x - y) := by
  have Hbeta : 2 ≤ beta.val := beta.prop
  have hx_ne : x ≠ 0 := ne_of_gt Px
  have hy_ne : y ≠ 0 := ne_of_gt Py
  -- bpow(mag x - 1) ≤ |x| = x.
  have h_x_low : bpow beta (mag beta x - 1) ≤ x := by
    have := bpow_mag_le beta hx_ne; rw [abs_of_pos Px] at this; exact this
  have h_y_high : y < bpow beta (mag beta y) := by
    have := bpow_mag_gt beta y; rw [abs_of_pos Py] at this; exact this
  -- bpow(mag x - 2) + bpow(mag x - 2) ≤ x: from bpow(mag x - 1) = β * bpow(mag x - 2)
  -- and 2 ≤ β.
  have h_step : bpow beta (mag beta x - 2) + bpow beta (mag beta x - 2) ≤ x := by
    refine le_trans ?_ h_x_low
    have h_pow_split : bpow beta (mag beta x - 1)
                    = (beta.val : ℝ) * bpow beta (mag beta x - 2) := by
      rw [show (mag beta x - 1 : ℤ) = (mag beta x - 2) + 1 from by ring,
          bpow_plus, bpow_one]; ring
    rw [h_pow_split]
    have h_beta_real : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast Hbeta
    have h_pow_nn : 0 ≤ bpow beta (mag beta x - 2) := bpow_ge_0 _ _
    nlinarith
  -- y < bpow(mag x - 2): from y < bpow(mag y) and mag y ≤ mag x - 2.
  have h_y_lt : y < bpow beta (mag beta x - 2) := by
    refine lt_of_lt_of_le h_y_high ?_
    exact bpow_le beta Hln
  -- bpow(mag x - 2) ≤ x - y.
  have h_xy_lb : bpow beta (mag beta x - 2) ≤ x - y := by linarith
  -- From bpow(mag x - 2) ≤ |x - y|, get mag x - 1 ≤ mag(x - y).
  apply mag_ge_bpow
  rw [show (mag beta x - 1 - 1 : ℤ) = mag beta x - 2 from by ring]
  -- |x - y| ≥ bpow(mag x - 2). Note x - y > 0 since y < x (from lt_mag).
  have h_xy_pos : 0 < x - y := by
    have : y < x := lt_mag beta Px (by omega)
    linarith
  rw [abs_of_pos h_xy_pos]
  exact h_xy_lb

/-! ### round_plus_F2R: structure of the rounded sum -/

/-- For `x ≠ 0` and `x, y ∈ F`, the rounded sum `round(x + y)` has an
F2R-representation at exponent `cexp(x / β)`. -/
theorem round_plus_F2R (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y) (Zx : x ≠ 0) :
    ∃ m : ℤ, round beta fexp rnd (x + y)
      = F2R (beta := beta) ⟨m, cexp beta fexp (x / (beta.val : ℝ))⟩ := by
  set e := cexp beta fexp (x / (beta.val : ℝ)) with he_def
  rcases le_or_gt (mag beta (x / (beta.val : ℝ))) (mag beta y) with H1 | H1
  · -- Case 1: mag(x/β) ≤ mag(y).
    have h_e_le_x : e ≤ cexp beta fexp x := by
      show cexp beta fexp _ ≤ cexp beta fexp x
      unfold cexp; apply hMon
      rw [← mag_minus1 beta Zx]; omega
    have h_e_le_y : e ≤ cexp beta fexp y := by
      show cexp beta fexp _ ≤ cexp beta fexp y
      unfold cexp; exact hMon _ _ H1
    obtain ⟨nx, Hnx⟩ := ex_shift beta fexp e Fx h_e_le_x
    obtain ⟨ny, Hny⟩ := ex_shift beta fexp e Fy h_e_le_y
    obtain ⟨n, Hn⟩ := round_repr_same_exp beta fexp rnd (nx + ny) e
    refine ⟨n, ?_⟩
    rw [show x + y = F2R (beta := beta) ⟨nx + ny, e⟩ from by
        rw [Hnx, Hny]
        show (nx : ℝ) * bpow beta e + (ny : ℝ) * bpow beta e
            = ((nx + ny : ℤ) : ℝ) * bpow beta e
        push_cast; ring]
    exact Hn
  · -- Case 2: mag(y) < mag(x/β) = mag(x) - 1, so mag(y) ≤ mag(x) - 2.
    have h_mag_minus1_eq : mag beta (x / (beta.val : ℝ)) = mag beta x - 1 :=
      (mag_minus1 beta Zx).symm
    have H1' : mag beta y ≤ mag beta x - 2 := by rw [h_mag_minus1_eq] at H1; omega
    -- x + y ≠ 0: if y = -x, mag y = mag x, contradicting H1'.
    have hxy_ne : x + y ≠ 0 := by
      intro h
      have h_y_neg_x : y = -x := by linarith
      have : mag beta y = mag beta x := by rw [h_y_neg_x]; exact mag_opp beta x
      omega
    have h_round_ne : round beta fexp rnd (x + y) ≠ 0 :=
      round_plus_neq_0 beta fexp hValid (monotone_exp_not_FTZ hValid hMon) rnd Fx Fy hxy_ne
    -- mag x - 1 ≤ mag (x + y).
    have h_mag_xy : mag beta x - 1 ≤ mag beta (x + y) := by
      apply mag_ge_bpow
      rw [show (mag beta x - 1 - 1 : ℤ) = mag beta x - 2 from by ring]
      have h_x_low : bpow beta (mag beta x - 1) ≤ |x| := bpow_mag_le beta Zx
      have h_y_high : |y| < bpow beta (mag beta x - 2) := by
        by_cases hy : y = 0
        · rw [hy, abs_zero]; exact bpow_gt_0 _ _
        · have h1 : |y| < bpow beta (mag beta y) := bpow_mag_gt beta y
          have h2 : bpow beta (mag beta y) ≤ bpow beta (mag beta x - 2) :=
            bpow_le beta H1'
          linarith
      have h_pow_split : bpow beta (mag beta x - 1)
                      = (beta.val : ℝ) * bpow beta (mag beta x - 2) := by
        rw [show (mag beta x - 1 : ℤ) = (mag beta x - 2) + 1 from by ring,
            bpow_plus, bpow_one]; ring
      have h_beta_real : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
      have h_pow_nn : 0 ≤ bpow beta (mag beta x - 2) := bpow_ge_0 _ _
      -- |x| - |y| ≥ bpow(mag x - 2).
      have h_sub : bpow beta (mag beta x - 2) ≤ |x| - |y| := by
        have h_2pow : 2 * bpow beta (mag beta x - 2)
                    ≤ bpow beta (mag beta x - 1) := by
          rw [h_pow_split]; nlinarith
        linarith
      -- |x + y| ≥ | |x| - |y| | ≥ |x| - |y|.
      have h_abs : |x| - |y| ≤ |x + y| := by
        have h_rev := abs_sub_abs_le_abs_sub x (-y)
        rw [show x - -y = x + y from by ring, abs_neg] at h_rev
        have h_self : |x| - |y| ≤ |(|x| - |y|)| := le_abs_self _
        linarith
      linarith
    -- e ≤ cexp (round (x + y)).
    have h_e_le_round : e ≤ cexp beta fexp (round beta fexp rnd (x + y)) := by
      refine le_trans ?_ (cexp_round_ge beta fexp hValid hMon rnd h_round_ne)
      show cexp beta fexp _ ≤ cexp beta fexp (x + y)
      unfold cexp; apply hMon
      rw [h_mag_minus1_eq]; exact h_mag_xy
    obtain ⟨n, Hn⟩ := ex_shift beta fexp e
                        (generic_format_round beta fexp hValid rnd (x + y))
                        h_e_le_round
    exact ⟨n, Hn⟩

/-! ### Round of x + y is at least one ulp -/

/-- Under `Exp_not_FTZ` (and Monotone), the rounded nonzero sum is at least
`ulp(x / β)`. -/
theorem round_plus_ge_ulp (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    (h_NotFTZ : Exp_not_FTZ fexp)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (KK : round beta fexp rnd (x + y) ≠ 0) :
    ulp beta fexp (x / (beta.val : ℝ)) ≤ |round beta fexp rnd (x + y)| := by
  by_cases Zx : x = 0
  · -- x = 0: round(0 + y) = y (since y ∈ F).
    rw [Zx, zero_add, round_generic beta fexp rnd Fy]
    rw [show (0 : ℝ) / (beta.val : ℝ) = 0 from by ring]
    have h_y_F : y = (Ztrunc (scaled_mantissa beta fexp y) : ℝ)
                  * bpow beta (cexp beta fexp y) := Fy
    by_cases Hm : Ztrunc (scaled_mantissa beta fexp y) = 0
    · -- y = 0 and round(0 + 0) = 0, contradicting KK.
      exfalso
      apply KK
      rw [Zx, zero_add, h_y_F, Hm]; push_cast; rw [zero_mul]; exact round_0 _ _ _
    · have hy_ne : y ≠ 0 := by
        rw [h_y_F]; intro h
        rcases mul_eq_zero.mp h with h1 | h1
        · apply Hm; exact_mod_cast h1
        · exact (bpow_ne_0 _ _) h1
      -- Chain: ulp 0 ≤ ulp y = bpow(cexp y) ≤ |my| * bpow(cexp y) = |y|.
      refine le_trans (ulp_ge_ulp_0 beta fexp hValid h_NotFTZ y) ?_
      rw [ulp_neq_0 beta fexp hy_ne]
      have h_y_abs : |y| = (|Ztrunc (scaled_mantissa beta fexp y)| : ℝ)
                          * bpow beta (cexp beta fexp y) := by
        conv_lhs => rw [h_y_F]
        rw [abs_mul, abs_of_pos (bpow_gt_0 _ _)]
      rw [h_y_abs]
      have h_m_ge_1 : (1 : ℝ) ≤ (|Ztrunc (scaled_mantissa beta fexp y)| : ℝ) := by
        have : 1 ≤ |Ztrunc (scaled_mantissa beta fexp y)| := by
          rcases lt_trichotomy (Ztrunc (scaled_mantissa beta fexp y)) 0 with h | h | h
          · rw [abs_of_neg h]; omega
          · exact absurd h Hm
          · rw [abs_of_pos h]; exact h
        exact_mod_cast this
      have h_pow_nn : 0 ≤ bpow beta (cexp beta fexp y) := bpow_ge_0 _ _
      nlinarith
  · obtain ⟨m, Hm⟩ := round_plus_F2R beta fexp hValid hMon rnd Fx Fy Zx
    by_cases Zm : m = 0
    · exfalso; apply KK; rw [Hm, Zm]; exact F2R_0 _
    · rw [Hm]
      have h_div_ne : x / (beta.val : ℝ) ≠ 0 := by
        intro h
        apply Zx
        have hb_ne : (beta.val : ℝ) ≠ 0 := ne_of_gt (radix_pos beta)
        rw [div_eq_zero_iff] at h
        rcases h with h | h
        · exact h
        · exact absurd h hb_ne
      rw [ulp_neq_0 beta fexp h_div_ne]
      show bpow beta (cexp beta fexp (x / (beta.val : ℝ)))
          ≤ |F2R (beta := beta) ⟨m, cexp beta fexp (x / (beta.val : ℝ))⟩|
      have h_F2R_abs : |F2R (beta := beta) ⟨m, cexp beta fexp (x / (beta.val : ℝ))⟩|
                    = (|m| : ℝ) * bpow beta (cexp beta fexp (x / (beta.val : ℝ))) := by
        show |(m : ℝ) * bpow beta _| = |(m : ℝ)| * bpow beta _
        rw [abs_mul, abs_of_pos (bpow_gt_0 _ _)]
      rw [h_F2R_abs]
      have h_abs_m : (1 : ℝ) ≤ (|m| : ℝ) := by
        have : 1 ≤ |m| := by
          rcases lt_trichotomy m 0 with hm | hm | hm
          · rw [abs_of_neg hm]; omega
          · exact absurd hm Zm
          · rw [abs_of_pos hm]; exact hm
        exact_mod_cast this
      have h_pow_nn : 0 ≤ bpow beta (cexp beta fexp (x / (beta.val : ℝ))) := bpow_ge_0 _ _
      nlinarith

/-! ### `round_FLT_plus_ge` and friends -/

/-- In FLT, if `|x| ≥ β^(e + prec)` and the sum doesn't round to zero, then
the rounded sum has magnitude at least `β^e`. -/
theorem round_FLT_plus_ge (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ} (e : ℤ)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (He : bpow beta (e + prec) ≤ |x|)
    (KK : round beta (FLT_exp emin prec) rnd (x + y) ≠ 0) :
    bpow beta e ≤ |round beta (FLT_exp emin prec) rnd (x + y)| := by
  have Zx : x ≠ 0 := by
    intro hx; rw [hx, abs_zero] at He
    exact absurd He (not_le_of_gt (bpow_gt_0 _ _))
  have h_div_ne : x / (beta.val : ℝ) ≠ 0 := by
    intro h
    have hb_ne : (beta.val : ℝ) ≠ 0 := ne_of_gt (radix_pos beta)
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact Zx h
    · exact hb_ne h
  refine le_trans ?_ (round_plus_ge_ulp beta (FLT_exp emin prec)
                      (FLT_exp_valid emin prec Hp) (FLT_exp_monotone emin prec)
                      (monotone_exp_not_FTZ (FLT_exp_valid emin prec Hp)
                        (FLT_exp_monotone emin prec))
                      rnd Fx Fy KK)
  rw [ulp_neq_0 beta (FLT_exp emin prec) h_div_ne]
  show bpow beta e ≤ bpow beta (cexp beta (FLT_exp emin prec) (x / (beta.val : ℝ)))
  apply bpow_le
  unfold cexp
  rw [← mag_minus1 beta Zx]
  unfold FLT_exp
  have h_mag : e + prec < mag beta x :=
    lt_bpow beta (lt_of_le_of_lt He (bpow_mag_gt beta x))
  exact le_max_of_le_left (by omega)

/-- Generalization: if `x = 0` then `|y| ≥ β^e` is enough. -/
theorem round_FLT_plus_ge' (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ} (e : ℤ)
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (H1 : x ≠ 0 → bpow beta (e + prec) ≤ |x|)
    (H2 : x = 0 → y ≠ 0 → bpow beta e ≤ |y|)
    (H3 : round beta (FLT_exp emin prec) rnd (x + y) ≠ 0) :
    bpow beta e ≤ |round beta (FLT_exp emin prec) rnd (x + y)| := by
  by_cases H4 : x = 0
  · by_cases H5 : y = 0
    · exfalso; apply H3
      rw [H4, H5, add_zero, round_0]
    · rw [H4, zero_add, round_generic beta (FLT_exp emin prec) rnd Fy]
      exact H2 H4 H5
  · exact round_FLT_plus_ge beta emin prec Hp rnd e Fx Fy (H1 H4) H3

/-- The same statement for FLX. -/
theorem round_FLX_plus_ge (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ} (e : ℤ)
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y)
    (He : bpow beta (e + prec) ≤ |x|)
    (KK : round beta (FLX_exp prec) rnd (x + y) ≠ 0) :
    bpow beta e ≤ |round beta (FLX_exp prec) rnd (x + y)| := by
  have Zx : x ≠ 0 := by
    intro hx; rw [hx, abs_zero] at He
    exact absurd He (not_le_of_gt (bpow_gt_0 _ _))
  have h_div_ne : x / (beta.val : ℝ) ≠ 0 := by
    intro h
    have hb_ne : (beta.val : ℝ) ≠ 0 := ne_of_gt (radix_pos beta)
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact Zx h
    · exact hb_ne h
  refine le_trans ?_ (round_plus_ge_ulp beta (FLX_exp prec)
                      (FLX_exp_valid prec Hp) (FLX_exp_monotone prec)
                      (monotone_exp_not_FTZ (FLX_exp_valid prec Hp)
                        (FLX_exp_monotone prec))
                      rnd Fx Fy KK)
  rw [ulp_neq_0 beta (FLX_exp prec) h_div_ne]
  show bpow beta e ≤ bpow beta (cexp beta (FLX_exp prec) (x / (beta.val : ℝ)))
  apply bpow_le
  unfold cexp
  rw [← mag_minus1 beta Zx]
  unfold FLX_exp
  have h_mag : e + prec < mag beta x :=
    lt_bpow beta (lt_of_le_of_lt He (bpow_mag_gt beta x))
  omega

end LeanFlocq
