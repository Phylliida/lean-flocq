/-
Lean port of Coq Flocq's `Prop/Mult_error.v` — error of multiplication
in FLX/FLT formats.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FLX
import LeanFlocq.Core.FLT
import LeanFlocq.Core.Ulp
import LeanFlocq.Calc.Operations

namespace LeanFlocq

/-! ### FLX section -/

/-- Auxiliary: when `round(x*y) ≠ x*y`, the error has a representation
with exponent `cexp x + cexp y`. -/
theorem mult_error_FLX_aux (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y)
    (Hz : round beta (FLX_exp prec) rnd (x * y) - x * y ≠ 0) :
    ∃ f : float beta,
      F2R f = round beta (FLX_exp prec) rnd (x * y) - x * y ∧
      cexp beta (FLX_exp prec) (F2R f) ≤ f.Fexp ∧
      f.Fexp = cexp beta (FLX_exp prec) x + cexp beta (FLX_exp prec) y := by
  have Hxy0 : x * y ≠ 0 := by
    intro hxy
    apply Hz
    rw [hxy, round_0]; ring
  have Hx0 : x ≠ 0 := fun h => Hxy0 (by rw [h, zero_mul])
  have Hy0 : y ≠ 0 := fun h => Hxy0 (by rw [h, mul_zero])
  -- Set up canonical representations.
  set mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hmx_def
  set my := Ztrunc (scaled_mantissa beta (FLX_exp prec) y) with hmy_def
  set ex := mag beta x with hex_def
  set ey := mag beta y with hey_def
  set exy := mag beta (x * y) with hexy_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set cy := cexp beta (FLX_exp prec) y with hcy_def
  set cxy := cexp beta (FLX_exp prec) (x * y) with hcxy_def
  -- Bounds on |x|, |y|, |xy|.
  have Hex_low : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta Hx0
  have Hex_high : |x| < bpow beta ex := bpow_mag_gt beta x
  have Hey_low : bpow beta (ey - 1) ≤ |y| := bpow_mag_le beta Hy0
  have Hey_high : |y| < bpow beta ey := bpow_mag_gt beta y
  have Hexy_low : bpow beta (exy - 1) ≤ |x * y| := bpow_mag_le beta Hxy0
  have Hexy_high : |x * y| < bpow beta exy := bpow_mag_gt beta (x * y)
  -- Hc1: cxy - prec ≤ cx + cy. From mag(xy) ≤ ex + ey.
  have h_exy_le : exy ≤ ex + ey := by
    have h_lt : bpow beta (exy - 1) < bpow beta (ex + ey) := by
      apply lt_of_le_of_lt Hexy_low
      rw [abs_mul, bpow_plus]
      exact mul_lt_mul'' Hex_high Hey_high (abs_nonneg _) (abs_nonneg _)
    have := lt_bpow beta h_lt; omega
  -- Express cx, cy, cxy as ex - prec, ey - prec, exy - prec.
  have hcx_eq : cx = ex - prec := by
    show cexp beta (FLX_exp prec) x = mag beta x - prec
    unfold cexp FLX_exp; rfl
  have hcy_eq : cy = ey - prec := by
    show cexp beta (FLX_exp prec) y = mag beta y - prec
    unfold cexp FLX_exp; rfl
  have hcxy_eq : cxy = exy - prec := by
    show cexp beta (FLX_exp prec) (x * y) = mag beta (x * y) - prec
    unfold cexp FLX_exp; rfl
  have Hc1 : cxy - prec ≤ cx + cy := by omega
  -- Hc2: cx + cy ≤ cxy. From (ex - 1) + (ey - 1) < exy.
  have h_exy_ge : ex + ey - 1 ≤ exy := by
    have : bpow beta (ex - 1 + (ey - 1)) ≤ |x * y| := by
      rw [abs_mul, bpow_plus]
      exact mul_le_mul Hex_low Hey_low (bpow_ge_0 _ _) (abs_nonneg _)
    have hh : bpow beta (ex - 1 + (ey - 1)) < bpow beta exy := lt_of_le_of_lt this Hexy_high
    have := lt_bpow beta hh; omega
  have Hc2 : cx + cy ≤ cxy := by omega
  -- Construct the float: m = -(mx * my) + rnd(scaled_mantissa(xy)) * beta^(cxy - (cx + cy))
  set rxy := rnd (scaled_mantissa beta (FLX_exp prec) (x * y)) with hrxy_def
  let m : ℤ := -(mx * my) + rxy * (beta.val : ℤ) ^ (cxy - (cx + cy)).toNat
  refine ⟨⟨m, cx + cy⟩, ?_, ?_, ?_⟩
  · -- F2R ⟨m, cx + cy⟩ = round(x*y) - x*y.
    show ((m : ℝ) * bpow beta (cx + cy))
        = round beta (FLX_exp prec) rnd (x * y) - x * y
    show ((-(mx * my) + rxy * (beta.val : ℤ) ^ (cxy - (cx + cy)).toNat : ℤ) : ℝ)
          * bpow beta (cx + cy)
        = round beta (FLX_exp prec) rnd (x * y) - x * y
    -- round(xy) = rxy * bpow(cxy), x*y = mx * bpow(cx) * (my * bpow(cy)) = mx*my * bpow(cx+cy)
    have hxy_F2R : x * y = ((mx * my : ℤ) : ℝ) * bpow beta (cx + cy) := by
      have hx : x = (mx : ℝ) * bpow beta cx := Fx
      have hy : y = (my : ℝ) * bpow beta cy := Fy
      rw [hx, hy, bpow_plus]
      push_cast; ring
    have hround : round beta (FLX_exp prec) rnd (x * y)
                  = (rxy : ℝ) * bpow beta cxy := rfl
    rw [hround, hxy_F2R]
    have h_diff_nn : 0 ≤ cxy - (cx + cy) := by linarith
    rw [show ((-(mx * my) + rxy * (beta.val : ℤ) ^ (cxy - (cx + cy)).toNat : ℤ) : ℝ)
        = -((mx * my : ℤ) : ℝ) + (rxy : ℝ)
            * ((((beta.val : ℤ) ^ (cxy - (cx + cy)).toNat : ℤ) : ℝ)) from by push_cast; ring]
    rw [IZR_Zpower beta h_diff_nn]
    have h_split : bpow beta cxy = bpow beta (cxy - (cx + cy)) * bpow beta (cx + cy) := by
      rw [← bpow_plus]; congr 1; omega
    rw [h_split]; ring
  · -- cexp(F2R f) ≤ f.Fexp = cx + cy.
    -- |error| < ulp(xy) = bpow(cxy), so mag(error) ≤ cxy. Then cexp(error) = mag(error) - prec
    -- ≤ cxy - prec ≤ cx + cy.
    have h_err_lt : |round beta (FLX_exp prec) rnd (x * y) - x * y|
                    < bpow beta cxy := by
      have h := error_lt_ulp beta (FLX_exp prec) (FLX_exp_valid prec Hp) rnd Hxy0
      rwa [ulp_neq_0 beta (FLX_exp prec) Hxy0] at h
    have h_mag : mag beta (round beta (FLX_exp prec) rnd (x * y) - x * y) ≤ cxy :=
      mag_le_bpow beta Hz h_err_lt
    have h_F2R_eq : F2R (beta := beta) ⟨m, cx + cy⟩
        = round beta (FLX_exp prec) rnd (x * y) - x * y := by
      -- Same expression as in the previous goal.
      show ((m : ℝ) * bpow beta (cx + cy))
          = round beta (FLX_exp prec) rnd (x * y) - x * y
      have hxy_F2R : x * y = ((mx * my : ℤ) : ℝ) * bpow beta (cx + cy) := by
        have hx : x = (mx : ℝ) * bpow beta cx := Fx
        have hy : y = (my : ℝ) * bpow beta cy := Fy
        rw [hx, hy, bpow_plus]; push_cast; ring
      have hround : round beta (FLX_exp prec) rnd (x * y)
                    = (rxy : ℝ) * bpow beta cxy := rfl
      rw [hround, hxy_F2R]
      have h_diff_nn : 0 ≤ cxy - (cx + cy) := by linarith
      rw [show ((-(mx * my) + rxy * (beta.val : ℤ) ^ (cxy - (cx + cy)).toNat : ℤ) : ℝ)
          = -((mx * my : ℤ) : ℝ) + (rxy : ℝ)
              * ((((beta.val : ℤ) ^ (cxy - (cx + cy)).toNat : ℤ) : ℝ)) from by
              push_cast; ring]
      rw [IZR_Zpower beta h_diff_nn]
      have h_split : bpow beta cxy = bpow beta (cxy - (cx + cy)) * bpow beta (cx + cy) := by
        rw [← bpow_plus]; congr 1; omega
      rw [h_split]; ring
    show cexp beta (FLX_exp prec) (F2R (beta := beta) ⟨m, cx + cy⟩) ≤ cx + cy
    rw [h_F2R_eq]
    have h_cexp_eq : cexp beta (FLX_exp prec)
        (round beta (FLX_exp prec) rnd (x * y) - x * y)
          = mag beta (round beta (FLX_exp prec) rnd (x * y) - x * y) - prec := by
      unfold cexp FLX_exp; rfl
    linarith [h_mag, hcx_eq, hcy_eq, hcxy_eq, h_cexp_eq, h_exy_le]
  · rfl

/-- The error of FLX multiplication is exactly representable. -/
theorem mult_error_FLX (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y) :
    generic_format beta (FLX_exp prec) (round beta (FLX_exp prec) rnd (x * y) - x * y) := by
  by_cases Hr0 : round beta (FLX_exp prec) rnd (x * y) - x * y = 0
  · rw [Hr0]; exact generic_format_0 _ _
  obtain ⟨f, h1, h2, _⟩ := mult_error_FLX_aux beta prec Hp rnd Fx Fy Hr0
  rw [← h1]
  obtain ⟨m, e⟩ := f
  exact generic_format_F2R beta (FLX_exp prec) m e (fun _ => h2)

/-- Multiplying an FLX value by `bpow e` keeps it in FLX. -/
theorem mult_bpow_exact_FLX (beta : radix) (prec : ℤ)
    {x : ℝ} (e : ℤ) (Fx : generic_format beta (FLX_exp prec) x) :
    generic_format beta (FLX_exp prec) (x * bpow beta e) := by
  by_cases Zx : x = 0
  · rw [Zx, zero_mul]; exact generic_format_0 _ _
  set mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hmx_def
  set ex := cexp beta (FLX_exp prec) x with hex_def
  refine generic_format_F2R' beta (FLX_exp prec)
    (⟨mx, ex + e⟩ : float beta) ?_ ?_
  · show (mx : ℝ) * bpow beta (ex + e) = x * bpow beta e
    rw [bpow_plus]
    have hx : x = (mx : ℝ) * bpow beta ex := Fx
    rw [show (mx : ℝ) * (bpow beta ex * bpow beta e)
        = ((mx : ℝ) * bpow beta ex) * bpow beta e from by ring, ← hx]
  · intro _
    show cexp beta (FLX_exp prec) (x * bpow beta e) ≤ ex + e
    unfold cexp
    rw [mag_mult_bpow beta Zx]
    show FLX_exp prec (mag beta x + e) ≤ ex + e
    have hex : ex = mag beta x - prec := by
      show cexp beta (FLX_exp prec) x = _
      unfold cexp FLX_exp; rfl
    unfold FLX_exp; omega

/-! ### FLT section -/

/-- The error of FLT multiplication is exactly representable, given that
the underflow threshold is far enough below `|x*y|`. -/
theorem mult_error_FLT (beta : radix) (emin prec : ℤ) (Hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    {x y : ℝ}
    (Fx : generic_format beta (FLT_exp emin prec) x)
    (Fy : generic_format beta (FLT_exp emin prec) y)
    (Hxy : x * y ≠ 0 → bpow beta (emin + 2 * prec - 1) ≤ |x * y|) :
    generic_format beta (FLT_exp emin prec)
      (round beta (FLT_exp emin prec) rnd (x * y) - x * y) := by
  by_cases Hr0 : round beta (FLT_exp emin prec) rnd (x * y) - x * y = 0
  · rw [Hr0]; exact generic_format_0 _ _
  by_cases Hxy' : x * y = 0
  · exfalso; apply Hr0
    rw [Hxy', round_0]; ring
  -- xy is in the FLX-equivalent regime.
  have Hxy_bound : bpow beta (emin + 2 * prec - 1) ≤ |x * y| := Hxy Hxy'
  have h_thresh : bpow beta (emin + prec - 1) ≤ |x * y| := by
    refine le_trans (bpow_le beta (by omega)) Hxy_bound
  have Fx' : generic_format beta (FLX_exp prec) x :=
    generic_format_FLX_FLT beta emin prec Fx
  have Fy' : generic_format beta (FLX_exp prec) y :=
    generic_format_FLX_FLT beta emin prec Fy
  -- Switch round-FLT to round-FLX for xy.
  rw [round_FLT_FLX beta emin prec rnd h_thresh] at *
  set rxy := round beta (FLX_exp prec) rnd (x * y) with hrxy_def
  -- Apply the FLX aux to get a representation.
  obtain ⟨⟨m, e⟩, h1, h2, h3⟩ := mult_error_FLX_aux beta prec Hp rnd Fx' Fy' Hr0
  rw [← h1]
  apply generic_format_F2R beta (FLT_exp emin prec) m e
  intro _
  -- cexp_FLT(F2R f) ≤ e. cexp_FLT = max(cexp_FLX, emin).
  show cexp beta (FLT_exp emin prec) (F2R (beta := beta) ⟨m, e⟩) ≤ e
  unfold cexp FLT_exp
  refine max_le ?_ ?_
  · -- cexp_FLX(F2R f) ≤ e from h2.
    show mag beta (F2R (beta := beta) ⟨m, e⟩) - prec ≤ e
    have h2' : cexp beta (FLX_exp prec) (F2R (beta := beta) ⟨m, e⟩) ≤ e := h2
    show mag beta (F2R (beta := beta) ⟨m, e⟩) - prec ≤ e
    have : cexp beta (FLX_exp prec) (F2R (beta := beta) ⟨m, e⟩)
        = mag beta (F2R (beta := beta) ⟨m, e⟩) - prec := by
      unfold cexp FLX_exp; rfl
    linarith
  · -- emin ≤ e. e = cexp_FLX x + cexp_FLX y. From bound on |x*y|.
    have Hx0 : x ≠ 0 := fun h => Hxy' (by rw [h, zero_mul])
    have Hy0 : y ≠ 0 := fun h => Hxy' (by rw [h, mul_zero])
    -- |xy| < bpow(mag x) * bpow(mag y) = bpow(mag x + mag y)
    -- and bpow(emin + 2prec - 1) ≤ |xy|, so emin + 2prec - 1 < mag x + mag y
    have h_xy_high : |x * y| < bpow beta (mag beta x + mag beta y) := by
      rw [abs_mul, bpow_plus]
      exact mul_lt_mul'' (bpow_mag_gt beta x) (bpow_mag_gt beta y)
        (abs_nonneg _) (abs_nonneg _)
    have h_emin_lt : emin + 2 * prec - 1 < mag beta x + mag beta y :=
      lt_bpow beta (lt_of_le_of_lt Hxy_bound h_xy_high)
    have h3' : e = cexp beta (FLX_exp prec) x + cexp beta (FLX_exp prec) y := h3
    show emin ≤ e
    rw [h3']
    show emin ≤ cexp beta (FLX_exp prec) x + cexp beta (FLX_exp prec) y
    unfold cexp FLX_exp; omega

/-- Lower bound on the absolute value of a nonzero `F2R`. -/
theorem F2R_ge (beta : radix) (y : float beta) (Hy : F2R y ≠ 0) :
    bpow beta y.Fexp ≤ |F2R y| := by
  obtain ⟨m, e⟩ := y
  have hm0 : m ≠ 0 := by
    intro h
    apply Hy
    show F2R (beta := beta) ⟨m, e⟩ = 0
    rw [h]; exact F2R_0 e
  show bpow beta e ≤ |F2R (beta := beta) ⟨m, e⟩|
  rw [show |F2R (beta := beta) ⟨m, e⟩| = F2R (beta := beta) ⟨|m|, e⟩ from
        (F2R_Zabs m e).symm]
  show bpow beta e ≤ ((|m| : ℤ) : ℝ) * bpow beta e
  have h_abs_pos : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
    have h_abs_int : 1 ≤ |m| := by
      rcases lt_trichotomy m 0 with hm | hm | hm
      · rw [abs_of_neg hm]; omega
      · exact absurd hm hm0
      · rw [abs_of_pos hm]; omega
    exact_mod_cast h_abs_int
  have h_pow_nn : 0 ≤ bpow beta e := bpow_ge_0 _ _
  nlinarith

/-- Multiplying an FLT value by a sufficiently-large `bpow e` keeps it in FLT. -/
theorem mult_bpow_exact_FLT (beta : radix) (emin prec : ℤ)
    {x : ℝ} (e : ℤ) (Fx : generic_format beta (FLT_exp emin prec) x)
    (He : emin + prec - mag beta x ≤ e) :
    generic_format beta (FLT_exp emin prec) (x * bpow beta e) := by
  by_cases Zx : x = 0
  · rw [Zx, zero_mul]; exact generic_format_0 _ _
  set mx := Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x) with hmx_def
  set ex := cexp beta (FLT_exp emin prec) x with hex_def
  refine generic_format_F2R' beta (FLT_exp emin prec)
    (⟨mx, ex + e⟩ : float beta) ?_ ?_
  · show (mx : ℝ) * bpow beta (ex + e) = x * bpow beta e
    rw [bpow_plus]
    have hx : x = (mx : ℝ) * bpow beta ex := Fx
    rw [show (mx : ℝ) * (bpow beta ex * bpow beta e)
        = ((mx : ℝ) * bpow beta ex) * bpow beta e from by ring, ← hx]
  · intro _
    show cexp beta (FLT_exp emin prec) (x * bpow beta e) ≤ ex + e
    unfold cexp
    rw [mag_mult_bpow beta Zx]
    show FLT_exp emin prec (mag beta x + e) ≤ ex + e
    have hex : ex = max (mag beta x - prec) emin := by
      show cexp beta (FLT_exp emin prec) x = _
      unfold cexp FLT_exp; rfl
    unfold FLT_exp
    rw [hex]
    -- Goal: max (mag x + e - prec) emin ≤ max (mag x - prec) emin + e
    rw [show max (mag beta x - prec) emin + e = max (mag beta x - prec + e) (emin + e) from by
        rcases le_total (mag beta x - prec) emin with h | h
        · rw [max_eq_right h, max_eq_right (by linarith)]
        · rw [max_eq_left h, max_eq_left (by linarith)]]
    refine max_le ?_ ?_
    · exact le_max_of_le_left (by omega)
    · exact le_max_of_le_left (by linarith)

end LeanFlocq
