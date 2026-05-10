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

end LeanFlocq
