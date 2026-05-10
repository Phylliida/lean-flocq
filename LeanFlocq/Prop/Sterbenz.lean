/-
Lean port of Coq Flocq's `Prop/Sterbenz.v` — conditions for exact subtraction.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Calc.Operations

namespace LeanFlocq

/-- If `x` and `y` are in the format and `|x + y|` does not exceed
`β^(min(mag x, mag y))`, then `x + y` is in the format. -/
theorem generic_format_plus (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    {x y : ℝ} (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hxy : |x + y| ≤ bpow beta (min (mag beta x) (mag beta y))) :
    generic_format beta fexp (x + y) := by
  by_cases Zxy : x + y = 0
  · rw [Zxy]; exact generic_format_0 beta fexp
  by_cases Zx : x = 0
  · rw [Zx, zero_add] at *; exact Fy
  by_cases Zy : y = 0
  · rw [Zy, add_zero] at *; exact Fx
  rcases lt_or_eq_of_le Hxy with Hxy_lt | Hxy_eq
  · -- Strict case: assemble the sum from F2R parts.
    set ex := mag beta x with hex_def
    set ey := mag beta y with hey_def
    set fx : float beta :=
      ⟨Ztrunc (scaled_mantissa beta fexp x), cexp beta fexp x⟩ with hfx
    set fy : float beta :=
      ⟨Ztrunc (scaled_mantissa beta fexp y), cexp beta fexp y⟩ with hfy
    have hx_eq : F2R fx = x := Fx.symm
    have hy_eq : F2R fy = y := Fy.symm
    have h_sum : F2R (Fplus fx fy) = x + y := by
      rw [F2R_plus, hx_eq, hy_eq]
    refine generic_format_F2R' beta fexp (Fplus fx fy) h_sum (fun _ => ?_)
    rw [Fexp_Fplus]
    show cexp beta fexp (x + y) ≤ min (cexp beta fexp x) (cexp beta fexp y)
    have h_min_eq : min (cexp beta fexp x) (cexp beta fexp y)
                  = fexp (min ex ey) := by
      unfold cexp
      rcases le_total ex ey with h | h
      · rw [min_eq_left h, min_eq_left (hMon _ _ h)]
      · rw [min_eq_right h, min_eq_right (hMon _ _ h)]
    rw [h_min_eq]
    unfold cexp
    exact hMon _ _ (mag_le_bpow beta Zxy Hxy_lt)
  · -- Equality case: x + y is ±β^(min ex ey).
    apply generic_format_abs_inv beta fexp
    rw [Hxy_eq]
    apply generic_format_bpow beta fexp
    set m := min (mag beta x) (mag beta y) with hm_def
    have h_lt : fexp m < m := by
      rcases le_total (mag beta x) (mag beta y) with h | h
      · rw [show m = mag beta x from min_eq_left h]
        exact mag_generic_gt beta fexp hValid Zx Fx
      · rw [show m = mag beta y from min_eq_right h]
        exact mag_generic_gt beta fexp hValid Zy Fy
    exact (hValid m).1 h_lt

/-- If `x` and `y` are in the format and `|x + y| ≤ min(|x|, |y|)`, then
`x + y` is in the format. -/
theorem generic_format_plus_weak (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    {x y : ℝ} (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hxy : |x + y| ≤ min |x| |y|) :
    generic_format beta fexp (x + y) := by
  by_cases Zx : x = 0
  · rw [Zx, zero_add]; exact Fy
  by_cases Zy : y = 0
  · rw [Zy, add_zero]; exact Fx
  apply generic_format_plus beta fexp hValid hMon Fx Fy
  refine le_trans Hxy ?_
  rcases le_or_gt |x| |y| with hxy | hxy
  · rw [min_eq_left hxy]
    rw [min_eq_left (mag_le_abs beta Zx hxy)]
    exact le_of_lt (bpow_mag_gt beta x)
  · rw [min_eq_right (le_of_lt hxy)]
    rw [min_eq_right (mag_le_abs beta Zy (le_of_lt hxy))]
    exact le_of_lt (bpow_mag_gt beta y)

/-- Helper: when `y ≤ x ≤ 2y`, `x - y` is in the format. -/
theorem sterbenz_aux (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    {x y : ℝ} (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hxy : y ≤ x ∧ x ≤ 2 * y) :
    generic_format beta fexp (x - y) := by
  obtain ⟨Hxy1, Hxy2⟩ := Hxy
  have Hy0 : 0 ≤ y := by linarith
  rw [show x - y = x + (-y) from by ring]
  apply generic_format_plus_weak beta fexp hValid hMon Fx (generic_format_opp beta fexp Fy)
  -- |x + (-y)| ≤ min |x| |-y|
  have h_xmy_nn : 0 ≤ x - y := by linarith
  have h_x_nn : 0 ≤ x := by linarith
  rw [show x + (-y) = x - y from by ring, abs_neg, abs_of_nonneg h_xmy_nn,
      abs_of_nonneg h_x_nn, abs_of_nonneg Hy0]
  rcases le_total y x with hyx | hyx
  · rw [min_eq_right hyx]; linarith
  · -- y ≤ x is given, so this branch is y = x.
    have heq : y = x := le_antisymm Hxy1 hyx
    rw [heq, min_eq_left (le_refl _)]; linarith

/-- The Sterbenz lemma: if `y/2 ≤ x ≤ 2y`, then `x - y` is exactly representable. -/
theorem sterbenz (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    {x y : ℝ} (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hxy : y / 2 ≤ x ∧ x ≤ 2 * y) :
    generic_format beta fexp (x - y) := by
  obtain ⟨Hxy1, Hxy2⟩ := Hxy
  rcases le_or_gt x y with Hxy_le | Hxy_gt
  · -- x ≤ y: rewrite x - y = -(y - x) and use sterbenz_aux on (y, x).
    rw [show x - y = -(y - x) from by ring]
    apply generic_format_opp
    apply sterbenz_aux beta fexp hValid hMon Fy Fx
    refine ⟨Hxy_le, ?_⟩
    -- Need y ≤ 2 * x. From y / 2 ≤ x: y ≤ 2x.
    linarith
  · -- y < x: use sterbenz_aux on (x, y).
    apply sterbenz_aux beta fexp hValid hMon Fx Fy ⟨le_of_lt Hxy_gt, Hxy2⟩

end LeanFlocq
