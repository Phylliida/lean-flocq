/-
Lean port of Coq Flocq's `Prop/Round_odd.v` — round-to-odd rounding mode.

Round-to-odd is the rounding mode where, for non-integers, the result is the
odd integer between ⌊x⌋ and ⌈x⌉. It is used to prove no-double-rounding
results: rounding through an intermediate format with round-to-odd, then to
the target with round-to-nearest-even, gives the same answer as rounding
directly with round-to-nearest-even (under a precision-gap condition).

Original Coq is © 2013–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.Round_NE
import LeanFlocq.Core.Ulp
import LeanFlocq.Calc.Operations

namespace LeanFlocq

open Classical in
/-- The round-to-odd integer rounding function.

If `x` is an integer, return it. Otherwise:
- If `⌊x⌋` is even, round up to `⌈x⌉` (which is `⌊x⌋ + 1`, hence odd).
- If `⌊x⌋` is odd, return `⌊x⌋`.

The result is always odd unless `x` itself is an integer. -/
noncomputable def Zrnd_odd (x : ℝ) : ℤ :=
  if x = (⌊x⌋ : ℝ) then ⌊x⌋
  else if Even ⌊x⌋ then ⌈x⌉ else ⌊x⌋

/-- When `x` is not an integer, `⌈x⌉ = ⌊x⌋ + 1`. -/
private theorem ceil_eq_floor_succ_of_ne {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    ⌈x⌉ = ⌊x⌋ + 1 := by
  have h_floor_le : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h_floor_lt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne h_floor_le (Ne.symm hx)
  have h_lt_succ : x < (⌊x⌋ + 1 : ℝ) := by
    have := Int.lt_floor_add_one x; push_cast; linarith
  -- ⌈x⌉ ≥ ⌊x⌋ + 1 (since x > ⌊x⌋ means ⌈x⌉ > ⌊x⌋, so ⌈x⌉ ≥ ⌊x⌋ + 1)
  have h_ceil_gt : ⌊x⌋ < ⌈x⌉ := by
    have h_floor_lt_ceil_cast : (⌊x⌋ : ℝ) < (⌈x⌉ : ℝ) :=
      lt_of_lt_of_le h_floor_lt (Int.le_ceil x)
    exact_mod_cast h_floor_lt_ceil_cast
  -- ⌈x⌉ ≤ ⌊x⌋ + 1 (since x < ⌊x⌋ + 1 = (⌊x⌋ + 1 : ℝ))
  have h_ceil_le : ⌈x⌉ ≤ ⌊x⌋ + 1 := by
    apply Int.ceil_le.mpr
    push_cast; linarith
  omega

/-- `Zrnd_odd` is a valid rounding function: monotone and identity on integers. -/
instance valid_rnd_odd : Valid_rnd Zrnd_odd where
  Zrnd_le := by
    intro x y Hxy
    have h_floor_le_rnd_y : ⌊x⌋ ≤ Zrnd_odd y := by
      have h_floor_mono : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_le_floor Hxy
      show ⌊x⌋ ≤ (if y = (⌊y⌋ : ℝ) then ⌊y⌋
                  else if Even ⌊y⌋ then ⌈y⌉ else ⌊y⌋)
      by_cases h_y_int : y = (⌊y⌋ : ℝ)
      · rw [if_pos h_y_int]; exact h_floor_mono
      · rw [if_neg h_y_int]
        by_cases h_even : Even ⌊y⌋
        · rw [if_pos h_even]
          have : ⌊y⌋ ≤ ⌈y⌉ := by
            have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
            have h2 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
            exact_mod_cast (le_trans h1 h2)
          linarith
        · rw [if_neg h_even]; exact h_floor_mono
    show (if x = (⌊x⌋ : ℝ) then ⌊x⌋ else if Even ⌊x⌋ then ⌈x⌉ else ⌊x⌋)
       ≤ Zrnd_odd y
    by_cases h_x_int : x = (⌊x⌋ : ℝ)
    · rw [if_pos h_x_int]; exact h_floor_le_rnd_y
    · rw [if_neg h_x_int]
      by_cases h_even_x : Even ⌊x⌋
      · rw [if_pos h_even_x]
        show ⌈x⌉ ≤ (if y = (⌊y⌋ : ℝ) then ⌊y⌋
                    else if Even ⌊y⌋ then ⌈y⌉ else ⌊y⌋)
        by_cases h_y_int : y = (⌊y⌋ : ℝ)
        · rw [if_pos h_y_int]
          apply Int.ceil_le.mpr
          rw [← h_y_int]; exact Hxy
        · rw [if_neg h_y_int]
          by_cases h_even_y : Even ⌊y⌋
          · rw [if_pos h_even_y]
            exact Int.ceil_le_ceil Hxy
          · rw [if_neg h_even_y]
            have h0 : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_le_floor Hxy
            rcases lt_or_eq_of_le h0 with h_lt | h_eq
            · have h_ceil_eq : ⌈x⌉ = ⌊x⌋ + 1 := ceil_eq_floor_succ_of_ne h_x_int
              omega
            · exfalso; rw [← h_eq] at h_even_y; exact h_even_y h_even_x
      · rw [if_neg h_even_x]; exact h_floor_le_rnd_y
  Zrnd_intCast := by
    intro n
    show (if (n : ℝ) = (⌊(n : ℝ)⌋ : ℝ) then ⌊(n : ℝ)⌋
          else if Even ⌊(n : ℝ)⌋ then ⌈(n : ℝ)⌉ else ⌊(n : ℝ)⌋) = n
    have h : (n : ℝ) = (⌊(n : ℝ)⌋ : ℝ) := by rw [Int.floor_intCast]
    rw [if_pos h, Int.floor_intCast]

/-- For non-integer `x`, `Zrnd_odd x` is odd. -/
theorem Zrnd_odd_Zodd {x : ℝ} (Hx : x ≠ (⌊x⌋ : ℝ)) : ¬ Even (Zrnd_odd x) := by
  show ¬ Even (if x = (⌊x⌋ : ℝ) then ⌊x⌋
               else if Even ⌊x⌋ then ⌈x⌉ else ⌊x⌋)
  rw [if_neg Hx]
  by_cases h_even : Even ⌊x⌋
  · rw [if_pos h_even]
    have h_ceil_eq : ⌈x⌉ = ⌊x⌋ + 1 := ceil_eq_floor_succ_of_ne Hx
    rw [h_ceil_eq]
    -- Even (⌊x⌋ + 1) ↔ ¬ Even ⌊x⌋. Since Even ⌊x⌋, ¬ Even (⌊x⌋ + 1).
    intro h_even_succ
    have h_odd_succ : Odd (⌊x⌋ + 1) := Even.add_one h_even
    rw [← Int.not_even_iff_odd] at h_odd_succ
    exact h_odd_succ h_even_succ
  · rw [if_neg h_even]; exact h_even

/-- `⌊n + y⌋ = n + ⌊y⌋` for integer `n`. -/
theorem Zfloor_plus (n : ℤ) (y : ℝ) : ⌊(n : ℝ) + y⌋ = n + ⌊y⌋ :=
  Int.floor_intCast_add n y

/-- `⌈n + y⌉ = n + ⌈y⌉` for integer `n`. -/
theorem Zceil_plus (n : ℤ) (y : ℝ) : ⌈(n : ℝ) + y⌉ = n + ⌈y⌉ := by
  rw [add_comm ((n : ℝ)) y, Int.ceil_add_intCast, add_comm ⌈y⌉ n]

/-- The natural-abs parity preserves the integer parity. -/
theorem Zeven_abs (z : ℤ) : Even z.natAbs ↔ Even z :=
  Int.natAbs_even

/-- When `x` is an integer with even floor, `Zrnd_odd (x + y) = x + Zrnd_odd y`. -/
theorem Zrnd_odd_plus {x y : ℝ} (Hx : x = (⌊x⌋ : ℝ)) (H : Even ⌊x⌋) :
    ((Zrnd_odd (x + y) : ℝ)) = x + (Zrnd_odd y : ℝ) := by
  unfold Zrnd_odd
  have h_floor_sum : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ := by
    nth_rewrite 1 [Hx]; exact Zfloor_plus _ y
  have h_even_sum : Even ⌊x + y⌋ ↔ Even ⌊y⌋ := by
    rw [h_floor_sum, Int.even_add]
    exact ⟨fun h => h.mp H, fun h => ⟨fun _ => h, fun _ => H⟩⟩
  by_cases h_y_int : y = (⌊y⌋ : ℝ)
  · -- y integer ⟹ x + y integer.
    have h_sum_int : x + y = (⌊x + y⌋ : ℝ) := by
      rw [h_floor_sum]
      push_cast
      rw [← Hx, ← h_y_int]
    rw [if_pos h_sum_int, if_pos h_y_int, h_floor_sum]
    push_cast
    rw [← Hx]
  · -- y not integer ⟹ x + y not integer.
    have h_sum_not_int : x + y ≠ (⌊x + y⌋ : ℝ) := by
      rw [h_floor_sum]
      push_cast
      rw [← Hx]
      intro h
      have : y = (⌊y⌋ : ℝ) := by linarith
      exact h_y_int this
    rw [if_neg h_sum_not_int, if_neg h_y_int]
    by_cases h_even_y : Even ⌊y⌋
    · have h_even_xy : Even ⌊x + y⌋ := h_even_sum.mpr h_even_y
      rw [if_pos h_even_xy, if_pos h_even_y]
      -- ⌈x + y⌉ = x + ⌈y⌉, since x integer.
      have h_ceil_sum : ⌈x + y⌉ = ⌊x⌋ + ⌈y⌉ := by
        nth_rewrite 1 [Hx]; exact Zceil_plus _ y
      rw [h_ceil_sum]
      push_cast; rw [← Hx]
    · have h_not_even_xy : ¬ Even ⌊x + y⌋ := fun h => h_even_y (h_even_sum.mp h)
      rw [if_neg h_not_even_xy, if_neg h_even_y, h_floor_sum]
      push_cast; rw [← Hx]

end LeanFlocq
