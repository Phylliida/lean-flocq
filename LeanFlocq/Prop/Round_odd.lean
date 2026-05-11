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

/-! ### Rnd_odd_pt predicate and basic properties -/

/-- `f` is the round-to-odd of `x` in the format. -/
def Rnd_odd_pt (beta : radix) (fexp : ℤ → ℤ) (x f : ℝ) : Prop :=
  generic_format beta fexp f ∧
  (f = x ∨
   ((Rnd_DN_pt (generic_format beta fexp) x f ∨
     Rnd_UP_pt (generic_format beta fexp) x f) ∧
    ∃ g : float beta, f = F2R g ∧ canonical beta fexp g ∧ ¬ Even g.Fnum))

/-- A rounding function `rnd : ℝ → ℝ` is round-to-odd. -/
def Rnd_odd (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, Rnd_odd_pt beta fexp x (rnd x)

/-- Negation symmetry: if `-f` is the round-to-odd of `-x`, then `f` is the
round-to-odd of `x`. -/
theorem Rnd_odd_pt_opp_inv (beta : radix) (fexp : ℤ → ℤ)
    {x f : ℝ} (h : Rnd_odd_pt beta fexp (-x) (-f)) :
    Rnd_odd_pt beta fexp x f := by
  obtain ⟨H1, H2⟩ := h
  refine ⟨?_, ?_⟩
  · -- f ∈ format from -f ∈ format.
    rw [show f = -(-f) from (neg_neg f).symm]
    exact generic_format_opp beta fexp H1
  · rcases H2 with h_eq | ⟨h_dn_up, g, hg1, hg2, hg3⟩
    · -- -f = -x ⟹ f = x.
      left
      rw [show f = -(-f) from (neg_neg f).symm, h_eq]; ring
    · -- DN/UP case.
      right
      refine ⟨?_, ?_⟩
      · rcases h_dn_up with h_dn | h_up
        · -- Rnd_DN_pt F (-x) (-f). Want Rnd_UP_pt F x f.
          -- Rnd_UP_pt_opp takes DN at (x', f') and gives UP at (-x', -f').
          -- With x' = -x, f' = -f: gives UP at (x, f). ✓
          have h := Rnd_UP_pt_opp (generic_format beta fexp)
            (fun y hy => generic_format_opp beta fexp hy) h_dn
          rw [neg_neg, neg_neg] at h
          right; exact h
        · -- Rnd_UP_pt F (-x) (-f). Want Rnd_DN_pt F x f.
          have h := Rnd_DN_pt_opp (generic_format beta fexp)
            (fun y hy => generic_format_opp beta fexp hy) h_up
          rw [neg_neg, neg_neg] at h
          left; exact h
      · -- canonical odd witness for f: negate g.
        refine ⟨⟨-g.Fnum, g.Fexp⟩, ?_, ?_, ?_⟩
        · -- f = F2R ⟨-g.Fnum, g.Fexp⟩ = -F2R g.
          show f = F2R (beta := beta) ⟨-g.Fnum, g.Fexp⟩
          rw [F2R_Zopp]
          rw [show f = -(-f) from (neg_neg f).symm, hg1]
        · -- canonical of negated float
          exact canonical_opp beta fexp g.Fnum g.Fexp hg2
        · -- ¬ Even (-g.Fnum)
          show ¬ Even (-g.Fnum)
          rwa [even_neg]

/-! ### Negation symmetry for the round_odd rounding -/

/-- `round (Zrnd_odd) (-x) = -round (Zrnd_odd) x`. -/
theorem round_odd_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    round beta fexp Zrnd_odd (-x) = -round beta fexp Zrnd_odd x := by
  unfold round
  rw [scaled_mantissa_opp, cexp_opp, ← F2R_Zopp]
  -- Show the two F2R expressions agree by matching mantissas.
  set r := scaled_mantissa beta fexp x with hr_def
  set ex := cexp beta fexp x with hex_def
  show F2R (beta := beta) ⟨Zrnd_odd (-r), ex⟩
     = F2R (beta := beta) ⟨-Zrnd_odd r, ex⟩
  congr 2
  show Zrnd_odd (-r) = -Zrnd_odd r
  unfold Zrnd_odd
  by_cases h_neg_r_int : -r = (⌊-r⌋ : ℝ)
  · -- -r is integer ⟹ r is integer.
    have h_r_int : r = (⌊r⌋ : ℝ) := by
      have h_neg_neg : -(-r) = -((⌊-r⌋ : ℝ)) := by rw [← h_neg_r_int]
      rw [neg_neg] at h_neg_neg
      rw [h_neg_neg, ← Int.cast_neg]
      congr 1
      -- ⌊r⌋ = -⌊-r⌋ when r is integer (and -r is integer).
      have : r = -((⌊-r⌋ : ℝ)) := h_neg_neg
      rw [this]
      rw [show (-((⌊-r⌋ : ℝ)) : ℝ) = ((-⌊-r⌋ : ℤ) : ℝ) from by push_cast; ring]
      rw [Int.floor_intCast]
    rw [if_pos h_neg_r_int, if_pos h_r_int]
    -- ⌊-r⌋ = -⌊r⌋ when r is integer. From -r = ⌊-r⌋ and r = ⌊r⌋: ⌊-r⌋ = -r = -⌊r⌋.
    have : (⌊-r⌋ : ℝ) = -(⌊r⌋ : ℝ) := by rw [← h_neg_r_int, ← h_r_int]
    exact_mod_cast this
  · -- -r is not integer ⟹ r is not integer.
    have h_r_not_int : r ≠ (⌊r⌋ : ℝ) := by
      intro h_r_int
      apply h_neg_r_int
      rw [h_r_int]
      rw [show -((⌊r⌋ : ℝ)) = ((-⌊r⌋ : ℤ) : ℝ) from by push_cast; ring]
      rw [Int.floor_intCast]
    rw [if_neg h_neg_r_int, if_neg h_r_not_int]
    -- For non-integer r: ⌊-r⌋ = -⌈r⌉ and ⌈-r⌉ = -⌊r⌋.
    have h_floor_neg : ⌊-r⌋ = -⌈r⌉ := Int.floor_neg
    have h_ceil_neg : ⌈-r⌉ = -⌊r⌋ := Int.ceil_neg
    have h_ceil_succ : ⌈r⌉ = ⌊r⌋ + 1 := ceil_eq_floor_succ_of_ne h_r_not_int
    -- Establish parity correspondence as an iff.
    have h_parity : Even ⌊-r⌋ ↔ ¬ Even ⌊r⌋ := by
      rw [h_floor_neg, even_neg, h_ceil_succ]
      constructor
      · intro h_e h_e2
        have h_odd : Odd (⌊r⌋ + 1) := Even.add_one h_e2
        exact (Int.not_even_iff_odd.mpr h_odd) h_e
      · intro h_ne
        have h_odd : Odd ⌊r⌋ := Int.not_even_iff_odd.mp h_ne
        obtain ⟨k, hk⟩ := h_odd
        refine ⟨k + 1, ?_⟩; omega
    by_cases h_even_r : Even ⌊r⌋
    · -- Even ⌊r⌋: ¬ Even ⌊-r⌋, take floor branch on LHS, ceil branch on RHS.
      have h_not_even_neg : ¬ Even ⌊-r⌋ := fun h => (h_parity.mp h) h_even_r
      rw [if_neg h_not_even_neg, if_pos h_even_r, h_floor_neg, h_ceil_succ]
    · -- ¬ Even ⌊r⌋: Even ⌊-r⌋, take ceil branch on LHS, floor branch on RHS.
      have h_even_neg : Even ⌊-r⌋ := h_parity.mpr h_even_r
      rw [if_pos h_even_neg, if_neg h_even_r, h_ceil_neg]

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
