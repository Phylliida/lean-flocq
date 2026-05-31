/-
# Error-free transformations at FLX (radix 2): Fast2Sum and TwoSum

The FLX (no-underflow) versions of the two addition EFTs, used by `ErrFMA`
where every building block must live at the same format as `TwoProduct`
(which is FLX). These are the original FLX developments (commits `a7d8eff`,
`cc7ad6c`), recovered here with `_FLX`-suffixed names so they coexist with the
gradual-underflow FLT versions in `Fast2Sum.lean` / `TwoSum.lean`.

Setting: radix 2, FLX format, round-to-nearest. The radix-2 assumption is used
because the proofs rely on `a/2 ∈ format`.

  Fast2Sum (|b| ≤ |a|):  s := round(a+b); z := round(s−a); e := round(b−z)
  TwoSum (no precond):   branch on |b| ≤ |a| into Fast2Sum on the larger side
Either way `a + b = s + e` exactly.
-/
import LeanFlocq.Core.FLX
import LeanFlocq.Prop.Sterbenz
import LeanFlocq.Prop.Mult_error
import LeanFlocq.Prop.Plus_error

namespace LeanFlocq

open radix (radix2)
open Classical

/-! ### Helper rewrites for `radix2` -/

private theorem radix2_val_cast : (radix2.val : ℝ) = 2 := by norm_cast

private theorem bpow_radix2_neg_one : bpow radix2 (-1) = 1 / 2 := by
  unfold bpow
  show ((radix2.val : ℝ) ^ (-1 : ℤ)) = 1 / 2
  rw [radix2_val_cast]; norm_num

private theorem div_two_eq_mul_bpow (a : ℝ) : a / 2 = a * bpow radix2 (-1) := by
  rw [bpow_radix2_neg_one]; ring

private theorem two_mul_eq_mul_bpow (a : ℝ) : 2 * a = a * bpow radix2 1 := by
  rw [bpow_one, radix2_val_cast]; ring

/-! ### Fast2Sum -/

/-- Step 1, positive case: under `0 < a` and `|b| ≤ a`, `round(a + b) − a ∈ F`. -/
private theorem Fast2Sum_FLX_step1_pos
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ} (Ha : 0 < a)
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ a) :
    generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by
  set s := round radix2 (FLX_exp prec) (Znearest choice) (a + b) with hs_def
  have hValid := FLX_exp_valid prec Hp
  have hMon := FLX_exp_monotone prec
  have hFa_half : generic_format radix2 (FLX_exp prec) (a / 2) := by
    rw [div_two_eq_mul_bpow]
    exact mult_bpow_exact_FLX radix2 prec (-1) Fa
  have hFa_two : generic_format radix2 (FLX_exp prec) (2 * a) := by
    rw [two_mul_eq_mul_bpow]
    exact mult_bpow_exact_FLX radix2 prec 1 Fa
  rcases lt_or_ge b (-(a / 2)) with Hcase2 | Hcase1
  · -- Case 2: b < −a/2. Then a + b ∈ F by Sterbenz on (a, −b).
    have h_b_neg : b < 0 := by linarith
    have h_b_abs : |b| = -b := abs_of_neg h_b_neg
    have h_neg_b_le_a : -b ≤ a := by rw [← h_b_abs]; exact Hab
    have h_ab_in_F : generic_format radix2 (FLX_exp prec) (a + b) := by
      have h_sub_eq : a - (-b) = a + b := by ring
      have h_sterbenz : generic_format radix2 (FLX_exp prec) (a - (-b)) :=
        sterbenz radix2 (FLX_exp prec) hValid hMon Fa
          (generic_format_opp radix2 (FLX_exp prec) Fb)
          ⟨by linarith, by linarith⟩
      rwa [h_sub_eq] at h_sterbenz
    have hs_eq : s = a + b := by
      rw [hs_def]
      exact round_generic radix2 (FLX_exp prec) (Znearest choice) h_ab_in_F
    rw [hs_eq, show a + b - a = b from by ring]
    exact Fb
  · -- Case 1: −a/2 ≤ b. Then a/2 ≤ s ≤ 2a, Sterbenz on (s, a).
    have h_lower : a / 2 ≤ a + b := by linarith
    have h_upper_b : b ≤ a := le_trans (le_abs_self b) Hab
    have h_upper : a + b ≤ 2 * a := by linarith
    have hs_lower : a / 2 ≤ s :=
      round_ge_generic radix2 (FLX_exp prec) hValid (Znearest choice) hFa_half h_lower
    have hs_upper : s ≤ 2 * a :=
      round_le_generic radix2 (FLX_exp prec) hValid (Znearest choice) hFa_two h_upper
    have h_s_format : generic_format radix2 (FLX_exp prec) s := by
      rw [hs_def]; exact generic_format_round _ _ hValid _ _
    exact sterbenz radix2 (FLX_exp prec) hValid hMon h_s_format Fa ⟨hs_lower, hs_upper⟩

/-- Step 1 (general): under `|b| ≤ |a|`, `round(a + b) − a ∈ F`. -/
theorem Fast2Sum_FLX_step1
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ |a|) :
    generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by
  rcases lt_trichotomy a 0 with Ha_neg | Ha_zero | Ha_pos
  · set choice' : ℤ → Bool := fun t => !choice (-(t + 1)) with hchoice'_def
    have Fa' : generic_format radix2 (FLX_exp prec) (-a) :=
      generic_format_opp radix2 (FLX_exp prec) Fa
    have Fb' : generic_format radix2 (FLX_exp prec) (-b) :=
      generic_format_opp radix2 (FLX_exp prec) Fb
    have Hab' : |-b| ≤ -a := by
      rw [abs_neg]
      have h : |a| = -a := abs_of_neg Ha_neg
      rw [← h]; exact Hab
    have h_pos := Fast2Sum_FLX_step1_pos prec Hp choice' (by linarith : (0 : ℝ) < -a) Fa' Fb' Hab'
    have h_sum_neg : -a + -b = -(a + b) := by ring
    rw [h_sum_neg] at h_pos
    have h_choice_double : (fun t : ℤ => !choice' (-(t + 1))) = choice := by
      funext t
      show (!choice' (-(t + 1))) = choice t
      rw [hchoice'_def]
      show (!(!choice (-(-(t + 1) + 1)))) = choice t
      simp
    rw [round_N_opp radix2 (FLX_exp prec) choice' (a + b), h_choice_double] at h_pos
    have h_eq : -round radix2 (FLX_exp prec) (Znearest choice) (a + b) - (-a)
              = -(round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by ring
    rw [h_eq] at h_pos
    have h_target := generic_format_opp radix2 (FLX_exp prec) h_pos
    rw [neg_neg] at h_target
    exact h_target
  · have h_b_zero : b = 0 := by
      have h_abs_b_nonneg : 0 ≤ |b| := abs_nonneg b
      have h_abs_b_zero : |b| = 0 := by
        rw [Ha_zero, abs_zero] at Hab
        linarith
      exact abs_eq_zero.mp h_abs_b_zero
    rw [Ha_zero, h_b_zero, add_zero, sub_zero,
      round_0 radix2 (FLX_exp prec) (Znearest choice)]
    exact generic_format_0 _ _
  · have hab_pos : |b| ≤ a := by rwa [abs_of_pos Ha_pos] at Hab
    exact Fast2Sum_FLX_step1_pos prec Hp choice Ha_pos Fa Fb hab_pos

/-- Step 2: `b − (round(a+b) − a) = (a+b) − round(a+b)`, the rounding error,
representable. -/
theorem Fast2Sum_FLX_step2
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b) :
    generic_format radix2 (FLX_exp prec)
      (b - (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a)) := by
  set s := round radix2 (FLX_exp prec) (Znearest choice) (a + b) with hs_def
  have h_rewrite : b - (s - a) = -(s - (a + b)) := by ring
  rw [h_rewrite]
  apply generic_format_opp
  rw [hs_def]
  exact plus_error radix2 (FLX_exp prec) (FLX_exp_valid prec Hp)
    (FLX_exp_monotone prec) choice Fa Fb

/-- **Fast2Sum correctness** (FLX). For `a, b ∈ F` with `|b| ≤ |a|`,
`s := round(a+b)`, `z := round(s−a)`, `e := round(b−z)` satisfy `z = s − a`,
`e = (a+b) − s`, and `a + b = s + e` exactly. -/
theorem Fast2Sum_FLX_correct
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ |a|) :
    let s := round radix2 (FLX_exp prec) (Znearest choice) (a + b)
    let z := round radix2 (FLX_exp prec) (Znearest choice) (s - a)
    let e := round radix2 (FLX_exp prec) (Znearest choice) (b - z)
    z = s - a ∧ e = (a + b) - s ∧ a + b = s + e := by
  intro s z e
  have h_step1 : generic_format radix2 (FLX_exp prec) (s - a) :=
    Fast2Sum_FLX_step1 prec Hp choice Fa Fb Hab
  have h_z : z = s - a :=
    round_generic radix2 (FLX_exp prec) (Znearest choice) h_step1
  have h_step2 : generic_format radix2 (FLX_exp prec) (b - (s - a)) :=
    Fast2Sum_FLX_step2 prec Hp choice Fa Fb
  have h_e : e = b - z := by
    show round radix2 (FLX_exp prec) (Znearest choice) (b - z) = b - z
    rw [h_z]
    exact round_generic radix2 (FLX_exp prec) (Znearest choice) h_step2
  refine ⟨h_z, ?_, ?_⟩
  · rw [h_e, h_z]; ring
  · rw [h_e, h_z]; ring

/-! ### TwoSum -/

/-- **TwoSum correctness** (FLX), no magnitude precondition. The sum
`s := round(a + b)` has exact error term computed by branching on `|b| ≤ |a|`. -/
theorem TwoSum_FLX_correct
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b) :
    let s := round radix2 (FLX_exp prec) (Znearest choice) (a + b)
    a + b = s +
      (if |b| ≤ |a|
       then round radix2 (FLX_exp prec) (Znearest choice)
              (b - round radix2 (FLX_exp prec) (Znearest choice) (s - a))
       else round radix2 (FLX_exp prec) (Znearest choice)
              (a - round radix2 (FLX_exp prec) (Znearest choice) (s - b))) := by
  intro s
  by_cases hab : |b| ≤ |a|
  · rw [if_pos hab]
    obtain ⟨_, _, h_sum⟩ := Fast2Sum_FLX_correct prec Hp choice Fa Fb hab
    exact h_sum
  · rw [if_neg hab]
    have hba : |a| ≤ |b| := le_of_not_ge hab
    obtain ⟨_, _, h_sum⟩ := Fast2Sum_FLX_correct prec Hp choice Fb Fa hba
    rw [add_comm b a] at h_sum
    exact h_sum

end LeanFlocq
