/-
Fast2Sum: the error-free transformation for floating-point addition under
the precondition |b| ≤ |a|.

Not part of Coq Flocq's main library — Flocq's version lives in the older
Pff theory (`Pff.v`'s Dekker_FTS). We prove it directly on top of Flocq's
Lean port, following the classical Boldo-Daumas-Muller structure.

Setting: radix 2, FLX format, round-to-nearest. The radix-2 assumption is
used because the proof relies on `a/2 ∈ format`.

The algorithm:
  s := round(a + b)
  z := round(s - a)   -- claim: z = s - a (exact)
  e := round(b - z)   -- claim: e = a + b - s (exact)
Then `a + b = s + e` exactly.
-/
import LeanFlocq.Core.FLX
import LeanFlocq.Prop.Sterbenz
import LeanFlocq.Prop.Mult_error
import LeanFlocq.Prop.Plus_error

namespace LeanFlocq

open radix (radix2)

/-! ### Helper rewrites for `radix2` -/

/-- `(radix2.val : ℝ) = 2`. -/
private theorem radix2_val_cast : (radix2.val : ℝ) = 2 := by norm_cast

/-- `bpow radix2 (-1) = 1/2`. -/
private theorem bpow_radix2_neg_one : bpow radix2 (-1) = 1 / 2 := by
  unfold bpow
  show ((radix2.val : ℝ) ^ (-1 : ℤ)) = 1 / 2
  rw [radix2_val_cast]; norm_num

/-- `a / 2 = a * bpow radix2 (-1)`. -/
private theorem div_two_eq_mul_bpow (a : ℝ) : a / 2 = a * bpow radix2 (-1) := by
  rw [bpow_radix2_neg_one]; ring

/-- `2 * a = a * bpow radix2 1`. -/
private theorem two_mul_eq_mul_bpow (a : ℝ) : 2 * a = a * bpow radix2 1 := by
  rw [bpow_one, radix2_val_cast]; ring

/-! ### The Sterbenz step (positive case) -/

/-- Step 1, positive case: under `0 < a` and `|b| ≤ a`, the second
subtraction in Fast2Sum is exact — `round(a + b) - a ∈ FLX_format`. -/
private theorem Fast2Sum_step1_pos
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
  -- a/2 ∈ format and 2a ∈ format (closure under multiplication by bpow).
  have hFa_half : generic_format radix2 (FLX_exp prec) (a / 2) := by
    rw [div_two_eq_mul_bpow]
    exact mult_bpow_exact_FLX radix2 prec (-1) Fa
  have hFa_two : generic_format radix2 (FLX_exp prec) (2 * a) := by
    rw [two_mul_eq_mul_bpow]
    exact mult_bpow_exact_FLX radix2 prec 1 Fa
  -- The two-case argument: either b is large-negative (|b| > a/2) or not.
  rcases lt_or_ge b (-(a/2)) with Hcase2 | Hcase1
  · -- Case 2: b < -a/2. Then a + b ∈ F by Sterbenz on (a, -b).
    have h_b_neg : b < 0 := by linarith
    have h_b_abs : |b| = -b := abs_of_neg h_b_neg
    have h_neg_b_le_a : -b ≤ a := by rw [← h_b_abs]; exact Hab
    -- Sterbenz needs (-b)/2 ≤ a ≤ 2(-b).
    have h_ab_in_F : generic_format radix2 (FLX_exp prec) (a + b) := by
      have h_sub_eq : a - (-b) = a + b := by ring
      have h_sterbenz : generic_format radix2 (FLX_exp prec) (a - (-b)) :=
        sterbenz radix2 (FLX_exp prec) hValid hMon Fa
          (generic_format_opp radix2 (FLX_exp prec) Fb)
          ⟨by linarith, by linarith⟩
      rwa [h_sub_eq] at h_sterbenz
    -- s = round(a + b) = a + b, so s - a = b ∈ F.
    have hs_eq : s = a + b := by
      rw [hs_def]
      exact round_generic radix2 (FLX_exp prec) (Znearest choice) h_ab_in_F
    rw [hs_eq, show a + b - a = b from by ring]
    exact Fb
  · -- Case 1: -a/2 ≤ b. Then a/2 ≤ a + b ≤ 2a, so a/2 ≤ s ≤ 2a, Sterbenz on (s, a).
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

/-- Step 1 (general): under `|b| ≤ |a|` in radix 2 FLX with round-to-nearest,
the difference `round(a + b) - a` is exactly representable. -/
theorem Fast2Sum_step1
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ |a|) :
    generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by
  rcases lt_trichotomy a 0 with Ha_neg | Ha_zero | Ha_pos
  · -- a < 0: use negation symmetry.
    -- Let a' := -a > 0 and b' := -b. Then |b'| ≤ a'.
    -- round(a + b) with Znearest choice = -round(-(a+b)) with flipped choice
    --                                   = -round(a' + b') with flipped choice
    -- So round(a + b) - a = -(round(a' + b') with flipped choice) - a
    --                     = -(round(a' + b') with flipped choice - a').
    -- Apply Fast2Sum_step1_pos to the negated picture, then use opp closure.
    set choice' : ℤ → Bool := fun t => !choice (-(t + 1)) with hchoice'_def
    have Fa' : generic_format radix2 (FLX_exp prec) (-a) :=
      generic_format_opp radix2 (FLX_exp prec) Fa
    have Fb' : generic_format radix2 (FLX_exp prec) (-b) :=
      generic_format_opp radix2 (FLX_exp prec) Fb
    have Hab' : |-b| ≤ -a := by
      rw [abs_neg]
      have h : |a| = -a := abs_of_neg Ha_neg
      rw [← h]; exact Hab
    have h_pos := Fast2Sum_step1_pos prec Hp choice' (by linarith : (0 : ℝ) < -a) Fa' Fb' Hab'
    -- h_pos : round_{choice'}((-a) + (-b)) - (-a) ∈ F
    -- Rewrite: (-a) + (-b) = -(a+b), so round_{choice'}(-(a+b)) - (-a)
    --                                 = round_{choice'}(-(a+b)) + a
    -- And round_{choice'}(-(a+b)) = -round_{choice}(a+b) (by round_N_opp applied "in reverse").
    have h_sum_neg : -a + -b = -(a + b) := by ring
    rw [h_sum_neg] at h_pos
    -- round_N_opp: round (Znearest choice) (-x) = -(round (Znearest choice') x) when
    -- choice' is the flipped one. We want to rewrite round (Znearest choice') (-(a+b))
    -- in terms of round (Znearest choice) (a+b).
    -- round_N_opp says: round (choice) (-x) = -round (flipped choice) x.
    -- Applied with x := a+b: round choice (-(a+b)) = -round choice' (a+b),
    -- so round choice' (a+b) = -round choice (-(a+b)).
    -- We have round choice' (-(a+b)) — apply round_N_opp with choice = choice', x = a+b:
    -- round choice' (-(a+b)) = -round (fun t => !choice' (-(t+1))) (a+b)
    --                        = -round choice (a+b)  -- since !!c = c and -(-(t+1)+1) = t.
    have h_choice_double : (fun t : ℤ => !choice' (-(t + 1))) = choice := by
      funext t
      show (!choice' (-(t + 1))) = choice t
      rw [hchoice'_def]
      show (!(!choice (-(-(t + 1) + 1)))) = choice t
      simp
    rw [round_N_opp radix2 (FLX_exp prec) choice' (a + b), h_choice_double] at h_pos
    -- h_pos : -round choice (a + b) - (-a) ∈ F
    -- i.e. -(round choice (a+b) - a) ∈ F. Apply opp closure to get round choice (a+b) - a ∈ F.
    have h_eq : -round radix2 (FLX_exp prec) (Znearest choice) (a + b) - (-a)
              = -(round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by ring
    rw [h_eq] at h_pos
    have h_target := generic_format_opp radix2 (FLX_exp prec) h_pos
    rw [neg_neg] at h_target
    exact h_target
  · -- a = 0: then |b| ≤ 0 forces b = 0, hence a + b = 0 and the difference is 0.
    have h_b_zero : b = 0 := by
      have h_abs_b_nonneg : 0 ≤ |b| := abs_nonneg b
      have h_abs_b_zero : |b| = 0 := by
        rw [Ha_zero, abs_zero] at Hab
        linarith
      exact abs_eq_zero.mp h_abs_b_zero
    rw [Ha_zero, h_b_zero, add_zero, sub_zero,
      round_0 radix2 (FLX_exp prec) (Znearest choice)]
    exact generic_format_0 _ _
  · -- a > 0: directly apply the positive lemma.
    have hab_pos : |b| ≤ a := by rwa [abs_of_pos Ha_pos] at Hab
    exact Fast2Sum_step1_pos prec Hp choice Ha_pos Fa Fb hab_pos

/-! ### The `plus_error` step -/

/-- Step 2: the residual `b - (round(a+b) - a)` equals `(a+b) - round(a+b)`,
which is the rounding error and is itself representable. -/
theorem Fast2Sum_step2
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b) :
    generic_format radix2 (FLX_exp prec)
      (b - (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a)) := by
  set s := round radix2 (FLX_exp prec) (Znearest choice) (a + b) with hs_def
  -- b - (s - a) = (a + b) - s = -(s - (a + b)).
  have h_rewrite : b - (s - a) = -(s - (a + b)) := by ring
  rw [h_rewrite]
  apply generic_format_opp
  rw [hs_def]
  exact plus_error radix2 (FLX_exp prec) (FLX_exp_valid prec Hp)
    (FLX_exp_monotone prec) choice Fa Fb

/-! ### Fast2Sum keystone -/

/-- **Fast2Sum correctness** — the error-free transformation.

Given `a, b ∈ F` (radix 2, FLX, round-to-nearest) with `|b| ≤ |a|`, define
  s := round(a + b)
  z := round(s - a)
  e := round(b - z)
Then `z = s - a`, `e = (a + b) - s`, and `a + b = s + e` exactly. -/
theorem Fast2Sum_correct
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
  -- Step 1: s - a is in format, so z = round(s - a) = s - a.
  have h_step1 : generic_format radix2 (FLX_exp prec) (s - a) :=
    Fast2Sum_step1 prec Hp choice Fa Fb Hab
  have h_z : z = s - a :=
    round_generic radix2 (FLX_exp prec) (Znearest choice) h_step1
  -- Step 2: b - (s - a) is in format (it equals (a+b) - s), so e = b - z = (a+b) - s.
  have h_step2 : generic_format radix2 (FLX_exp prec) (b - (s - a)) :=
    Fast2Sum_step2 prec Hp choice Fa Fb
  have h_e : e = b - z := by
    show round radix2 (FLX_exp prec) (Znearest choice) (b - z) = b - z
    rw [h_z]
    exact round_generic radix2 (FLX_exp prec) (Znearest choice) h_step2
  refine ⟨h_z, ?_, ?_⟩
  · rw [h_e, h_z]; ring
  · rw [h_e, h_z]; ring

end LeanFlocq
