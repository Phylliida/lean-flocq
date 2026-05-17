/-
TwoSum: error-free transformation for floating-point addition with no
precondition on operand magnitudes.

The branching formulation: dispatch to Fast2Sum after a magnitude
comparison. This is mathematically equivalent to Knuth's 6-op TwoSum
and substantially simpler to verify.

  if |b| ≤ |a|: (s, e) := Fast2Sum(a, b)
  else:         (s, e) := Fast2Sum(b, a)

Either way `s := round(a + b)`, `e` is representable, and
`a + b = s + e` exactly.

Setting: radix 2, FLX format, round-to-nearest with arbitrary choice.
-/
import LeanFlocq.Algorithms.Fast2Sum

namespace LeanFlocq

open radix (radix2)
open Classical

/-- **TwoSum correctness** — error-free transformation without a magnitude
precondition.

Given `a, b ∈ F` (radix 2, FLX, round-to-nearest), define
  s := round(a + b)
  e := if |b| ≤ |a|
       then round(b - round(s - a))
       else round(a - round(s - b))
Then `e ∈ F` and `a + b = s + e` exactly. -/
theorem TwoSum_correct
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b) :
    let s := round radix2 (FLX_exp prec) (Znearest choice) (a + b)
    let e := if |b| ≤ |a|
             then round radix2 (FLX_exp prec) (Znearest choice)
                    (b - round radix2 (FLX_exp prec) (Znearest choice) (s - a))
             else round radix2 (FLX_exp prec) (Znearest choice)
                    (a - round radix2 (FLX_exp prec) (Znearest choice) (s - b))
    generic_format radix2 (FLX_exp prec) e ∧ a + b = s + e := by
  intro s e
  have hValid := FLX_exp_valid prec Hp
  by_cases hab : |b| ≤ |a|
  · -- |b| ≤ |a|: e zeta-reduces to round(b - round(s - a)).
    have he : e = round radix2 (FLX_exp prec) (Znearest choice)
                (b - round radix2 (FLX_exp prec) (Znearest choice) (s - a)) :=
      if_pos hab
    refine ⟨?_, ?_⟩
    · rw [he]
      exact generic_format_round _ _ hValid _ _
    · rw [he]
      obtain ⟨_, _, h_sum⟩ := Fast2Sum_correct prec Hp choice Fa Fb hab
      exact h_sum
  · -- |a| < |b|: e zeta-reduces to round(a - round(s - b)).
    have hba : |a| ≤ |b| := le_of_not_ge hab
    have he : e = round radix2 (FLX_exp prec) (Znearest choice)
                (a - round radix2 (FLX_exp prec) (Znearest choice) (s - b)) :=
      if_neg hab
    refine ⟨?_, ?_⟩
    · rw [he]
      exact generic_format_round _ _ hValid _ _
    · rw [he]
      obtain ⟨_, _, h_sum⟩ := Fast2Sum_correct prec Hp choice Fb Fa hba
      rw [add_comm b a] at h_sum
      exact h_sum

end LeanFlocq
