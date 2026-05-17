/-
TwoSum: error-free transformation for floating-point addition with no
precondition on operand magnitudes.

The branching formulation: dispatch to Fast2Sum after a magnitude
comparison. This is mathematically equivalent to Knuth's 6-op TwoSum
and substantially simpler to verify.

  if |b| ≤ |a|: (s, e) := Fast2Sum(a, b)
  else:         (s, e) := Fast2Sum(b, a)

Either way `s := round(a + b)` and `a + b = s + e` exactly.

Setting: radix 2, FLX format, round-to-nearest with arbitrary choice.
-/
import LeanFlocq.Algorithms.Fast2Sum

namespace LeanFlocq

open radix (radix2)
open Classical

/-- **TwoSum correctness** — error-free transformation without a magnitude
precondition.

Given `a, b ∈ F` (radix 2, FLX, round-to-nearest), the sum `s := round(a + b)`
admits an exactly representable error term `e` computed by branching on
`|b| ≤ |a|`:
  s = round(a + b)
  e = if |b| ≤ |a| then round(b - round(s - a)) else round(a - round(s - b))
Then `a + b = s + e` exactly. -/
theorem TwoSum_correct
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
  · -- Case |b| ≤ |a|: directly apply Fast2Sum_correct.
    rw [if_pos hab]
    obtain ⟨_, _, h_sum⟩ := Fast2Sum_correct prec Hp choice Fa Fb hab
    exact h_sum
  · -- Case |b| > |a|: apply Fast2Sum_correct with arguments swapped.
    rw [if_neg hab]
    have hba : |a| ≤ |b| := le_of_not_ge hab
    obtain ⟨_, _, h_sum⟩ := Fast2Sum_correct prec Hp choice Fb Fa hba
    -- h_sum : b + a = round(b + a) + round(a - round(round(b + a) - b))
    rw [add_comm b a] at h_sum
    exact h_sum

end LeanFlocq
