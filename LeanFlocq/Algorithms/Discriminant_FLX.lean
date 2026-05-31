/-
# Kahan's discriminant algorithm `b² − a·c`

Kahan's algorithm computes the discriminant `b·b − a·c` of a quadratic with a
relative error of at most `2u` (twice the unit roundoff), even in the presence
of catastrophic cancellation between the two products `b·b` and `a·c`.

The algorithm (round-to-nearest, FLX):
```
  p  := RN(b·b)            q := RN(a·c)
  d  := RN(p − q)
  if 3·|d| ≥ p + q then return d                  -- benign: products far apart
  else
    dp := b·b − p   (exact)   dq := a·c − q  (exact)
    return RN(d + RN(dp − dq))                     -- (p−q)+(dp−dq) = b·b − a·c
```

This file builds the result in stages mirroring the ErrFMA development:

- **D0 (here)**: the algorithm's structural facts at general radix — the product
  errors `b·b − RN(b·b)` and `a·c − RN(a·c)` are exact floats (so the `fma`
  steps `dp`, `dq` are computed exactly), via `mult_error_FLX`.
- **D1 (here)**: the exact corrected value — in the correction branch the
  products are in Sterbenz range, so `p − q` is exact, and the un-rounded
  corrected value `(p − q) + (dp − dq)` is *exactly* the true discriminant
  `b·b − a·c` (the analog of `ErrFMA_chain`).
- **D2/D3 (later)**: the `2u` relative error bound (benign branch + assembly).

Reference: S. Boldo, "Kahan's algorithm for a correct discriminant computation
at last formally proven", IEEE Trans. Computers 58(2), 2009. Built Flocq-native
on our error-free transformations rather than the original Pff development.
-/
import LeanFlocq.Prop.Mult_error
import LeanFlocq.Prop.Sterbenz
import LeanFlocq.Prop.Relative
import LeanFlocq.Algorithms.RoundMinusRound_FLX

namespace LeanFlocq

/-! ## D0: product-error exactness (general radix) -/

/-- **The fma error step is exact.**

For `x, y ∈ F`, the residual `x·y − RN(x·y)` is itself representable, so rounding
it is the identity: `RN(x·y − RN(x·y)) = x·y − RN(x·y)`. This is what makes the
`dp := fma(b, b, −p)` and `dq := fma(a, c, −q)` steps of Kahan's algorithm
return the *exact* product errors.

General radix — only needs `mult_error_FLX` (the product error is always in F at
FLX). -/
theorem disc_fma_error_exact (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y) :
    round beta (FLX_exp prec) (Znearest choice)
        (x * y - round beta (FLX_exp prec) (Znearest choice) (x * y))
      = x * y - round beta (FLX_exp prec) (Znearest choice) (x * y) := by
  apply round_generic
  rw [show x * y - round beta (FLX_exp prec) (Znearest choice) (x * y)
        = -(round beta (FLX_exp prec) (Znearest choice) (x * y) - x * y) from by ring]
  exact generic_format_opp beta (FLX_exp prec)
    (mult_error_FLX beta prec Hp (Znearest choice) Fx Fy)

/-- The product error `x·y − RN(x·y)` is an exact float. -/
theorem disc_prod_error_format (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y) :
    generic_format beta (FLX_exp prec)
      (x * y - round beta (FLX_exp prec) (Znearest choice) (x * y)) := by
  rw [show x * y - round beta (FLX_exp prec) (Znearest choice) (x * y)
        = -(round beta (FLX_exp prec) (Znearest choice) (x * y) - x * y) from by ring]
  exact generic_format_opp beta (FLX_exp prec)
    (mult_error_FLX beta prec Hp (Znearest choice) Fx Fy)

/-! ## D1: the exact corrected value (correction branch) -/

/-- **The corrected value is exactly the discriminant.**

With `p = RN(b·b)`, `q = RN(a·c)`, and the exact product errors
`dp = b·b − p`, `dq = a·c − q`, the un-rounded corrected expression
`(p − q) + (dp − dq)` equals the true discriminant `b·b − a·c` *exactly*.

This is pure algebra — the analog of `ErrFMA_chain` for the discriminant. It
holds for any `p, q` whatsoever once `dp, dq` are defined as the residuals. The
content of Kahan's algorithm is that each piece is *computed* exactly: `dp, dq`
by `disc_fma_error_exact`, and `p − q` (in the correction branch) by Sterbenz
(`disc_sterbenz_exact`). -/
theorem disc_corrected_value {a b c p q dp dq : ℝ}
    (hdp : dp = b * b - p) (hdq : dq = a * c - q) :
    (p - q) + (dp - dq) = b * b - a * c := by
  rw [hdp, hdq]; ring

/-- **The naive subtraction is exact in the correction branch.**

When the two (nonnegative) products are within a factor of two of each other —
`q ≤ 2p` and `p ≤ 2q` — the difference `p − q` is in Sterbenz range, hence
exactly representable. This is the regime Kahan's algorithm enters when the test
`3|RN(p − q)| < p + q` detects near-cancellation; there the computed
`d = RN(p − q)` equals `p − q` exactly. -/
theorem disc_sterbenz_exact (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    {p q : ℝ}
    (Fp : generic_format beta (FLX_exp prec) p)
    (Fq : generic_format beta (FLX_exp prec) q)
    (hpq1 : q ≤ 2 * p) (hpq2 : p ≤ 2 * q) :
    generic_format beta (FLX_exp prec) (p - q) :=
  sterbenz beta (FLX_exp prec) (FLX_exp_valid prec Hp) (FLX_exp_monotone prec)
    Fp Fq ⟨by linarith, hpq2⟩

/-- `RN(b·b) ≥ 0`: the squared product rounds to a nonnegative float. -/
theorem disc_p_nonneg (beta : radix) (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool) (b : ℝ) :
    0 ≤ round beta (FLX_exp prec) (Znearest choice) (b * b) :=
  round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec Hp) (Znearest choice)
    (generic_format_0 beta (FLX_exp prec)) (mul_self_nonneg b)

/-! ## D2: the master error decomposition (general radix) -/

/-- **Error decomposition of the naive result.**

The naive result `d = RN(p − q)` (what Kahan's algorithm returns in the benign
branch) differs from the true discriminant `b·b − a·c` by at most
`u_ro · (|d| + |p| + |q|)`.

This is the exact, tight decomposition — three rounding errors, each bounded by
`u_ro` times its own (output) magnitude:
`d − (b·b − a·c) = (d − (p−q)) + (p − b·b) − (q − a·c)`,
with `|d − (p−q)| ≤ u_ro|d|`, `|p − b·b| ≤ u_ro|p|`, `|q − a·c| ≤ u_ro|q|`
(each from `err_le_uro_round_FLX`). General radix.

The benign-branch relative bound `≤ 2u_ro · |b·b − a·c|` (Boldo 2009) is obtained
from this by combining with the branch test `3|d| ≥ p + q` and a sign-cancellation
analysis of the three errors; that tightening is the remaining work. -/
theorem disc_naive_error_bound (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hde : d = round beta (FLX_exp prec) (Znearest choice) (p - q)) :
    |d - (b * b - a * c)| ≤ u_ro beta prec * (|d| + |p| + |q|) := by
  -- Each of the three roundings is within `u_ro` of its own output magnitude.
  have e1 : |d - (p - q)| ≤ u_ro beta prec * |d| := by
    rw [hde]; exact err_le_uro_round_FLX beta prec hp choice (p - q)
  have e2 : |p - b * b| ≤ u_ro beta prec * |p| := by
    rw [hpe]; exact err_le_uro_round_FLX beta prec hp choice (b * b)
  have e3 : |q - a * c| ≤ u_ro beta prec * |q| := by
    rw [hqe]; exact err_le_uro_round_FLX beta prec hp choice (a * c)
  -- Algebraic decomposition + triangle inequality.
  have key : d - (b * b - a * c)
      = (d - (p - q)) + (p - b * b) + (-(q - a * c)) := by ring
  rw [key]
  have t1 : |(d - (p - q)) + (p - b * b) + (-(q - a * c))|
      ≤ |(d - (p - q)) + (p - b * b)| + |(-(q - a * c))| := abs_add_le _ _
  have t2 : |(d - (p - q)) + (p - b * b)| ≤ |d - (p - q)| + |p - b * b| := abs_add_le _ _
  have t3 : |(-(q - a * c))| = |q - a * c| := abs_neg _
  calc |(d - (p - q)) + (p - b * b) + (-(q - a * c))|
      ≤ |d - (p - q)| + |p - b * b| + |q - a * c| := by linarith [t1, t2, t3]
    _ ≤ u_ro beta prec * |d| + u_ro beta prec * |p| + u_ro beta prec * |q| := by
          linarith [e1, e2, e3]
    _ = u_ro beta prec * (|d| + |p| + |q|) := by ring

end LeanFlocq
