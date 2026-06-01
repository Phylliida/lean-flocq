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

/-- **Boldo's Lemma 1 (branch-test ⟹ exact subtraction).**

In the correction branch `3|p − q| < p + q` (with `p = RN(b·b) ≥ 0`), the two
products are forced into Sterbenz range: first `q > 0` (else the condition is
absurd), then `p ≤ 2q` and `q ≤ 2p`, so `p − q` is computed exactly.

This is the gateway to the entire cancellation-case analysis of Kahan's
branch algorithm. Reference: Boldo (2009), Lemma 1. -/
theorem disc_branch_subtract_exact (beta : radix) (prec : ℤ) (hp : 0 < prec)
    {p q : ℝ}
    (Fp : generic_format beta (FLX_exp prec) p)
    (Fq : generic_format beta (FLX_exp prec) q)
    (hp_nn : 0 ≤ p)
    (hcond : 3 * |p - q| < p + q) :
    generic_format beta (FLX_exp prec) (p - q) := by
  have hpq1 : p - q ≤ |p - q| := le_abs_self _
  have hpq2 : q - p ≤ |p - q| := by rw [abs_sub_comm]; exact le_abs_self _
  -- q > 0: otherwise p + q ≤ |p - q| = p - q, contradicting 3|p-q| < p+q.
  have hq_pos : 0 < q := by
    by_contra h
    push_neg at h
    have habs : |p - q| = p - q := abs_of_nonneg (by linarith)
    rw [habs] at hcond; linarith
  -- Sterbenz range, from the condition and |p-q| ≥ ±(p-q).
  have hp_le : p ≤ 2 * q := by nlinarith [hcond, hpq1]
  have hq_le : q ≤ 2 * p := by nlinarith [hcond, hpq2]
  exact disc_sterbenz_exact beta prec hp Fp Fq hq_le hp_le

/-! ## Boldo §3: the branch algorithm `2·ulp(d)` bound (radix 2)

Kahan's *branch* algorithm (the one Boldo 2009 proves), for `b·b − a·c`:
```
  p := RN(b·b)        q := RN(a·c)
  dp := b·b − p       dq := a·c − q          (exact, via exactmult — D0)
  if 3|p − q| ≥ p + q  then  d := RN(p − q)               -- benign
                       else  d := RN((p − q) + RN(dp − dq))  -- correction
```
Boldo proves `|d − (b·b − a·c)| ≤ 2·ulp(d)` (ulps of the *result* — §8 shows the
`ulp(b·b − a·c)` form is false at powers of two; relative ≈ 4u, with the tight
2u being the separate Jeannerod–Louvet–Muller refinement). The factor-of-two
ulp arguments are radix-2 specific, so this arc is at `radix2`.

The shared starting point (general even radix) is the ulp-form error
decomposition for the naive `d = RN(p − q)`: `δ ≤ ½(ulp d + ulp p + ulp q)`. -/

/-- Rounding never decreases the ulp: `ulp x ≤ ulp (RN x)` (FLX). -/
theorem ulp_le_ulp_round_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    ulp beta (FLX_exp prec) x
      ≤ ulp beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) x) := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  rcases ulp_round beta (FLX_exp prec) hValid hNF (Znearest choice) x with heq | hpow
  · rw [heq]
  · rw [← ulp_abs beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) x), hpow,
      ulp_bpow]
    by_cases hx : x = 0
    · rw [hx, ulp_FLX_0 beta prec hp]; exact bpow_ge_0 _ _
    · rw [ulp_neq_0 beta (FLX_exp prec) hx]
      exact bpow_le beta (by unfold cexp FLX_exp; omega)

/-- Radix 2: `ulp(2·x) = 2·ulp(x)` (doubling shifts one binade). -/
theorem ulp_two_mul_r2 (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (x : ℝ) :
    ulp beta (FLX_exp prec) (2 * x) = 2 * ulp beta (FLX_exp prec) x := by
  have hb : bpow beta 1 = 2 := by rw [bpow_one, hbeta]; norm_num
  have hs := ulp_FLX_exact_shift beta prec hp x 1
  rw [hb] at hs
  rw [show (2 : ℝ) * x = x * 2 from by ring, hs]; ring

/-- Radix 2: `ulp(x/2) = ulp(x)/2`. -/
theorem ulp_half_r2 (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (x : ℝ) :
    ulp beta (FLX_exp prec) (x / 2) = ulp beta (FLX_exp prec) x / 2 := by
  have hb : bpow beta (-1) = 1 / 2 := by unfold bpow; rw [hbeta]; norm_num
  have hs := ulp_FLX_exact_shift beta prec hp x (-1)
  rw [hb] at hs
  rw [show x / 2 = x * (1 / 2) from by ring, hs]; ring

/-- **ulp-form error decomposition** (Boldo §3, the common starting bound).

For `p = RN(b·b)`, `q = RN(a·c)`, `d = RN(p − q)`:
`|d − (b·b − a·c)| ≤ ½·ulp d + ½·ulp p + ½·ulp q`,
from the three half-ulp rounding bounds (`error_le_half_ulp_round`) on
`d = RN(p−q)`, `p = RN(b·b)`, `q = RN(a·c)` and the algebraic split
`d − (b·b−a·c) = (d−(p−q)) + (p−b·b) − (q−a·c)`. General radix. -/
theorem disc_branch_err_decomp (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hde : d = round beta (FLX_exp prec) (Znearest choice) (p - q)) :
    |d - (b * b - a * c)|
      ≤ (1/2) * ulp beta (FLX_exp prec) d
        + (1/2) * ulp beta (FLX_exp prec) p
        + (1/2) * ulp beta (FLX_exp prec) q := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have ed : |d - (p - q)| ≤ (1/2) * ulp beta (FLX_exp prec) d := by
    rw [hde]; exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (p - q)
  have ep : |p - b * b| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hpe]; exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have eq' : |q - a * c| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [hqe]; exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  have key : d - (b * b - a * c) = (d - (p - q)) + (p - b * b) + (-(q - a * c)) := by ring
  rw [key]
  have t1 : |(d - (p - q)) + (p - b * b) + (-(q - a * c))|
      ≤ |(d - (p - q)) + (p - b * b)| + |(-(q - a * c))| := abs_add_le _ _
  have t2 : |(d - (p - q)) + (p - b * b)| ≤ |d - (p - q)| + |p - b * b| := abs_add_le _ _
  have t3 : |(-(q - a * c))| = |q - a * c| := abs_neg _
  calc |(d - (p - q)) + (p - b * b) + (-(q - a * c))|
      ≤ |d - (p - q)| + |p - b * b| + |q - a * c| := by linarith [t1, t2, t3]
    _ ≤ (1/2) * ulp beta (FLX_exp prec) d + (1/2) * ulp beta (FLX_exp prec) p
          + (1/2) * ulp beta (FLX_exp prec) q := by linarith [ed, ep, eq']

/-- **Benign-case ulp key** (radix 2, Boldo §3.1).

Under the benign test `3|p − q| ≥ p + q` with `p ≥ 0`, the products' ulps are
controlled by the ulp of the result: `ulp p + ulp q ≤ 3·ulp(RN(p − q))`. Three
subcases (`p ≥ q ≥ 0`, `p ≥ q > ` negative, `q > p`), each using the radix-2
doubling/halving ulp shifts and `ulp ≤ ulp∘round`. -/
theorem disc_benign_ulp_key (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {p q : ℝ}
    (hp_nn : 0 ≤ p)
    (hcond : p + q ≤ 3 * |p - q|) :
    ulp beta (FLX_exp prec) p + ulp beta (FLX_exp prec) q
      ≤ 3 * ulp beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (p - q)) := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  set R := round beta (FLX_exp prec) (Znearest choice) (p - q) with hR
  have hround : ulp beta (FLX_exp prec) (p - q) ≤ ulp beta (FLX_exp prec) R := by
    rw [hR]; exact ulp_le_ulp_round_FLX beta prec hp choice (p - q)
  have hud0 : 0 ≤ ulp beta (FLX_exp prec) R := ulp_ge_0 _ _ _
  rcases le_or_lt q p with hqp | hqp
  · -- q ≤ p:  |p - q| = p - q,  2q ≤ p,  p - q ≥ p/2.
    have habs : |p - q| = p - q := abs_of_nonneg (by linarith)
    rw [habs] at hcond
    have h2q : 2 * q ≤ p := by linarith
    have hpq2 : p / 2 ≤ p - q := by linarith
    rcases le_or_lt 0 q with hq0 | hq0
    · -- q ≥ 0:  2·ulp q ≤ ulp p  and  ulp p / 2 ≤ ulp R.
      have f1 : 2 * ulp beta (FLX_exp prec) q ≤ ulp beta (FLX_exp prec) p := by
        rw [← ulp_two_mul_r2 beta hbeta prec hp q]
        exact ulp_le_pos beta (FLX_exp prec) hValid hMon (by linarith) h2q
      have f2 : ulp beta (FLX_exp prec) p / 2 ≤ ulp beta (FLX_exp prec) R := by
        rw [← ulp_half_r2 beta hbeta prec hp p]
        exact le_trans (ulp_le_pos beta (FLX_exp prec) hValid hMon (by linarith) hpq2) hround
      linarith
    · -- q < 0:  ulp p ≤ ulp R  and  ulp q ≤ ulp R.
      have f1 : ulp beta (FLX_exp prec) p ≤ ulp beta (FLX_exp prec) R :=
        le_trans (ulp_le_pos beta (FLX_exp prec) hValid hMon hp_nn (by linarith)) hround
      have f2 : ulp beta (FLX_exp prec) q ≤ ulp beta (FLX_exp prec) R := by
        refine le_trans ?_ hround
        apply ulp_le beta (FLX_exp prec) hValid hMon
        rw [habs, abs_of_neg hq0]; linarith
      linarith
  · -- q > p:  |p - q| = q - p,  2p ≤ q,  q - p ≥ q/2.
    have hq_pos : 0 < q := lt_of_le_of_lt hp_nn hqp
    have habs : |p - q| = q - p := by rw [abs_of_nonpos (by linarith)]; ring
    rw [habs] at hcond
    have h2p : 2 * p ≤ q := by linarith
    have hpq2 : q / 2 ≤ q - p := by linarith
    have f1 : 2 * ulp beta (FLX_exp prec) p ≤ ulp beta (FLX_exp prec) q := by
      rw [← ulp_two_mul_r2 beta hbeta prec hp p]
      exact ulp_le_pos beta (FLX_exp prec) hValid hMon (by linarith) h2p
    have f2 : ulp beta (FLX_exp prec) q / 2 ≤ ulp beta (FLX_exp prec) R := by
      rw [← ulp_half_r2 beta hbeta prec hp q]
      refine le_trans ?_ hround
      apply ulp_le beta (FLX_exp prec) hValid hMon
      rw [habs, abs_of_nonneg (by linarith : (0:ℝ) ≤ q / 2)]; linarith
    linarith

/-- **Boldo §3.1: the benign branch is within `2·ulp(d)`** (radix 2).

When `3|p − q| ≥ p + q`, the algorithm returns `d = RN(p − q)`, and
`|d − (b·b − a·c)| ≤ 2·ulp(d)`. Combines the ulp-form decomposition with the
benign ulp key. -/
theorem disc_branch_benign (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hde : d = round beta (FLX_exp prec) (Znearest choice) (p - q))
    (hcond : p + q ≤ 3 * |p - q|) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hp_nn : 0 ≤ p := by rw [hpe]; exact disc_p_nonneg beta prec hp choice b
  have hdecomp := disc_branch_err_decomp beta prec hp choice a b c hpe hqe hde
  have hkey := disc_benign_ulp_key beta hbeta prec hp choice hp_nn hcond
  rw [← hde] at hkey
  linarith [hdecomp, hkey]

/-! ### Boldo §3.2: the correction branch

When `3|p − q| < p + q` the products nearly cancel; the algorithm returns
`d = RN((p − q) + g)` with `g = RN(dp − dq)` (and `p − q` exact by Lemma 1).
Writing `b·b − a·c = (p − q) + (dp − dq)` (D1), the error splits into the outer
rounding and the inner correction rounding. -/

/-- **Correction-branch error decomposition.**

For `g = RN(dp − dq)` and `d = RN((p − q) + g)` (with `dp = b·b − p`,
`dq = a·c − q`): `|d − (b·b − a·c)| ≤ ½·ulp d + ½·ulp g`. General radix. -/
theorem disc_corr_err_decomp (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g)) :
    |d - (b * b - a * c)|
      ≤ (1/2) * ulp beta (FLX_exp prec) d + (1/2) * ulp beta (FLX_exp prec) g := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have eo : |d - ((p - q) + g)| ≤ (1/2) * ulp beta (FLX_exp prec) d := by
    rw [hd]; exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice ((p - q) + g)
  have ei : |g - (dp - dq)| ≤ (1/2) * ulp beta (FLX_exp prec) g := by
    rw [hg]; exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (dp - dq)
  have key : d - (b * b - a * c) = (d - ((p - q) + g)) + (g - (dp - dq)) := by
    rw [hdp, hdq]; ring
  rw [key]
  calc |(d - ((p - q) + g)) + (g - (dp - dq))|
      ≤ |d - ((p - q) + g)| + |g - (dp - dq)| := abs_add_le _ _
    _ ≤ (1/2) * ulp beta (FLX_exp prec) d + (1/2) * ulp beta (FLX_exp prec) g := by linarith

/-- **Boldo Lemma 3: if `dp − dq` is exact, the result is within `½·ulp d`.**

Then `g = dp − dq` and `(p − q) + g = b·b − a·c`, so `d = RN(b·b − a·c)`. -/
theorem disc_corr_exact (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hexact : generic_format beta (FLX_exp prec) (dp - dq)) :
    |d - (b * b - a * c)| ≤ (1/2) * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hg_exact : g = dp - dq := by
    rw [hg]; exact round_generic beta (FLX_exp prec) (Znearest choice) hexact
  have hs : (p - q) + g = b * b - a * c := by rw [hg_exact, hdp, hdq]; ring
  rw [hd, hs]
  exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b - a * c)

/-- The product-error difference is bounded by half the ulps of the products:
`|dp − dq| ≤ ½·ulp p + ½·ulp q`. General radix. -/
theorem disc_corr_dpdq_bound (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q) :
    |dp - dq| ≤ (1/2) * ulp beta (FLX_exp prec) p + (1/2) * ulp beta (FLX_exp prec) q := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hdp_bd : |b * b - p| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [abs_sub_comm, hpe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have hdq_bd : |a * c - q| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [abs_sub_comm, hqe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  have htri : |dp - dq| ≤ |b * b - p| + |a * c - q| := by
    have h := abs_add_le (b * b - p) (-(a * c - q))
    rw [show (b * b - p) + -(a * c - q) = dp - dq from by rw [hdp, hdq]; ring,
      abs_neg] at h
    exact h
  linarith

/-- **Boldo §3.2.1 general case: small correction ⟹ within `2·ulp d`** (radix 2).

When `|dp − dq| ≤ ½|p − q|` (the regime `|p − q| ≥ 3·min(ulp p, ulp q)`), the
inner correction `g = RN(dp − dq)` has `|g| ≤ ½|p − q| ≤ |(p − q) + g|`, so
`ulp g ≤ ulp d`, and the decomposition gives `δ ≤ ½ulp d + ½ulp g ≤ ulp d`. -/
theorem disc_corr_general (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hpqF : generic_format beta (FLX_exp prec) (p - q))
    (hsmall : |dp - dq| ≤ |p - q| / 2) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  -- ½|p − q| is representable (halving a float at radix 2).
  have hpq2_F : generic_format beta (FLX_exp prec) ((p - q) / 2) := by
    have h := mult_bpow_exact_FLX beta prec (-1) hpqF
    rwa [show bpow beta (-1) = (1 : ℝ) / 2 by unfold bpow; rw [hbeta]; norm_num,
      show (p - q) * ((1 : ℝ) / 2) = (p - q) / 2 from by ring] at h
  have hhalf_F : generic_format beta (FLX_exp prec) (|p - q| / 2) := by
    rcases abs_cases (p - q) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; exact hpq2_F
    · rw [he, show -(p - q) / 2 = -((p - q) / 2) from by ring]
      exact generic_format_opp beta (FLX_exp prec) hpq2_F
  -- |g| ≤ ½|p − q|.
  have hg_bd : |g| ≤ |p - q| / 2 := by
    rw [hg]; exact abs_round_le_generic beta (FLX_exp prec) hValid (Znearest choice) hhalf_F hsmall
  -- |(p − q) + g| ≥ ½|p − q|, hence |g| ≤ |(p − q) + g|.
  have htri : |p - q| ≤ |(p - q) + g| + |g| := by
    have h := abs_add_le ((p - q) + g) (-g)
    rw [show (p - q) + g + -g = p - q from by ring, abs_neg] at h
    exact h
  have hg_le_s : |g| ≤ |(p - q) + g| := by linarith
  have hulp_g : ulp beta (FLX_exp prec) g ≤ ulp beta (FLX_exp prec) ((p - q) + g) :=
    ulp_le beta (FLX_exp prec) hValid hMon hg_le_s
  have hulp_gd : ulp beta (FLX_exp prec) g ≤ ulp beta (FLX_exp prec) d := by
    rw [hd]; exact le_trans hulp_g (ulp_le_ulp_round_FLX beta prec hp choice ((p - q) + g))
  have hdecomp := disc_corr_err_decomp beta prec hp choice a b c hdp hdq hg hd
  linarith [hdecomp, hulp_gd, ulp_ge_0 beta (FLX_exp prec) d]

/-- **Correction branch, products far apart: `ulp p + ulp q ≤ |p − q| ⟹ δ ≤ 2·ulp d`.**

Combines the `|dp − dq| ≤ ½(ulp p + ulp q)` bound with the general case. -/
theorem disc_corr_far (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hpqF : generic_format beta (FLX_exp prec) (p - q))
    (hfar : ulp beta (FLX_exp prec) p + ulp beta (FLX_exp prec) q ≤ |p - q|) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hbd := disc_corr_dpdq_bound beta prec hp choice a b c hpe hqe hdp hdq
  have hsmall : |dp - dq| ≤ |p - q| / 2 := by linarith
  exact disc_corr_general beta hbeta prec hp choice a b c hdp hdq hg hd hpqF hsmall

/-- **Correction branch, `p = q`: `δ ≤ 2·ulp d`** (in fact `d = RN(b·b − a·c)`).

When `p = q`, `p − q = 0`, `g = RN(dp − dq) = RN(b·b − a·c)`, and the outer round
is the identity, so `d = RN(b·b − a·c)` and `δ ≤ ½·ulp d`. -/
theorem disc_corr_pq_eq (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hpq_eq : p = q) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hdpdq : dp - dq = b * b - a * c := by rw [hdp, hdq, hpq_eq]; ring
  have hg' : g = round beta (FLX_exp prec) (Znearest choice) (b * b - a * c) := by
    rw [hg, hdpdq]
  have hg_F : generic_format beta (FLX_exp prec) g := by
    rw [hg']; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  have hd' : d = g := by
    rw [hd, show p - q = 0 from by rw [hpq_eq]; ring, zero_add]
    exact round_generic beta (FLX_exp prec) (Znearest choice) hg_F
  rw [hd', hg']
  have herr := error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b - a * c)
  have h0 := ulp_ge_0 beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (b * b - a * c))
  linarith

/-! ### Boldo §3.2 Lemma 4: equal ulps ⟹ exact correction

Boldo's first "easy" correction subcase: when `ulp p = ulp q`, the inner
difference `dp − dq` is computed *exactly*, so the result is within `½·ulp d`
(Lemma 3). The proof is a grid argument: both product errors `dp`, `dq` are
integer multiples of the common grid `β^(cexp p − prec)`, and `|dp − dq| ≤
ulp p = β^(cexp p)`, so the mantissa of `dp − dq` at that grid is an integer of
magnitude `≤ β^prec` — either `< β^prec` (in `F` by the grid bound) or exactly
`= β^prec` (then `dp − dq = ±β^(cexp p)`, a power of `β`, also in `F`). -/

/-- Coarsen an integer multiple of a fine grid onto a coarser grid (mirrors
`bpow_coarsen`): `M·β^G = (M·β^(G−E))·β^E` for `E ≤ G`. -/
private theorem disc_bpow_coarsen (beta : radix) (M E_small E_big : ℤ)
    (h : E_small ≤ E_big) :
    (M : ℝ) * bpow beta E_big
      = ((M * beta.val ^ (E_big - E_small).toNat : ℤ) : ℝ) * bpow beta E_small := by
  have hd : 0 ≤ E_big - E_small := by omega
  have hsplit : bpow beta E_big = bpow beta (E_big - E_small) * bpow beta E_small := by
    rw [← bpow_plus]; congr 1; omega
  rw [hsplit, ← IZR_Zpower beta hd]
  push_cast; ring

/-- **Grid-difference exactness** (general radix) — the heart of Lemma 4.

If `x` and `y` are integer multiples of a common grid `β^E` and
`|x − y| ≤ β^(prec+E)`, then `x − y ∈ F(FLX prec)`. The mantissa `M = Mx − My`
satisfies `|M| ≤ β^prec`: strictly inside the binade (`< β^(prec+E)`) it is in
`F` by the grid bound; at the boundary (`= β^(prec+E)`) the value is `±β^(prec+E)`,
a power of `β`. -/
theorem disc_diff_on_grid_exact (beta : radix) (prec : ℤ) (hp : 0 < prec)
    {x y : ℝ} (E Mx My : ℤ)
    (hx : x = (Mx : ℝ) * bpow beta E)
    (hy : y = (My : ℝ) * bpow beta E)
    (hbound : |x - y| ≤ bpow beta (prec + E)) :
    generic_format beta (FLX_exp prec) (x - y) := by
  have hMform : x - y = ((Mx - My : ℤ) : ℝ) * bpow beta E := by
    rw [hx, hy]; push_cast; ring
  rcases lt_or_eq_of_le hbound with hlt | heq
  · -- strict: the value lies strictly inside the binade.
    by_cases hM : (Mx - My) = 0
    · rw [hMform, hM]; push_cast; rw [zero_mul]; exact generic_format_0 _ _
    have hvF2R : x - y = F2R (beta := beta) ⟨Mx - My, E⟩ := hMform
    have hvne : x - y ≠ 0 := by
      rw [hMform]; exact mul_ne_zero (by exact_mod_cast hM) (ne_of_gt (bpow_gt_0 beta E))
    have h_mag : mag beta (x - y) ≤ prec + E := mag_le_bpow beta hvne hlt
    rw [hvF2R]
    apply generic_format_F2R
    intro _
    rw [← hvF2R]
    show cexp beta (FLX_exp prec) (x - y) ≤ E
    have hcx : cexp beta (FLX_exp prec) (x - y) = mag beta (x - y) - prec := by
      unfold cexp FLX_exp; rfl
    rw [hcx]; omega
  · -- boundary: `x − y = ±β^(prec+E)`, a power of `β`.
    have hb_nn : (0 : ℝ) ≤ bpow beta (prec + E) := le_of_lt (bpow_gt_0 beta (prec + E))
    rcases (abs_eq hb_nn).mp heq with h | h
    · rw [h]
      exact generic_format_bpow beta (FLX_exp prec) (prec + E) (by unfold FLX_exp; omega)
    · rw [h]
      exact generic_format_opp beta (FLX_exp prec)
        (generic_format_bpow beta (FLX_exp prec) (prec + E) (by unfold FLX_exp; omega))

/-- The product error `x·y − RN(x·y)` is an integer multiple of the product grid
`β^(cexp x + cexp y)` (from `mult_error_FLX_aux`, which places it at exactly that
exponent). General radix. -/
theorem disc_prod_err_mult_bpow (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y) :
    ∃ M : ℤ, x * y - round beta (FLX_exp prec) (Znearest choice) (x * y)
        = (M : ℝ)
          * bpow beta (cexp beta (FLX_exp prec) x + cexp beta (FLX_exp prec) y) := by
  by_cases hz : round beta (FLX_exp prec) (Znearest choice) (x * y) - x * y = 0
  · refine ⟨0, ?_⟩
    have h0 : x * y - round beta (FLX_exp prec) (Znearest choice) (x * y) = 0 := by linarith
    rw [h0]; push_cast; ring
  · obtain ⟨f, hF2R, _, hexp⟩ := mult_error_FLX_aux beta prec hp (Znearest choice) Fx Fy hz
    refine ⟨-f.Fnum, ?_⟩
    have hneg : x * y - round beta (FLX_exp prec) (Znearest choice) (x * y) = -(F2R f) := by
      rw [hF2R]; ring
    rw [hneg]
    unfold F2R
    rw [hexp]; push_cast; ring

/-- **Orientation-agnostic inner-exactness core.**

Given the two product errors `dp = b·b − p`, `dq = a·c − q` and a common grid
exponent `E` lying below both product grids (`E ≤ 2·cexp b` and
`E ≤ cexp a + cexp c`), if `|dp − dq| ≤ β^(prec+E)` then `dp − dq` is computed
*exactly*. Both errors are integer multiples of their product grids
(`disc_prod_err_mult_bpow`); coarsening each onto the common `β^E`
(`disc_bpow_coarsen`) puts the difference on a single grid, where
`disc_diff_on_grid_exact` finishes. This is the shared engine of *both*
orientations of the §3.2.2 particular case — the reference grid is
`E = mag(min p q) − 2·prec`. General radix. -/
theorem disc_inner_exact (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (E : ℤ)
    (hEb : E ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b)
    (hEac : E ≤ cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c)
    (hbound : |dp - dq| ≤ bpow beta (prec + E)) :
    generic_format beta (FLX_exp prec) (dp - dq) := by
  obtain ⟨Mdp0, hMdp0⟩ := disc_prod_err_mult_bpow beta prec hp choice Fb Fb
  obtain ⟨Mdq0, hMdq0⟩ := disc_prod_err_mult_bpow beta prec hp choice Fa Fc
  have hdp_eq : dp = (Mdp0 : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b) := by
    rw [hdp, hpe]; exact hMdp0
  have hdq_eq : dq = (Mdq0 : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c) := by
    rw [hdq, hqe]; exact hMdq0
  have hdp_E : dp = ((Mdp0 * beta.val
        ^ (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b - E).toNat : ℤ) : ℝ)
        * bpow beta E := by rw [hdp_eq]; exact disc_bpow_coarsen beta Mdp0 E _ hEb
  have hdq_E : dq = ((Mdq0 * beta.val
        ^ (cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c - E).toNat : ℤ) : ℝ)
        * bpow beta E := by rw [hdq_eq]; exact disc_bpow_coarsen beta Mdq0 E _ hEac
  exact disc_diff_on_grid_exact beta prec hp E _ _ hdp_E hdq_E hbound

/-- **Boldo Lemma 4: equal ulps ⟹ `δ ≤ 2·ulp(d)`** (general radix).

When `ulp p = ulp q` and neither product crosses a binade under rounding (the
two grid hypotheses, which fail only when `p` resp. `q` is an exact rounded-up
power of two — handled by the §3.2.2 particular cases), the inner difference
`dp − dq` is computed *exactly* (`disc_diff_on_grid_exact`), so the result is
within `½·ulp d` by Lemma 3 (`disc_corr_exact`), hence within `2·ulp d`.

The inputs `a, b, c` are floats (`Fa, Fb, Fc`), as in Kahan's algorithm. -/
theorem disc_corr_lemma4 (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hulp : ulp beta (FLX_exp prec) p = ulp beta (FLX_exp prec) q)
    (hgb : cexp beta (FLX_exp prec) p - prec
            ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b)
    (hgc : cexp beta (FLX_exp prec) p - prec
            ≤ cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  -- It suffices to show `dp − dq ∈ F`; Lemma 3 then closes (and `½ ≤ 2`).
  suffices hF : generic_format beta (FLX_exp prec) (dp - dq) by
    have h3 := disc_corr_exact beta prec hp choice a b c hdp hdq hg hd hF
    have h0 := ulp_ge_0 beta (FLX_exp prec) d
    linarith
  -- The half-ulp product-error bound (shared with both branches).
  have hbd := disc_corr_dpdq_bound beta prec hp choice a b c hpe hqe hdp hdq
  by_cases hp0 : p = 0
  · -- ulp p = 0 ⟹ dp = dq = 0 ⟹ dp − dq = 0.
    have hulp0 : ulp beta (FLX_exp prec) p = 0 := by rw [hp0]; exact ulp_FLX_0 beta prec hp
    have hq0u : ulp beta (FLX_exp prec) q = 0 := by rw [← hulp, hulp0]
    have h0 : |dp - dq| ≤ 0 := by rw [hulp0, hq0u] at hbd; linarith
    have hdpdq0 : dp - dq = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
    rw [hdpdq0]; exact generic_format_0 _ _
  · -- Main case: grid argument at common exponent `E = cexp p − prec`.
    set E := cexp beta (FLX_exp prec) p - prec with hE
    -- Each product error is an integer multiple of its product grid, then coarsen to `E`.
    obtain ⟨Mdp0, hMdp0⟩ := disc_prod_err_mult_bpow beta prec hp choice Fb Fb
    obtain ⟨Mdq0, hMdq0⟩ := disc_prod_err_mult_bpow beta prec hp choice Fa Fc
    have hdp_eq : dp = (Mdp0 : ℝ)
        * bpow beta (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b) := by
      rw [hdp, hpe]; exact hMdp0
    have hdq_eq : dq = (Mdq0 : ℝ)
        * bpow beta (cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c) := by
      rw [hdq, hqe]; exact hMdq0
    have hdp_E : dp = ((Mdp0 * beta.val
          ^ (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b - E).toNat : ℤ) : ℝ)
          * bpow beta E := by
      rw [hdp_eq]; exact disc_bpow_coarsen beta Mdp0 E _ hgb
    have hdq_E : dq = ((Mdq0 * beta.val
          ^ (cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c - E).toNat : ℤ) : ℝ)
          * bpow beta E := by
      rw [hdq_eq]; exact disc_bpow_coarsen beta Mdq0 E _ hgc
    -- `|dp − dq| ≤ ulp p = β^(cexp p) = β^(prec+E)`.
    have hsum : (1/2) * ulp beta (FLX_exp prec) p + (1/2) * ulp beta (FLX_exp prec) q
        = ulp beta (FLX_exp prec) p := by rw [← hulp]; ring
    have hdpdq_le : |dp - dq| ≤ ulp beta (FLX_exp prec) p := by linarith [hbd, hsum]
    have hulp_p : ulp beta (FLX_exp prec) p = bpow beta (prec + E) := by
      rw [ulp_neq_0 beta (FLX_exp prec) hp0]; congr 1; omega
    have hbound : |dp - dq| ≤ bpow beta (prec + E) := by rw [← hulp_p]; exact hdpdq_le
    exact disc_diff_on_grid_exact beta prec hp E _ _ hdp_E hdq_E hbound

/-- **The grid hypothesis holds unless the product rounds to a power of two.**

For `b ≠ 0`, either `cexp(◦(b·b)) − prec ≤ 2·cexp b` (the grid hypothesis of
Lemma 4) holds, or `◦(b·b)` is the boundary power of two `β^(2·cexp b + 2·prec) =
β^(2·mag b)`. From `mag_mult` (`mag(b·b) ≤ 2·mag b`) and `mag_round` (rounding
either preserves `mag` or jumps to the next power of `β`): the grid bound fails
*only* when `b·b` rounds up across the binade `2·mag b` — exactly the case that
feeds Boldo's §3.2.2 particular cases. This is the tool that splits Lemma 4's
clean regime from its power-of-two boundary. -/
theorem disc_prod_grid_or_pow2 (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {b : ℝ} (hb : b ≠ 0) :
    cexp beta (FLX_exp prec) (round beta (FLX_exp prec) (Znearest choice) (b * b)) - prec
        ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b
      ∨ round beta (FLX_exp prec) (Znearest choice) (b * b)
        = bpow beta (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b + 2 * prec) := by
  have hValid := FLX_exp_valid prec hp
  have hbb_pos : 0 < b * b := mul_self_pos.mpr hb
  have hp_pos : 0 < round beta (FLX_exp prec) (Znearest choice) (b * b) :=
    gt_0_round_gt_0_FLX beta prec hp (Znearest choice) hbb_pos
  have hp_ne : round beta (FLX_exp prec) (Znearest choice) (b * b) ≠ 0 := ne_of_gt hp_pos
  have hmag_mult : mag beta (b * b) ≤ mag beta b + mag beta b := (mag_mult beta hb hb).2
  have hmr := mag_round beta (FLX_exp prec) hValid (Znearest choice) hp_ne
  have hmax : max (mag beta (b * b)) (FLX_exp prec (mag beta (b * b))) = mag beta (b * b) := by
    apply max_eq_left; unfold FLX_exp; omega
  rw [hmax] at hmr
  set p := round beta (FLX_exp prec) (Znearest choice) (b * b) with hpdef
  rcases hmr with hmr1 | hmr2
  · -- rounding preserved `mag`: `mag p = mag(b·b) ≤ 2·mag b`.
    left; unfold cexp FLX_exp; omega
  · -- rounding jumped to `β^(mag(b·b))`; `p = β^(mag(b·b))` since `p > 0`.
    rw [abs_of_pos hp_pos] at hmr2
    have hmagp : mag beta p = mag beta (b * b) + 1 := by rw [hmr2, mag_bpow]
    rcases lt_or_eq_of_le hmag_mult with hlt | heq
    · -- below the binade: `mag p = mag(b·b)+1 ≤ 2·mag b`.
      left; unfold cexp FLX_exp; omega
    · -- on the binade `mag(b·b) = 2·mag b`: `p = β^(2·mag b)`, the boundary power.
      right; rw [hmr2, heq]; congr 1; unfold cexp FLX_exp; omega

/-! ### Grid-bound discharge for the particular case

The §3.2.2 subcases (and Lemma 4) need grid bounds `mag(RN(b·b)) ≤ mag b + mag b` and
`mag(RN(a·c)) ≤ mag a + mag c`. Both follow from the single keystone below: a product
of two `prec`-significand floats is too small (by a factor argument) to round up to the
binade-doubling power `β^(mag x+mag y)`, so its magnitude never bumps. This discharges
every grid hypothesis *unconditionally* — no `prec ≥ 3`, no near-cancellation needed. -/

/-- **Products never bump the magnitude.** `mag(RN(x·y)) ≤ mag x + mag y` for nonzero
`x·y` with `x, y ∈ F` — *unconditional*. Since `|x| ≤ β^(mag x) − ulp x` and likewise
for `y`, the product `|x·y| ≤ (β^(mag x) − ulp x)(β^(mag y) − ulp y) =
β^(mag x+mag y)(1 − β^(−prec))²` lies strictly below the round-up midpoint
`β^(mag x+mag y)(1 − ½β^(−prec))` of the power `β^(mag x+mag y)` (because
`(1−t)² < 1 − ½t` for `0 < t = β^(−prec) ≤ ½`). So rounding cannot reach that power.
This is the keystone making every §3.2 product grid bound unconditional — in
particular it discharges Boldo Lemma 4's grid hypotheses with no side conditions. -/
theorem disc_mag_prod_no_bump (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y)
    (hxy : 0 < x * y) :
    mag beta (round beta (FLX_exp prec) (Znearest choice) (x * y))
      ≤ mag beta x + mag beta y := by
  have hValid := FLX_exp_valid prec hp
  have hx : x ≠ 0 := left_ne_zero_of_mul (ne_of_gt hxy)
  have hy : y ≠ 0 := right_ne_zero_of_mul (ne_of_gt hxy)
  have hxa : (0:ℝ) < |x| := abs_pos.mpr hx
  have hya : (0:ℝ) < |y| := abs_pos.mpr hy
  set ex := mag beta x with hex
  set ey := mag beta y with hey
  have hcexp_ax : ulp beta (FLX_exp prec) |x| = bpow beta (ex - prec) := by
    rw [ulp_abs, ulp_neq_0 beta (FLX_exp prec) hx]; unfold cexp FLX_exp; rw [← hex]
  have hcexp_ay : ulp beta (FLX_exp prec) |y| = bpow beta (ey - prec) := by
    rw [ulp_abs, ulp_neq_0 beta (FLX_exp prec) hy]; unfold cexp FLX_exp; rw [← hey]
  have hxlt : |x| < bpow beta ex := by have := bpow_mag_gt beta x; rwa [← hex] at this
  have hylt : |y| < bpow beta ey := by have := bpow_mag_gt beta y; rwa [← hey] at this
  have hFax : generic_format beta (FLX_exp prec) |x| := generic_format_abs beta (FLX_exp prec) Fx
  have hFay : generic_format beta (FLX_exp prec) |y| := generic_format_abs beta (FLX_exp prec) Fy
  have hxb : |x| + bpow beta (ex - prec) ≤ bpow beta ex := by
    have h := id_p_ulp_le_bpow beta (FLX_exp prec) hxa hFax (e := ex) hxlt
    rwa [hcexp_ax] at h
  have hyb : |y| + bpow beta (ey - prec) ≤ bpow beta ey := by
    have h := id_p_ulp_le_bpow beta (FLX_exp prec) hya hFay (e := ey) hylt
    rwa [hcexp_ay] at h
  have hxy_eq : x * y = |x| * |y| := by rw [← abs_mul, abs_of_pos hxy]
  -- bpow product identities.
  have hpe1 : bpow beta ex * bpow beta ey = bpow beta (ex + ey) := by rw [← bpow_plus]
  have hpe2 : bpow beta (ex - prec) * bpow beta ey = bpow beta (ex + ey - prec) := by
    rw [← bpow_plus]; congr 1; ring
  have hpe3 : bpow beta ex * bpow beta (ey - prec) = bpow beta (ex + ey - prec) := by
    rw [← bpow_plus]; congr 1; ring
  have hpe4 : bpow beta (ex - prec) * bpow beta (ey - prec) = bpow beta (ex + ey - 2 * prec) := by
    rw [← bpow_plus]; congr 1; ring
  -- product upper bound, expanded over the common power.
  have hbnnx : (0:ℝ) ≤ bpow beta ex - bpow beta (ex - prec) := by linarith [hxb, hxa]
  have hxy_ub : x * y ≤ (bpow beta ex - bpow beta (ex - prec))
      * (bpow beta ey - bpow beta (ey - prec)) := by
    rw [hxy_eq]
    exact mul_le_mul (by linarith [hxb]) (by linarith [hyb]) (le_of_lt hya) hbnnx
  have hexp : (bpow beta ex - bpow beta (ex - prec)) * (bpow beta ey - bpow beta (ey - prec))
      = bpow beta (ex + ey) - 2 * bpow beta (ex + ey - prec) + bpow beta (ex + ey - 2 * prec) := by
    have hdist : (bpow beta ex - bpow beta (ex - prec)) * (bpow beta ey - bpow beta (ey - prec))
        = bpow beta ex * bpow beta ey - bpow beta ex * bpow beta (ey - prec)
          - bpow beta (ex - prec) * bpow beta ey
          + bpow beta (ex - prec) * bpow beta (ey - prec) := by ring
    rw [hdist, hpe1, hpe3, hpe2, hpe4]; ring
  have hxy_ub' : x * y ≤ bpow beta (ex + ey) - 2 * bpow beta (ex + ey - prec)
      + bpow beta (ex + ey - 2 * prec) := by rw [hexp] at hxy_ub; exact hxy_ub
  -- round-up exclusion.
  by_contra hcon
  push_neg at hcon
  set r := round beta (FLX_exp prec) (Znearest choice) (x * y) with hr
  have hr_pos : 0 < r := by rw [hr]; exact gt_0_round_gt_0_FLX beta prec hp (Znearest choice) hxy
  have hr_ge : bpow beta (ex + ey) ≤ r := by
    have h := bpow_mag_le beta (ne_of_gt hr_pos)
    rw [abs_of_pos hr_pos] at h
    exact le_trans (bpow_le beta (by omega)) h
  have herr : |r - x * y| ≤ (1/2) * ulp beta (FLX_exp prec) (x * y) := by
    rw [hr]; exact error_le_half_ulp beta (FLX_exp prec) hValid choice (x * y)
  have hulp_xy : ulp beta (FLX_exp prec) (x * y) ≤ bpow beta (ex + ey - prec) := by
    rw [ulp_neq_0 beta (FLX_exp prec) (ne_of_gt hxy)]
    apply bpow_le beta
    have hmm : mag beta (x * y) ≤ ex + ey := by
      have := (mag_mult beta hx hy).2; rw [← hex, ← hey] at this; exact this
    unfold cexp FLX_exp; omega
  have hgap : bpow beta (ex + ey) - x * y ≤ (1/2) * bpow beta (ex + ey - prec) := by
    have h2 : r - x * y ≤ |r - x * y| := le_abs_self _
    have h3 : (1/2) * ulp beta (FLX_exp prec) (x * y) ≤ (1/2) * bpow beta (ex + ey - prec) :=
      mul_le_mul_of_nonneg_left hulp_xy (by norm_num)
    linarith [hr_ge, h2, herr, h3]
  -- `β^(ex+ey−2prec) ≤ ½·β^(ex+ey−prec)` since `β^(−prec) ≤ ½`.
  have h2le : (2:ℝ) ≤ bpow beta prec := by
    calc (2:ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
      _ = bpow beta 1 := (bpow_one beta).symm
      _ ≤ bpow beta prec := bpow_le beta hp
  have hmul1 : bpow beta (-prec) * bpow beta prec = 1 := by
    rw [← bpow_plus, neg_add_cancel, bpow_zero]
  have hbp : bpow beta (-prec) ≤ 1/2 := by
    have hpos : 0 < bpow beta prec := bpow_gt_0 _ _
    nlinarith [hmul1, h2le, hpos, bpow_gt_0 beta (-prec)]
  have hsmall : bpow beta (ex + ey - 2 * prec) ≤ (1/2) * bpow beta (ex + ey - prec) := by
    have hsplit : bpow beta (ex + ey - 2 * prec)
        = bpow beta (ex + ey - prec) * bpow beta (-prec) := by rw [← bpow_plus]; congr 1; ring
    rw [hsplit]
    calc bpow beta (ex + ey - prec) * bpow beta (-prec)
        ≤ bpow beta (ex + ey - prec) * (1/2) :=
          mul_le_mul_of_nonneg_left hbp (le_of_lt (bpow_gt_0 _ _))
      _ = (1/2) * bpow beta (ex + ey - prec) := by ring
  have hP_pos : (0:ℝ) < bpow beta (ex + ey - prec) := bpow_gt_0 _ _
  linarith [hgap, hxy_ub', hsmall, hP_pos]

/-! ### Boldo §3.2.2: the particular power-of-two cases — geometric setup

When `ulp p ≠ ulp q` (so Lemma 4 does not apply) and the products nearly cancel
(`|p − q| ≤ 2·min(ulp p, ulp q)`), `p` and `q` straddle a power of `β`: with
`q < p` (WLOG), `mag p = mag q + 1` and `q < β^(mag q) ≤ p`. This is the
"`p, q` very near a power of 2" structure Boldo normalizes to `p ≈ 1`; we keep it
at general exponent. The geometric core is general radix. -/

/-- **Straddle lemma** (general radix). In the near-cancellation regime with
distinct ulps, `q < p` straddle a power of `β`: `mag p = mag q + 1` and
`q < β^(mag q) ≤ p`. If `mag p ≥ mag q + 2`, then `p − q > β^(mag q) ≥ 2·ulp q`,
contradicting `|p − q| ≤ 2·ulp q`; distinct ulps rule out `mag p = mag q`. -/
theorem disc_straddle (beta : radix) (prec : ℤ) (hp : 0 < prec) {p q : ℝ}
    (hq_pos : 0 < q) (hqp : q < p)
    (hulp_ne : ulp beta (FLX_exp prec) p ≠ ulp beta (FLX_exp prec) q)
    (hclose : |p - q| ≤ 2 * ulp beta (FLX_exp prec) q) :
    mag beta p = mag beta q + 1
      ∧ q < bpow beta (mag beta q) ∧ bpow beta (mag beta q) ≤ p := by
  have hp_pos : 0 < p := lt_trans hq_pos hqp
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  set mp := mag beta p with hmp
  set mq := mag beta q with hmq
  have hcexp_p : cexp beta (FLX_exp prec) p = mp - prec := by unfold cexp FLX_exp; rw [← hmp]
  have hcexp_q : cexp beta (FLX_exp prec) q = mq - prec := by unfold cexp FLX_exp; rw [← hmq]
  have hulp_p : ulp beta (FLX_exp prec) p = bpow beta (mp - prec) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hp_ne, hcexp_p]
  have hulp_q : ulp beta (FLX_exp prec) q = bpow beta (mq - prec) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq_ne, hcexp_q]
  have hq_ub : q < bpow beta mq := by
    have := bpow_mag_gt beta q; rwa [abs_of_pos hq_pos, ← hmq] at this
  have hp_lb : bpow beta (mp - 1) ≤ p := by
    have := bpow_mag_le beta hp_ne; rwa [abs_of_pos hp_pos, ← hmp] at this
  -- `mag` is monotone, so `mq ≤ mp`; distinct ulps force the inequality strict.
  have hmag_le : mq ≤ mp := by
    have := mag_le_abs beta hq_ne (y := p)
      (by rw [abs_of_pos hq_pos, abs_of_pos hp_pos]; linarith)
    rwa [← hmp, ← hmq] at this
  have hmag_lt : mq < mp := by
    rcases lt_or_eq_of_le hmag_le with h | h
    · exact h
    · exact absurd (by rw [hulp_p, hulp_q, h]) hulp_ne
  -- `2·ulp q ≤ β^(mq)`, since `β^prec ≥ 2`.
  have hβp : (2 : ℝ) ≤ bpow beta prec := by
    calc (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
      _ = bpow beta 1 := (bpow_one beta).symm
      _ ≤ bpow beta prec := bpow_le beta hp
  have hβ2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have h2ulp : 2 * ulp beta (FLX_exp prec) q ≤ bpow beta mq := by
    rw [hulp_q]
    have hsplit : bpow beta mq = bpow beta (mq - prec) * bpow beta prec := by
      rw [← bpow_plus]; congr 1; omega
    have h0 : 0 < bpow beta (mq - prec) := bpow_gt_0 _ _
    calc 2 * bpow beta (mq - prec)
        ≤ bpow beta prec * bpow beta (mq - prec) := mul_le_mul_of_nonneg_right hβp (le_of_lt h0)
      _ = bpow beta mq := by rw [hsplit]; ring
  -- `mp ≤ mq + 1`: else `p − q > β^(mq) ≥ 2·ulp q ≥ |p − q|`.
  have hmag_ub : mp ≤ mq + 1 := by
    by_contra hcon
    push_neg at hcon
    have hp_ge : bpow beta (mq + 1) ≤ p := le_trans (bpow_le beta (by omega)) hp_lb
    have hbig : bpow beta (mq + 1) = bpow beta mq * (beta.val : ℝ) := by rw [bpow_plus, bpow_one]
    have h0 : 0 < bpow beta mq := bpow_gt_0 _ _
    have hdouble : bpow beta mq * 2 ≤ bpow beta (mq + 1) := by rw [hbig]; nlinarith
    have hpq_gt : bpow beta mq < p - q := by linarith [hp_ge, hq_ub, hdouble]
    rw [abs_of_pos (by linarith : (0 : ℝ) < p - q)] at hclose
    linarith [h2ulp, hpq_gt, hclose]
  exact ⟨by omega, hq_ub, le_trans (bpow_le beta (by omega)) hp_lb⟩

/-- If `x` and `y` share a sign (`0 ≤ x·y`) and both have magnitude `≤ H`, then
`|x − y| ≤ H` — the difference cannot exceed the larger magnitude. -/
theorem abs_sub_le_of_same_sign {x y H : ℝ} (hxy : 0 ≤ x * y)
    (hx : |x| ≤ H) (hy : |y| ≤ H) : |x - y| ≤ H := by
  rcases le_or_lt 0 x with hx0 | hx0
  · rcases le_or_lt 0 y with hy0 | hy0
    · rw [abs_of_nonneg hx0] at hx; rw [abs_of_nonneg hy0] at hy
      rw [abs_le]; constructor <;> linarith
    · -- `x ≥ 0`, `y < 0`: `x·y ≤ 0`, so with `0 ≤ x·y` it is `0`, forcing `x = 0`.
      have hxy_le : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 (le_of_lt hy0)
      have hx_eq : x = 0 := by
        rcases mul_eq_zero.mp (le_antisymm hxy_le hxy) with h | h
        · exact h
        · exact absurd h (ne_of_lt hy0)
      rw [hx_eq, zero_sub, abs_neg]; exact hy
  · rcases le_or_lt y 0 with hy0 | hy0
    · rw [abs_of_nonpos (le_of_lt hx0)] at hx; rw [abs_of_nonpos hy0] at hy
      rw [abs_le]; constructor <;> linarith
    · exact absurd hxy (not_le.mpr (mul_neg_of_neg_of_pos hx0 hy0))

/-- **§3.2.2 grid-exactness core** (general radix). In the particular regime, if
the inner difference is small — `|dp − dq| ≤ ulp q` — then `dp − dq` is computed
*exactly*. Both product errors live on the common grid `β^(mag q − 2·prec)`
(coarsened from their product grids via `hgb`, `hgc`), and `ulp q = β^(prec+E)`,
so `disc_diff_on_grid_exact` applies; Lemma 3 (`disc_corr_exact`) then gives
`δ ≤ ½·ulp d ≤ 2·ulp d`. The same-sign / opposite-sign subcases differ only in how
they establish the `|dp − dq| ≤ ulp q` hypothesis. -/
theorem disc_corr_particular_exact (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hq0 : q ≠ 0)
    (hgb : mag beta q ≤ mag beta b + mag beta b)
    (hgc : mag beta q ≤ mag beta a + mag beta c)
    (hbound : |dp - dq| ≤ ulp beta (FLX_exp prec) q) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  suffices hF : generic_format beta (FLX_exp prec) (dp - dq) by
    have h3 := disc_corr_exact beta prec hp choice a b c hdp hdq hg hd hF
    have h0 := ulp_ge_0 beta (FLX_exp prec) d
    linarith
  set E := mag beta q - 2 * prec with hE
  have hcb : cexp beta (FLX_exp prec) b = mag beta b - prec := by unfold cexp FLX_exp; rfl
  have hca : cexp beta (FLX_exp prec) a = mag beta a - prec := by unfold cexp FLX_exp; rfl
  have hcc : cexp beta (FLX_exp prec) c = mag beta c - prec := by unfold cexp FLX_exp; rfl
  obtain ⟨Mdp0, hMdp0⟩ := disc_prod_err_mult_bpow beta prec hp choice Fb Fb
  obtain ⟨Mdq0, hMdq0⟩ := disc_prod_err_mult_bpow beta prec hp choice Fa Fc
  have hdp_eq : dp = (Mdp0 : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b) := by
    rw [hdp, hpe]; exact hMdp0
  have hdq_eq : dq = (Mdq0 : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c) := by
    rw [hdq, hqe]; exact hMdq0
  have hEb : E ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b := by rw [hcb]; omega
  have hEac : E ≤ cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c := by rw [hca, hcc]; omega
  have hdp_E : dp = ((Mdp0 * beta.val
        ^ (cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b - E).toNat : ℤ) : ℝ)
        * bpow beta E := by rw [hdp_eq]; exact disc_bpow_coarsen beta Mdp0 E _ hEb
  have hdq_E : dq = ((Mdq0 * beta.val
        ^ (cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c - E).toNat : ℤ) : ℝ)
        * bpow beta E := by rw [hdq_eq]; exact disc_bpow_coarsen beta Mdq0 E _ hEac
  -- `ulp q = β^(prec+E)`.
  have hbound' : |dp - dq| ≤ bpow beta (prec + E) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq0] at hbound
    have hc : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hc, show mag beta q - prec = prec + E from by omega] at hbound
    exact hbound
  exact disc_diff_on_grid_exact beta prec hp E _ _ hdp_E hdq_E hbound'

/-- **Boldo §3.2.2 subcase (a): same-sign correction is exact** (radix 2).

In the particular (near-power-of-two) regime — `q < p` straddling a power of `β`
(`mag p = mag q + 1`) — if the product errors `dp, dq` share a sign then
`|dp − dq| ≤ ½·ulp p = ulp q`, exactly meeting the grid bound, so `dp − dq` is
exact and `δ ≤ 2·ulp d` by the core. The same-sign hypothesis is what tightens
`|dp − dq|` from `½(ulp p + ulp q)` (too large) down to `½·ulp p`. -/
theorem disc_corr_particular_same_sign (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hq_pos : 0 < q) (hqp : q < p)
    (hmag : mag beta p = mag beta q + 1)
    (hgb : mag beta q ≤ mag beta b + mag beta b)
    (hgc : mag beta q ≤ mag beta a + mag beta c)
    (hsame : 0 ≤ dp * dq) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans hq_pos hqp)
  have hq0 : q ≠ 0 := ne_of_gt hq_pos
  -- `ulp p = 2·ulp q`, hence `½·ulp p = ulp q` (radix 2, `mag p = mag q + 1`).
  have hulp_p_2q : ulp beta (FLX_exp prec) p = 2 * ulp beta (FLX_exp prec) q := by
    rw [ulp_neq_0 beta (FLX_exp prec) hp0, ulp_neq_0 beta (FLX_exp prec) hq0]
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hcp, hcq, hmag, show mag beta q + 1 - prec = (mag beta q - prec) + 1 from by ring,
      bpow_plus, bpow_one, hbeta]; push_cast; ring
  have hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hdp, abs_sub_comm, hpe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [hdq, abs_sub_comm, hqe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  have hdq_le_p : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hulp_p_2q]; have := ulp_ge_0 beta (FLX_exp prec) q; linarith [hdq_bd]
  have hbound : |dp - dq| ≤ ulp beta (FLX_exp prec) q := by
    have h := abs_sub_le_of_same_sign hsame hdp_bd hdq_le_p
    rw [hulp_p_2q] at h; linarith
  exact disc_corr_particular_exact beta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
    hq0 hgb hgc hbound

/-- **Boldo §3.2.2 subcase (b.ii): opposite-sign, `dp − dq ≤ 0`, is exact**
(general radix).

When `dp ≤ 0 ≤ dq` (so `dp − dq ≤ 0`) and `p = β^(mag q)` is the straddled power
of two: `dp ≤ 0` forces `b·b ≤ p = β^(mag q)`, so `mag(b·b) ≤ mag q` and the
*input*-ulp bound gives the sharper `|dp| ≤ ½·ulp(b·b) ≤ ½·ulp q` (vs the generic
`½·ulp p = ulp q`). With `|dq| ≤ ½·ulp q`, the opposite signs give
`|dp − dq| = |dp| + |dq| ≤ ulp q`, and the core closes. -/
theorem disc_corr_particular_opp_neg (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hq0 : q ≠ 0)
    (hp_pow : p = bpow beta (mag beta q))
    (hgb : mag beta q ≤ mag beta b + mag beta b)
    (hgc : mag beta q ≤ mag beta a + mag beta c)
    (hdp_np : dp ≤ 0) (hdq_nn : 0 ≤ dq) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hp_pos : 0 < p := by rw [hp_pow]; exact bpow_gt_0 _ _
  -- `b·b ≠ 0` (else `p = RN 0 = 0`).
  have hbb_ne : b * b ≠ 0 := by
    intro h
    have : p = 0 := by rw [hpe, h, round_0]
    exact (ne_of_gt hp_pos) this
  -- Sharper `|dp| ≤ ½·ulp q` from `dp ≤ 0 ⟹ b·b ≤ β^(mag q)`.
  have hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    by_cases hdp0 : dp = 0
    · rw [hdp0, abs_zero]; have := ulp_ge_0 beta (FLX_exp prec) q; linarith
    · have hbb_pos : 0 < b * b := lt_of_le_of_ne (mul_self_nonneg b) (Ne.symm hbb_ne)
      have hbb_lt : b * b < bpow beta (mag beta q) := by
        rw [← hp_pow]
        rcases lt_or_eq_of_le (by rw [hdp] at hdp_np; linarith : b * b ≤ p) with h | h
        · exact h
        · exact absurd (by rw [hdp, h]; ring) hdp0
      have hmag_bb : mag beta (b * b) ≤ mag beta q :=
        mag_le_bpow beta hbb_ne (by rwa [abs_of_pos hbb_pos])
      have h1 : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) (b * b) := by
        rw [hdp, abs_sub_comm, hpe]
        exact error_le_half_ulp beta (FLX_exp prec) hValid choice (b * b)
      have h2 : ulp beta (FLX_exp prec) (b * b) ≤ ulp beta (FLX_exp prec) q := by
        rw [ulp_neq_0 beta (FLX_exp prec) hbb_ne, ulp_neq_0 beta (FLX_exp prec) hq0]
        have hcbb : cexp beta (FLX_exp prec) (b * b) = mag beta (b * b) - prec := by
          unfold cexp FLX_exp; rfl
        have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
        rw [hcbb, hcq]; exact bpow_le beta (by omega)
      linarith [mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 1/2)]
  -- `|dq| ≤ ½·ulp q`; opposite signs give `|dp − dq| = |dp| + |dq| ≤ ulp q`.
  have hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [hdq, abs_sub_comm, hqe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  have hbound : |dp - dq| ≤ ulp beta (FLX_exp prec) q := by
    have hrw : |dp - dq| = -dp + dq := by
      rw [abs_of_nonpos (by linarith : dp - dq ≤ 0)]; ring
    have e1 : -dp ≤ (1/2) * ulp beta (FLX_exp prec) q := by
      rw [← abs_of_nonpos hdp_np]; exact hdp_bd
    have e2 : dq ≤ (1/2) * ulp beta (FLX_exp prec) q := by
      rw [← abs_of_nonneg hdq_nn]; exact hdq_bd
    rw [hrw]; linarith
  exact disc_corr_particular_exact beta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
    hq0 hgb hgc hbound

/-- **Boldo §3.2.2 subcase (b.i): opposite-sign, `dp − dq ≥ 0`, is within `3/2·ulp d`**
(radix 2).

When `0 ≤ dp`, `dq ≤ 0` (so `dp − dq ≥ 0`): the inner correction is small,
`0 ≤ dp − dq ≤ 3/2·ulp q ≤ 2·ulp q`, so `g = RN(dp − dq) ∈ [0, 2·ulp q]`. The
result `d = RN((p − q) + g) ≥ p − q ≥ ulp q` (monotonicity + `p − q` exact), so
`ulp d ≥ ulp(ulp q)` while `ulp g ≤ ulp(2·ulp q) = 2·ulp(ulp q) ≤ 2·ulp d`. The
decomposition `δ ≤ ½·ulp d + ½·ulp g` then gives `δ ≤ 3/2·ulp d ≤ 2·ulp d`.

This is the one non-exact subcase. Hypotheses `hpqF` (`p − q ∈ F`, from Lemma 1)
and `hpq_ge` (`ulp q ≤ p − q`, the straddle spacing) are provided by context. -/
theorem disc_corr_particular_opp_pos (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hq_pos : 0 < q) (hqp : q < p)
    (hmag : mag beta p = mag beta q + 1)
    (hpqF : generic_format beta (FLX_exp prec) (p - q))
    (hpq_ge : ulp beta (FLX_exp prec) q ≤ p - q)
    (hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p)
    (hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q)
    (hdp_nn : 0 ≤ dp) (hdq_np : dq ≤ 0) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans hq_pos hqp)
  have hq0 : q ≠ 0 := ne_of_gt hq_pos
  have huq_nn : 0 ≤ ulp beta (FLX_exp prec) q := ulp_ge_0 _ _ _
  -- `ulp p = 2·ulp q` (radix 2).
  have hulp_p_2q : ulp beta (FLX_exp prec) p = 2 * ulp beta (FLX_exp prec) q := by
    rw [ulp_neq_0 beta (FLX_exp prec) hp0, ulp_neq_0 beta (FLX_exp prec) hq0]
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hcp, hcq, hmag, show mag beta q + 1 - prec = (mag beta q - prec) + 1 from by ring,
      bpow_plus, bpow_one, hbeta]; push_cast; ring
  -- `0 ≤ dp − dq ≤ 2·ulp q`.
  have hdpdq_nn : 0 ≤ dp - dq := by linarith
  have hdp_le : dp ≤ (1/2) * ulp beta (FLX_exp prec) p := le_trans (le_abs_self _) hdp_bd
  have hndq_le : -dq ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [← abs_of_nonpos hdq_np]; exact hdq_bd
  have hdpdq_le : dp - dq ≤ 2 * ulp beta (FLX_exp prec) q := by
    rw [hulp_p_2q] at hdp_le; linarith
  -- `2·ulp q = β^(mag q − prec + 1) ∈ F`.
  have h2ulpq_eq : 2 * ulp beta (FLX_exp prec) q = bpow beta (mag beta q - prec + 1) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq0]
    have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hcq, show mag beta q - prec + 1 = (mag beta q - prec) + 1 from by ring, bpow_plus,
      bpow_one, hbeta]; push_cast; ring
  have h2ulpq_F : generic_format beta (FLX_exp prec) (2 * ulp beta (FLX_exp prec) q) := by
    rw [h2ulpq_eq]; exact generic_format_bpow beta (FLX_exp prec) _ (by unfold FLX_exp; omega)
  -- `0 ≤ g ≤ 2·ulp q`.
  have hg_nn : 0 ≤ g := by
    rw [hg]
    exact round_ge_generic beta (FLX_exp prec) hValid (Znearest choice)
      (generic_format_0 _ _) hdpdq_nn
  have hg_le : g ≤ 2 * ulp beta (FLX_exp prec) q := by
    rw [hg]
    exact round_le_generic beta (FLX_exp prec) hValid (Znearest choice) h2ulpq_F hdpdq_le
  -- `d ≥ p − q ≥ ulp q`.
  have hd_ge : p - q ≤ d := by
    rw [hd]
    have hmono := round_le beta (FLX_exp prec) hValid (Znearest choice)
      (by linarith : p - q ≤ (p - q) + g)
    have heq := round_generic beta (FLX_exp prec) (Znearest choice) hpqF
    linarith [hmono, heq]
  have hd_nn : 0 ≤ d := by linarith
  -- `ulp g ≤ ulp(2·ulp q) = 2·ulp(ulp q) ≤ 2·ulp d`.
  have hulp_g_le : ulp beta (FLX_exp prec) g
      ≤ ulp beta (FLX_exp prec) (2 * ulp beta (FLX_exp prec) q) := by
    apply ulp_le beta (FLX_exp prec) hValid hMon
    rw [abs_of_nonneg hg_nn, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * ulp beta (FLX_exp prec) q)]
    exact hg_le
  have hulp2 := ulp_two_mul_r2 beta hbeta prec hp (ulp beta (FLX_exp prec) q)
  have hulp_uq_d : ulp beta (FLX_exp prec) (ulp beta (FLX_exp prec) q)
      ≤ ulp beta (FLX_exp prec) d := by
    apply ulp_le beta (FLX_exp prec) hValid hMon
    rw [abs_of_nonneg huq_nn, abs_of_nonneg hd_nn]
    exact le_trans hpq_ge hd_ge
  have hulp_g_2d : ulp beta (FLX_exp prec) g ≤ 2 * ulp beta (FLX_exp prec) d := by
    rw [hulp2] at hulp_g_le; linarith
  -- `δ ≤ ½·ulp d + ½·ulp g ≤ 3/2·ulp d ≤ 2·ulp d`.
  have hdecomp := disc_corr_err_decomp beta prec hp choice a b c hdp hdq hg hd
  have hud := ulp_ge_0 beta (FLX_exp prec) d
  linarith [hdecomp, hulp_g_2d, hud]

/-! ### Boldo §3.2.2 — the mirror orientation `p < q`

The three subcases above assume `q < p` (Boldo's WLOG `p ≥ q`). In our *functional*
rounding setting that WLOG is not free: the swap `(p, dp) ↔ (q, dq)` only flips the
algorithm's result to `−d` under a *flipped* tie-breaker, and negating the (positive)
products leaves the positive regime. So the `p < q` orientation — which the square
discriminant genuinely reaches (e.g. `p = 7`, `q = 8`) — needs its own mirror. The
geometry (`disc_straddle`, `disc_particular_p_pow2`) is polymorphic in `{p q}` and
reused by swapped instantiation; only the three sign-subcases are mirrored here.
Now `q` is the larger product and the straddled power of two is `q = β^(mag p)`. -/

/-- **Mirror subcase (a): same-sign correction is exact** (`p < q`, radix 2).
Symmetric to `disc_corr_particular_same_sign`: `|dp − dq| ≤ ½·ulp q = ulp p`
(the smaller product `p` is the reference grid), so `dp − dq` is exact. -/
theorem disc_corr_particular_same_sign_lo (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hp_pos : 0 < p) (hpq : p < q)
    (hmag : mag beta q = mag beta p + 1)
    (hgb : mag beta p ≤ mag beta b + mag beta b)
    (hgc : mag beta p ≤ mag beta a + mag beta c)
    (hsame : 0 ≤ dp * dq) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hp0 : p ≠ 0 := ne_of_gt hp_pos
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans hp_pos hpq)
  -- `ulp q = 2·ulp p` (radix 2, `mag q = mag p + 1`).
  have hulp_q_2p : ulp beta (FLX_exp prec) q = 2 * ulp beta (FLX_exp prec) p := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq0, ulp_neq_0 beta (FLX_exp prec) hp0]
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hcq, hcp, hmag, show mag beta p + 1 - prec = (mag beta p - prec) + 1 from by ring,
      bpow_plus, bpow_one, hbeta]; push_cast; ring
  have hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hdp, abs_sub_comm, hpe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [hdq, abs_sub_comm, hqe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  have hdp_le_p : |dp| ≤ ulp beta (FLX_exp prec) p := by
    have := ulp_ge_0 beta (FLX_exp prec) p; linarith [hdp_bd]
  have hdq_le_p : |dq| ≤ ulp beta (FLX_exp prec) p := by
    rw [hulp_q_2p] at hdq_bd; linarith [hdq_bd]
  have hbound_ulp : |dp - dq| ≤ ulp beta (FLX_exp prec) p :=
    abs_sub_le_of_same_sign hsame hdp_le_p hdq_le_p
  set E := mag beta p - 2 * prec with hE
  have hbound : |dp - dq| ≤ bpow beta (prec + E) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hp0] at hbound_ulp
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    rw [hcp, show mag beta p - prec = prec + E from by omega] at hbound_ulp
    exact hbound_ulp
  have hcb : cexp beta (FLX_exp prec) b = mag beta b - prec := by unfold cexp FLX_exp; rfl
  have hca : cexp beta (FLX_exp prec) a = mag beta a - prec := by unfold cexp FLX_exp; rfl
  have hcc : cexp beta (FLX_exp prec) c = mag beta c - prec := by unfold cexp FLX_exp; rfl
  have hEb : E ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b := by rw [hcb]; omega
  have hEac : E ≤ cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c := by rw [hca, hcc]; omega
  have hF := disc_inner_exact beta prec hp choice Fa Fb Fc hpe hqe hdp hdq E hEb hEac hbound
  have h3 := disc_corr_exact beta prec hp choice a b c hdp hdq hg hd hF
  have h0 := ulp_ge_0 beta (FLX_exp prec) d
  linarith

/-- **Mirror subcase (exact): opposite-sign, `dp − dq ≥ 0`, is exact** (`p < q`,
general radix). Here `q = β^(mag p)` is the straddled power of two (the *larger*
product). `dq ≤ 0` forces `a·c ≤ q = β^(mag p)`, and `a·c > 0` (since `q = RN(a·c) > 0`
by round-monotonicity — no squareness needed, unlike the `q < p` orientation where it
came free from `b·b`), so `mag(a·c) ≤ mag p` and the *input*-ulp bound gives the sharper
`|dq| ≤ ½·ulp p`. With `|dp| ≤ ½·ulp p`, opposite signs give `|dp − dq| ≤ ulp p`. -/
theorem disc_corr_particular_opp_pos_lo (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hp0 : p ≠ 0)
    (hq_pow : q = bpow beta (mag beta p))
    (hgb : mag beta p ≤ mag beta b + mag beta b)
    (hgc : mag beta p ≤ mag beta a + mag beta c)
    (hdp_nn : 0 ≤ dp) (hdq_np : dq ≤ 0) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hq_pos : 0 < q := by rw [hq_pow]; exact bpow_gt_0 _ _
  have hq0 : q ≠ 0 := ne_of_gt hq_pos
  -- `a·c > 0` (else `q = RN(a·c) ≤ RN 0 = 0`).
  have hac_pos : 0 < a * c := by
    by_contra h; push_neg at h
    have hqle : q ≤ 0 := by
      rw [hqe]
      calc round beta (FLX_exp prec) (Znearest choice) (a * c)
          ≤ round beta (FLX_exp prec) (Znearest choice) 0 :=
            round_le beta (FLX_exp prec) hValid (Znearest choice) h
        _ = 0 := round_0 beta (FLX_exp prec) (Znearest choice)
    linarith
  -- Sharper `|dq| ≤ ½·ulp p` from `dq ≤ 0 ⟹ a·c ≤ β^(mag p)`.
  have hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    by_cases hdq0 : dq = 0
    · rw [hdq0, abs_zero]; have := ulp_ge_0 beta (FLX_exp prec) p; linarith
    · have hac_lt : a * c < bpow beta (mag beta p) := by
        rw [← hq_pow]
        rcases lt_or_eq_of_le (by rw [hdq] at hdq_np; linarith : a * c ≤ q) with h | h
        · exact h
        · exact absurd (by rw [hdq, h]; ring) hdq0
      have hac_ne : a * c ≠ 0 := ne_of_gt hac_pos
      have hmag_ac : mag beta (a * c) ≤ mag beta p :=
        mag_le_bpow beta hac_ne (by rwa [abs_of_pos hac_pos])
      have h1 : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) (a * c) := by
        rw [hdq, abs_sub_comm, hqe]
        exact error_le_half_ulp beta (FLX_exp prec) hValid choice (a * c)
      have h2 : ulp beta (FLX_exp prec) (a * c) ≤ ulp beta (FLX_exp prec) p := by
        rw [ulp_neq_0 beta (FLX_exp prec) hac_ne, ulp_neq_0 beta (FLX_exp prec) hp0]
        have hcac : cexp beta (FLX_exp prec) (a * c) = mag beta (a * c) - prec := by
          unfold cexp FLX_exp; rfl
        have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
        rw [hcac, hcp]; exact bpow_le beta (by omega)
      linarith [mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 1/2)]
  have hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hdp, abs_sub_comm, hpe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have hbound_ulp : |dp - dq| ≤ ulp beta (FLX_exp prec) p := by
    have hrw : |dp - dq| = dp + (-dq) := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ dp - dq)]; ring
    have e1 : dp ≤ (1/2) * ulp beta (FLX_exp prec) p := le_trans (le_abs_self _) hdp_bd
    have e2 : -dq ≤ (1/2) * ulp beta (FLX_exp prec) p := by
      rw [← abs_of_nonpos hdq_np]; exact hdq_bd
    rw [hrw]; linarith
  set E := mag beta p - 2 * prec with hE
  have hbound : |dp - dq| ≤ bpow beta (prec + E) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hp0] at hbound_ulp
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    rw [hcp, show mag beta p - prec = prec + E from by omega] at hbound_ulp
    exact hbound_ulp
  have hcb : cexp beta (FLX_exp prec) b = mag beta b - prec := by unfold cexp FLX_exp; rfl
  have hca : cexp beta (FLX_exp prec) a = mag beta a - prec := by unfold cexp FLX_exp; rfl
  have hcc : cexp beta (FLX_exp prec) c = mag beta c - prec := by unfold cexp FLX_exp; rfl
  have hEb : E ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b := by rw [hcb]; omega
  have hEac : E ≤ cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c := by rw [hca, hcc]; omega
  have hF := disc_inner_exact beta prec hp choice Fa Fb Fc hpe hqe hdp hdq E hEb hEac hbound
  have h3 := disc_corr_exact beta prec hp choice a b c hdp hdq hg hd hF
  have h0 := ulp_ge_0 beta (FLX_exp prec) d
  linarith

/-- **Mirror subcase (magnitude): opposite-sign, `dp − dq ≤ 0`, within `3/2·ulp d`**
(`p < q`, radix 2). The mirror of `disc_corr_particular_opp_pos`: `dp ≤ 0 ≤ dq`, so
`g = RN(dp − dq) ∈ [−2·ulp p, 0]`; `d ≤ p − q ≤ −ulp p` so `|d| ≥ ulp p`, hence
`ulp g ≤ ulp(2·ulp p) = 2·ulp(ulp p) ≤ 2·ulp d` and `δ ≤ 3/2·ulp d ≤ 2·ulp d`. -/
theorem disc_corr_particular_opp_neg_lo (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq g d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hp_pos : 0 < p) (hpq : p < q)
    (hmag : mag beta q = mag beta p + 1)
    (hpqF : generic_format beta (FLX_exp prec) (p - q))
    (hpq_ge : ulp beta (FLX_exp prec) p ≤ q - p)
    (hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p)
    (hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q)
    (hdp_np : dp ≤ 0) (hdq_nn : 0 ≤ dq) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hp0 : p ≠ 0 := ne_of_gt hp_pos
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans hp_pos hpq)
  have hup_nn : 0 ≤ ulp beta (FLX_exp prec) p := ulp_ge_0 _ _ _
  -- `ulp q = 2·ulp p` (radix 2).
  have hulp_q_2p : ulp beta (FLX_exp prec) q = 2 * ulp beta (FLX_exp prec) p := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq0, ulp_neq_0 beta (FLX_exp prec) hp0]
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hcq, hcp, hmag, show mag beta p + 1 - prec = (mag beta p - prec) + 1 from by ring,
      bpow_plus, bpow_one, hbeta]; push_cast; ring
  -- `−2·ulp p ≤ dp − dq ≤ 0`.
  have hdpdq_np : dp - dq ≤ 0 := by linarith
  have hndp_le : -dp ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [← abs_of_nonpos hdp_np]; exact hdp_bd
  have hdq_le : dq ≤ (1/2) * ulp beta (FLX_exp prec) q := le_trans (le_abs_self _) hdq_bd
  have hdpdq_ge : -(2 * ulp beta (FLX_exp prec) p) ≤ dp - dq := by
    rw [hulp_q_2p] at hdq_le; linarith
  -- `2·ulp p = β^(mag p − prec + 1) ∈ F`, and its negation.
  have h2ulpp_eq : 2 * ulp beta (FLX_exp prec) p = bpow beta (mag beta p - prec + 1) := by
    rw [ulp_neq_0 beta (FLX_exp prec) hp0]
    have hcp : cexp beta (FLX_exp prec) p = mag beta p - prec := by unfold cexp FLX_exp; rfl
    rw [hcp, show mag beta p - prec + 1 = (mag beta p - prec) + 1 from by ring, bpow_plus,
      bpow_one, hbeta]; push_cast; ring
  have h2ulpp_F : generic_format beta (FLX_exp prec) (2 * ulp beta (FLX_exp prec) p) := by
    rw [h2ulpp_eq]; exact generic_format_bpow beta (FLX_exp prec) _ (by unfold FLX_exp; omega)
  have hneg2ulpp_F : generic_format beta (FLX_exp prec) (-(2 * ulp beta (FLX_exp prec) p)) :=
    generic_format_opp beta (FLX_exp prec) h2ulpp_F
  -- `−2·ulp p ≤ g ≤ 0`.
  have hg_np : g ≤ 0 := by
    rw [hg]
    exact round_le_generic beta (FLX_exp prec) hValid (Znearest choice)
      (generic_format_0 _ _) hdpdq_np
  have hg_ge : -(2 * ulp beta (FLX_exp prec) p) ≤ g := by
    rw [hg]
    exact round_ge_generic beta (FLX_exp prec) hValid (Znearest choice) hneg2ulpp_F hdpdq_ge
  -- `d ≤ p − q ≤ −ulp p`, so `|d| ≥ ulp p`.
  have hd_le : d ≤ p - q := by
    rw [hd]
    have hmono := round_le beta (FLX_exp prec) hValid (Znearest choice)
      (by linarith : (p - q) + g ≤ p - q)
    have heq := round_generic beta (FLX_exp prec) (Znearest choice) hpqF
    linarith [hmono, heq]
  have hd_np : d ≤ -ulp beta (FLX_exp prec) p := by linarith [hd_le, hpq_ge]
  have hd_neg : d ≤ 0 := by linarith [hup_nn]
  have hd_abs : ulp beta (FLX_exp prec) p ≤ |d| := by
    rw [abs_of_nonpos hd_neg]; linarith [hd_np]
  -- `ulp g ≤ ulp(2·ulp p) = 2·ulp(ulp p) ≤ 2·ulp d`.
  have hg_abs : |g| ≤ 2 * ulp beta (FLX_exp prec) p := by
    rw [abs_of_nonpos hg_np]; linarith [hg_ge]
  have hulp_g_le : ulp beta (FLX_exp prec) g
      ≤ ulp beta (FLX_exp prec) (2 * ulp beta (FLX_exp prec) p) := by
    apply ulp_le beta (FLX_exp prec) hValid hMon
    rw [abs_of_nonneg (by linarith [hup_nn] : (0:ℝ) ≤ 2 * ulp beta (FLX_exp prec) p)]
    exact hg_abs
  have hulp2 := ulp_two_mul_r2 beta hbeta prec hp (ulp beta (FLX_exp prec) p)
  have hulp_up_d : ulp beta (FLX_exp prec) (ulp beta (FLX_exp prec) p)
      ≤ ulp beta (FLX_exp prec) d := by
    apply ulp_le beta (FLX_exp prec) hValid hMon
    rw [abs_of_nonneg hup_nn]
    exact hd_abs
  have hulp_g_2d : ulp beta (FLX_exp prec) g ≤ 2 * ulp beta (FLX_exp prec) d := by
    rw [hulp2] at hulp_g_le; linarith
  have hdecomp := disc_corr_err_decomp beta prec hp choice a b c hdp hdq hg hd
  have hud := ulp_ge_0 beta (FLX_exp prec) d
  linarith [hdecomp, hulp_g_2d, hud]

/-! ### Boldo §3.2.2 assembly

In the particular regime — correction branch, `q < p`, distinct ulps, and the
near-cancellation `p − q ≤ 2·ulp q` — `p` is exactly the straddled power of two
`β^(mag q)`, and `p − q ≥ ulp q`. Combined with the straddle (`mag p = mag q + 1`)
and `p − q ∈ F` (Lemma 1), this supplies every structural fact the three subcases
need; dispatching on the signs of `dp, dq` then closes all of §3.2.2. -/

/-- **`p` is the straddled power of two** (radix 2). In the particular regime, `p`
is the unique float in `[β^(mag q), β^(mag q) + ulp q]` with `mag p = mag q + 1`,
namely `β^(mag q)`: the next float above `β^(mag q)` is `β^(mag q) + 2·ulp q`, which
exceeds the upper bound `β^(mag q) + ulp q`. -/
theorem disc_particular_p_pow2 (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    {p q : ℝ}
    (Fp : generic_format beta (FLX_exp prec) p)
    (Fq : generic_format beta (FLX_exp prec) q)
    (hq_pos : 0 < q) (hqp : q < p)
    (hmag : mag beta p = mag beta q + 1)
    (hclose : p - q ≤ 2 * ulp beta (FLX_exp prec) q) :
    p = bpow beta (mag beta q) := by
  have hValid := FLX_exp_valid prec hp
  have hp_pos : 0 < p := lt_trans hq_pos hqp
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hulp_pos : 0 < ulp beta (FLX_exp prec) q := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq_ne]; exact bpow_gt_0 _ _
  -- `β^(mag q) ≤ p` (from `mag p = mag q + 1`).
  have hpow_le_p : bpow beta (mag beta q) ≤ p := by
    have h := bpow_mag_le beta (ne_of_gt hp_pos)
    rw [abs_of_pos hp_pos, hmag, show mag beta q + 1 - 1 = mag beta q from by ring] at h
    exact h
  -- `q + ulp q ≤ β^(mag q)`, so `p ≤ β^(mag q) + ulp q`.
  have hq_lt : q < bpow beta (mag beta q) := by
    have := bpow_mag_gt beta q; rwa [abs_of_pos hq_pos] at this
  have hq_ulp : q + ulp beta (FLX_exp prec) q ≤ bpow beta (mag beta q) :=
    id_p_ulp_le_bpow beta (FLX_exp prec) hq_pos Fq hq_lt
  have hp_ub : p ≤ bpow beta (mag beta q) + ulp beta (FLX_exp prec) q := by linarith [hclose, hq_ulp]
  -- If `p ≠ β^(mag q)`, the successor `β^(mag q) + 2·ulp q ≤ p` contradicts the upper bound.
  by_contra hne
  have hlt : bpow beta (mag beta q) < p := lt_of_le_of_ne hpow_le_p (Ne.symm hne)
  have hFpow : generic_format beta (FLX_exp prec) (bpow beta (mag beta q)) :=
    generic_format_bpow beta (FLX_exp prec) (mag beta q) (by unfold FLX_exp; omega)
  have hsucc_le := succ_le_lt_aux beta (FLX_exp prec) hValid hFpow Fp
    (le_of_lt (bpow_gt_0 _ _)) hlt
  rw [succ_eq_pos beta (FLX_exp prec) (le_of_lt (bpow_gt_0 _ _))] at hsucc_le
  have hulp_pow : ulp beta (FLX_exp prec) (bpow beta (mag beta q))
      = 2 * ulp beta (FLX_exp prec) q := by
    rw [ulp_bpow, ulp_neq_0 beta (FLX_exp prec) hq_ne]
    have hcq : cexp beta (FLX_exp prec) q = mag beta q - prec := by unfold cexp FLX_exp; rfl
    rw [hcq, show FLX_exp prec (mag beta q + 1) = (mag beta q - prec) + 1 from by unfold FLX_exp; ring,
      bpow_plus, bpow_one, hbeta]; push_cast; ring
  rw [hulp_pow] at hsucc_le
  linarith [hsucc_le, hp_ub, hulp_pos]

/-- **§3.2.2 assembled: the particular case is within `2·ulp d`** (radix 2).

Correction branch (`3|p − q| < p + q`), `q < p`, distinct ulps, near cancellation
(`p − q ≤ 2·ulp q`). The straddle gives `mag p = mag q + 1`; `p = β^(mag q)` (the
power of two); `p − q ∈ F` (Lemma 1) and `p − q ≥ ulp q` (spacing). Dispatching on
`sign(dp·dq)` routes into the three subcases — same-sign (a), opposite/`dp−dq≥0`
(b.i), opposite/`dp−dq≤0` (b.ii). The grid bounds `hgb`, `hgc` are passed through.

`a, b, c` are floats; `dp, dq` are the (exact) product errors. -/
theorem disc_corr_particular (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hq_pos : 0 < q) (hqp : q < p)
    (hulp_ne : ulp beta (FLX_exp prec) p ≠ ulp beta (FLX_exp prec) q)
    (hclose : p - q ≤ 2 * ulp beta (FLX_exp prec) q)
    (hbranch : 3 * |p - q| < p + q) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hp_pos : 0 < p := lt_trans hq_pos hqp
  have hq0 : q ≠ 0 := ne_of_gt hq_pos
  have Fp : generic_format beta (FLX_exp prec) p := by
    rw [hpe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  have Fq : generic_format beta (FLX_exp prec) q := by
    rw [hqe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  have habs : |p - q| = p - q := abs_of_nonneg (by linarith)
  -- Straddle: `mag p = mag q + 1`; then `p = β^(mag q)`.
  obtain ⟨hmag, -, -⟩ := disc_straddle beta prec hp hq_pos hqp hulp_ne
    (by rw [habs]; exact hclose)
  have hp_pow : p = bpow beta (mag beta q) :=
    disc_particular_p_pow2 beta hbeta prec hp Fp Fq hq_pos hqp hmag hclose
  -- `p − q ∈ F` (Lemma 1) and `p − q ≥ ulp q`.
  have hpqF : generic_format beta (FLX_exp prec) (p - q) :=
    disc_branch_subtract_exact beta prec hp Fp Fq (le_of_lt hp_pos) hbranch
  have hpq_ge : ulp beta (FLX_exp prec) q ≤ p - q := by
    have hq_lt : q < bpow beta (mag beta q) := by
      have := bpow_mag_gt beta q; rwa [abs_of_pos hq_pos] at this
    have hq_ulp := id_p_ulp_le_bpow beta (FLX_exp prec) hq_pos Fq hq_lt
    rw [hp_pow]; linarith
  -- Grid discharge (unconditional, via the no-bump keystone): `hgb` cross, `hgc` direct.
  have hbb_pos : 0 < b * b := by
    rcases (mul_self_nonneg b).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hpe, ← h, round_0] at hp_pos; exact lt_irrefl 0 hp_pos
  have hac_pos : 0 < a * c := by
    by_contra h; push_neg at h
    have hqle : q ≤ 0 := by
      rw [hqe]
      calc round beta (FLX_exp prec) (Znearest choice) (a * c)
          ≤ round beta (FLX_exp prec) (Znearest choice) 0 :=
            round_le beta (FLX_exp prec) hValid (Znearest choice) h
        _ = 0 := round_0 beta (FLX_exp prec) (Znearest choice)
    linarith
  have hgb : mag beta q ≤ mag beta b + mag beta b := by
    have h := disc_mag_prod_no_bump beta prec hp choice Fb Fb hbb_pos
    rw [← hpe] at h; omega
  have hgc : mag beta q ≤ mag beta a + mag beta c := by
    have h := disc_mag_prod_no_bump beta prec hp choice Fa Fc hac_pos
    rw [← hqe] at h; exact h
  -- Trivial half-ulp bounds.
  have hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hdp, abs_sub_comm, hpe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [hdq, abs_sub_comm, hqe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  -- Dispatch on the sign of `dp · dq`.
  rcases le_or_lt 0 (dp * dq) with hsame | hopp
  · exact disc_corr_particular_same_sign beta hbeta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
      hq_pos hqp hmag hgb hgc hsame
  · rcases le_or_lt 0 dp with hdp_nn | hdp_neg
    · -- `dp ≥ 0`, `dq < 0` ⟹ subcase (b.i).
      have hdq_np : dq ≤ 0 := by
        by_contra h; push_neg at h; exact absurd (mul_nonneg hdp_nn (le_of_lt h)) (not_le.mpr hopp)
      exact disc_corr_particular_opp_pos beta hbeta prec hp choice a b c hdp hdq hg hd
        hq_pos hqp hmag hpqF hpq_ge hdp_bd hdq_bd hdp_nn hdq_np
    · -- `dp < 0`, `dq > 0` ⟹ subcase (b.ii).
      have hdq_nn : 0 ≤ dq := by
        by_contra h; push_neg at h
        exact absurd (mul_nonneg (le_of_lt (neg_pos.mpr hdp_neg)) (le_of_lt (neg_pos.mpr h)))
          (by rw [neg_mul_neg]; exact not_le.mpr hopp)
      exact disc_corr_particular_opp_neg beta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
        hq0 hp_pow hgb hgc (le_of_lt hdp_neg) hdq_nn

/-- **§3.2.2 assembled, mirror orientation** (`0 < p < q`, radix 2).

The `p < q` counterpart of `disc_corr_particular`. Boldo's WLOG `p ≥ q` covers only
the `q < p` orientation in our functional setting; here `q` is the larger product and
the straddled power of two is `q = β^(mag p)`. The geometry (`disc_straddle`,
`disc_particular_p_pow2`) is reused by swapped instantiation, and the sign dispatch
routes into the three mirror subcases (`_lo`). `q − p ≥ ulp p` is the mirror spacing. -/
theorem disc_corr_particular_lo (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hp_pos : 0 < p) (hpq : p < q)
    (hulp_ne : ulp beta (FLX_exp prec) p ≠ ulp beta (FLX_exp prec) q)
    (hclose : q - p ≤ 2 * ulp beta (FLX_exp prec) p)
    (hbranch : 3 * |p - q| < p + q) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have hp0 : p ≠ 0 := ne_of_gt hp_pos
  have Fp : generic_format beta (FLX_exp prec) p := by
    rw [hpe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  have Fq : generic_format beta (FLX_exp prec) q := by
    rw [hqe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  -- Straddle (swapped instantiation): `mag q = mag p + 1`; then `q = β^(mag p)`.
  obtain ⟨hmag, -, -⟩ := disc_straddle beta prec hp (p := q) (q := p) hp_pos hpq
    hulp_ne.symm (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ q - p)]; exact hclose)
  have hq_pow : q = bpow beta (mag beta p) :=
    disc_particular_p_pow2 beta hbeta prec hp Fq Fp hp_pos hpq hmag hclose
  -- `p − q ∈ F` (Lemma 1) and `q − p ≥ ulp p`.
  have hpqF : generic_format beta (FLX_exp prec) (p - q) :=
    disc_branch_subtract_exact beta prec hp Fp Fq (le_of_lt hp_pos) hbranch
  have hpq_ge : ulp beta (FLX_exp prec) p ≤ q - p := by
    have hp_lt : p < bpow beta (mag beta p) := by
      have := bpow_mag_gt beta p; rwa [abs_of_pos hp_pos] at this
    have hp_ulp := id_p_ulp_le_bpow beta (FLX_exp prec) hp_pos Fp hp_lt
    rw [hq_pow]; linarith
  -- Grid discharge (unconditional, via the no-bump keystone): `hgb` direct, `hgc` cross.
  have hbb_pos : 0 < b * b := by
    rcases (mul_self_nonneg b).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hpe, ← h, round_0] at hp_pos; exact lt_irrefl 0 hp_pos
  have hq_pos : 0 < q := lt_trans hp_pos hpq
  have hac_pos : 0 < a * c := by
    by_contra h; push_neg at h
    have hqle : q ≤ 0 := by
      rw [hqe]
      calc round beta (FLX_exp prec) (Znearest choice) (a * c)
          ≤ round beta (FLX_exp prec) (Znearest choice) 0 :=
            round_le beta (FLX_exp prec) hValid (Znearest choice) h
        _ = 0 := round_0 beta (FLX_exp prec) (Znearest choice)
    linarith
  have hgb : mag beta p ≤ mag beta b + mag beta b := by
    have h := disc_mag_prod_no_bump beta prec hp choice Fb Fb hbb_pos
    rw [← hpe] at h; exact h
  have hgc : mag beta p ≤ mag beta a + mag beta c := by
    have h := disc_mag_prod_no_bump beta prec hp choice Fa Fc hac_pos
    rw [← hqe] at h; omega
  -- Trivial half-ulp bounds.
  have hdp_bd : |dp| ≤ (1/2) * ulp beta (FLX_exp prec) p := by
    rw [hdp, abs_sub_comm, hpe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (b * b)
  have hdq_bd : |dq| ≤ (1/2) * ulp beta (FLX_exp prec) q := by
    rw [hdq, abs_sub_comm, hqe]
    exact error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice (a * c)
  -- Dispatch on the sign of `dp · dq`.
  rcases le_or_lt 0 (dp * dq) with hsame | hopp
  · exact disc_corr_particular_same_sign_lo beta hbeta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
      hp_pos hpq hmag hgb hgc hsame
  · rcases le_or_lt 0 dp with hdp_nn | hdp_neg
    · -- `dp ≥ 0`, `dq < 0` ⟹ exact subcase.
      have hdq_np : dq ≤ 0 := by
        by_contra h; push_neg at h; exact absurd (mul_nonneg hdp_nn (le_of_lt h)) (not_le.mpr hopp)
      exact disc_corr_particular_opp_pos_lo beta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
        hp0 hq_pow hgb hgc hdp_nn hdq_np
    · -- `dp < 0`, `dq > 0` ⟹ magnitude subcase.
      have hdq_nn : 0 ≤ dq := by
        by_contra h; push_neg at h
        exact absurd (mul_nonneg (le_of_lt (neg_pos.mpr hdp_neg)) (le_of_lt (neg_pos.mpr h)))
          (by rw [neg_mul_neg]; exact not_le.mpr hopp)
      exact disc_corr_particular_opp_neg_lo beta hbeta prec hp choice a b c hdp hdq hg hd
        hp_pos hpq hmag hpqF hpq_ge hdp_bd hdq_bd (le_of_lt hdp_neg) hdq_nn

/-! ### Boldo §3 — the full correction dispatch

The correction branch (`3|p − q| < p + q`, `p ≠ q`) splits — after `p = q` (handled
by `disc_corr_pq_eq`) — on the ulps of `p` and `q`:
- `ulp p = ulp q` → Lemma 4 (`disc_corr_lemma4`);
- distinct ulps, far (`ulp p + ulp q ≤ |p − q|`) → `disc_corr_far`;
- distinct ulps, near → the §3.2.2 particular case, oriented by `q < p` (case A,
  `disc_corr_particular`) or `p < q` (case B, `disc_corr_particular_lo`).

The two structural facts the dispatch must supply to the particular cases are the
*tight* gap bound `p − q ≤ 2·ulp(min)` (the "not-far" test only gives `< 3·ulp(min)`)
and the grid bounds on `mag(min p q)`. Both are proved here. -/

/-- **Tight gap in the distinct-ulp near regime.** With `q < p`, distinct ulps, and
`p ≤ 2q` (Lemma 1), `mag p = mag q + 1` so `ulp p = 2·ulp q`. If moreover the gap is
not "far" (`p − q < ulp p + ulp q = 3·ulp q`), then `p − q ≤ 2·ulp q`: writing both
floats over the common grid `β^(cexp q)` (with `cexp p = cexp q + 1`), `p − q` is an
integer multiple of `ulp q` strictly below `3·ulp q`. Radix 2. -/
theorem disc_gap_le_two_ulp (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    {p q : ℝ}
    (Fp : generic_format beta (FLX_exp prec) p)
    (Fq : generic_format beta (FLX_exp prec) q)
    (hq_pos : 0 < q) (hqp : q < p)
    (hulp_ne : ulp beta (FLX_exp prec) p ≠ ulp beta (FLX_exp prec) q)
    (hp_le : p ≤ 2 * q)
    (hnotfar : p - q < ulp beta (FLX_exp prec) p + ulp beta (FLX_exp prec) q) :
    p - q ≤ 2 * ulp beta (FLX_exp prec) q := by
  have hp_pos : 0 < p := lt_trans hq_pos hqp
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  set mp := mag beta p with hmp
  set mq := mag beta q with hmq
  have hcp0 : cexp beta (FLX_exp prec) p = mp - prec := by unfold cexp FLX_exp; rw [← hmp]
  have hcq0 : cexp beta (FLX_exp prec) q = mq - prec := by unfold cexp FLX_exp; rw [← hmq]
  -- `mag p = mag q + 1`.
  have hq_ub : q < bpow beta mq := by
    have := bpow_mag_gt beta q; rwa [abs_of_pos hq_pos, ← hmq] at this
  have hmag_le : mq ≤ mp := by
    have := mag_le_abs beta hq_ne (y := p)
      (by rw [abs_of_pos hq_pos, abs_of_pos hp_pos]; linarith)
    rwa [← hmp, ← hmq] at this
  have hmag_lt : mq < mp := by
    rcases lt_or_eq_of_le hmag_le with h | h
    · exact h
    · exact absurd (by rw [ulp_neq_0 beta (FLX_exp prec) hp_ne,
        ulp_neq_0 beta (FLX_exp prec) hq_ne, hcp0, hcq0, h]) hulp_ne
  have hp_lt2 : p < bpow beta (mq + 1) := by
    have hd : bpow beta (mq + 1) = 2 * bpow beta mq := by
      rw [bpow_plus, bpow_one, hbeta]; push_cast; ring
    rw [hd]; linarith [hp_le, hq_ub]
  have hmag_ub : mp ≤ mq + 1 := by
    have := mag_le_bpow beta hp_ne (show |p| < bpow beta (mq + 1) by rwa [abs_of_pos hp_pos])
    rwa [← hmp] at this
  have hmag : mp = mq + 1 := by omega
  -- `cexp p = cexp q + 1`; both floats over the common grid `u = β^(cexp q)`.
  have hcpq : cexp beta (FLX_exp prec) p = cexp beta (FLX_exp prec) q + 1 := by
    rw [hcp0, hcq0, hmag]; ring
  have huq : ulp beta (FLX_exp prec) q = bpow beta (cexp beta (FLX_exp prec) q) :=
    ulp_neq_0 beta (FLX_exp prec) hq_ne
  have hup : ulp beta (FLX_exp prec) p = bpow beta (cexp beta (FLX_exp prec) p) :=
    ulp_neq_0 beta (FLX_exp prec) hp_ne
  have hbpow_cp : bpow beta (cexp beta (FLX_exp prec) p)
      = 2 * bpow beta (cexp beta (FLX_exp prec) q) := by
    rw [hcpq, bpow_plus, bpow_one, hbeta]; push_cast; ring
  have hpm : p = ((Ztrunc (scaled_mantissa beta (FLX_exp prec) p) : ℤ) : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) p) := by
    have h := Fp; unfold generic_format F2R at h; exact h
  have hqm : q = ((Ztrunc (scaled_mantissa beta (FLX_exp prec) q) : ℤ) : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) q) := by
    have h := Fq; unfold generic_format F2R at h; exact h
  set Mp := (Ztrunc (scaled_mantissa beta (FLX_exp prec) p) : ℤ) with hMpdef
  set Mq := (Ztrunc (scaled_mantissa beta (FLX_exp prec) q) : ℤ) with hMqdef
  set u := bpow beta (cexp beta (FLX_exp prec) q) with hu
  have hu_pos : 0 < u := bpow_gt_0 _ _
  have hgap : p - q = ((2 * Mp - Mq : ℤ) : ℝ) * u := by
    rw [hpm, hqm, hbpow_cp]; push_cast; ring
  -- the integer `k = 2 Mp − Mq` lies in `{1, 2}`.
  have hkr_pos : 0 < ((2 * Mp - Mq : ℤ) : ℝ) := by
    by_contra h; push_neg at h
    have hle : ((2 * Mp - Mq : ℤ) : ℝ) * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hu_pos)
    rw [← hgap] at hle; linarith
  have h3u : ulp beta (FLX_exp prec) p + ulp beta (FLX_exp prec) q = 3 * u := by
    rw [hup, hbpow_cp, huq]; ring
  have hkr_lt : ((2 * Mp - Mq : ℤ) : ℝ) < 3 := by
    rw [h3u, hgap] at hnotfar
    exact lt_of_mul_lt_mul_right (by linarith [hnotfar]) (le_of_lt hu_pos)
  have hk_le : (2 * Mp - Mq : ℤ) ≤ 2 := by
    have : (2 * Mp - Mq : ℤ) < 3 := by exact_mod_cast hkr_lt
    omega
  have hkr_le2 : ((2 * Mp - Mq : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hk_le
  rw [hgap, huq]
  exact mul_le_mul_of_nonneg_right hkr_le2 (le_of_lt hu_pos)

/-- **Boldo §3: the correction branch is within `2·ulp(d)`** (radix 2).

The full dispatch of Kahan's correction branch `3|p − q| < p + q`. With `q > 0` and
`p − q ∈ F` (Lemma 1), it splits on the ulps of `p` and `q`:
- `ulp p = ulp q` → Lemma 4 (`disc_corr_lemma4`), its grid hypotheses discharged
  unconditionally by `disc_mag_prod_no_bump`;
- distinct ulps, far (`ulp p + ulp q ≤ |p − q|`) → `disc_corr_far`;
- distinct ulps, near → the §3.2.2 particular case, oriented by `q < p`
  (`disc_corr_particular`) or `p < q` (`disc_corr_particular_lo`), with the tight gap
  `|p − q| ≤ 2·ulp(min)` from `disc_gap_le_two_ulp`.

The WLOG `p ≥ q` of Boldo's paper is *not* assumed: both orientations are handled, by
the genuine mirror `disc_corr_particular_lo` (the functional-rounding setting does not
collapse them). No `prec ≥ 3` side condition — the no-bump keystone removed it. -/
theorem disc_correction (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) ((p - q) + g))
    (hbranch : 3 * |p - q| < p + q) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hp_nn : 0 ≤ p := by rw [hpe]; exact disc_p_nonneg beta prec hp choice b
  have Fp : generic_format beta (FLX_exp prec) p := by
    rw [hpe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  have Fq : generic_format beta (FLX_exp prec) q := by
    rw [hqe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  -- `q > 0` and `p > 0` in the correction branch (Boldo Lemma 1's first step).
  have hq_pos : 0 < q := by
    by_contra h; push_neg at h
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p - q)] at hbranch; linarith
  have hp_pos : 0 < p := by
    rcases lt_or_eq_of_le hp_nn with h | h
    · exact h
    · exfalso; rw [← h, zero_sub, abs_neg, abs_of_pos hq_pos] at hbranch; linarith
  -- products positive (for the no-bump grid discharge).
  have hbb_pos : 0 < b * b := by
    rcases (mul_self_nonneg b).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hpe, ← h, round_0] at hp_pos; exact lt_irrefl 0 hp_pos
  have hac_pos : 0 < a * c := by
    by_contra h; push_neg at h
    have hqle : q ≤ 0 := by
      rw [hqe]
      calc round beta (FLX_exp prec) (Znearest choice) (a * c)
          ≤ round beta (FLX_exp prec) (Znearest choice) 0 :=
            round_le beta (FLX_exp prec) hValid (Znearest choice) h
        _ = 0 := round_0 beta (FLX_exp prec) (Znearest choice)
    linarith
  -- Lemma 1 Sterbenz ranges.
  have hp2q : p ≤ 2 * q := by nlinarith [hbranch, le_abs_self (p - q)]
  have hq2p : q ≤ 2 * p := by
    nlinarith [hbranch, (by rw [abs_sub_comm]; exact le_abs_self (q - p) : q - p ≤ |p - q|)]
  have hpqF : generic_format beta (FLX_exp prec) (p - q) :=
    disc_branch_subtract_exact beta prec hp Fp Fq hp_nn hbranch
  by_cases hue : ulp beta (FLX_exp prec) p = ulp beta (FLX_exp prec) q
  · -- equal ulp → Lemma 4 (grid hypotheses discharged by the no-bump keystone).
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne : q ≠ 0 := ne_of_gt hq_pos
    have hcpq : cexp beta (FLX_exp prec) p = cexp beta (FLX_exp prec) q := by
      rw [ulp_neq_0 beta (FLX_exp prec) hp_ne, ulp_neq_0 beta (FLX_exp prec) hq_ne] at hue
      rcases lt_trichotomy (cexp beta (FLX_exp prec) p) (cexp beta (FLX_exp prec) q) with h | h | h
      · exact absurd hue (ne_of_lt (bpow_lt beta h))
      · exact h
      · exact absurd hue.symm (ne_of_lt (bpow_lt beta h))
    have hgb4 : cexp beta (FLX_exp prec) p - prec
        ≤ cexp beta (FLX_exp prec) b + cexp beta (FLX_exp prec) b := by
      have h := disc_mag_prod_no_bump beta prec hp choice Fb Fb hbb_pos
      rw [← hpe] at h; unfold cexp FLX_exp; omega
    have hgc4 : cexp beta (FLX_exp prec) p - prec
        ≤ cexp beta (FLX_exp prec) a + cexp beta (FLX_exp prec) c := by
      have h := disc_mag_prod_no_bump beta prec hp choice Fa Fc hac_pos
      rw [← hqe] at h; rw [hcpq]; unfold cexp FLX_exp; omega
    exact disc_corr_lemma4 beta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd hue hgb4 hgc4
  · -- distinct ulps → far or particular (oriented).
    rcases lt_trichotomy p q with hlt | heq | hgt
    · -- p < q (case B).
      by_cases hfar : ulp beta (FLX_exp prec) p + ulp beta (FLX_exp prec) q ≤ |p - q|
      · exact disc_corr_far beta hbeta prec hp choice a b c hpe hqe hdp hdq hg hd hpqF hfar
      · push_neg at hfar
        have hgap : q - p ≤ 2 * ulp beta (FLX_exp prec) p :=
          disc_gap_le_two_ulp beta hbeta prec hp (p := q) (q := p) Fq Fp hp_pos hlt (Ne.symm hue) hq2p
            (by rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ q - p)] at hfar;
                linarith [hfar])
        exact disc_corr_particular_lo beta hbeta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
          hp_pos hlt hue hgap hbranch
    · exact absurd (by rw [heq]) hue
    · -- q < p (case A).
      by_cases hfar : ulp beta (FLX_exp prec) p + ulp beta (FLX_exp prec) q ≤ |p - q|
      · exact disc_corr_far beta hbeta prec hp choice a b c hpe hqe hdp hdq hg hd hpqF hfar
      · push_neg at hfar
        have hgap : p - q ≤ 2 * ulp beta (FLX_exp prec) q :=
          disc_gap_le_two_ulp beta hbeta prec hp Fp Fq hq_pos hgt hue hp2q
            (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ p - q)] at hfar; exact hfar)
        exact disc_corr_particular beta hbeta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg hd
          hq_pos hgt hue hgap hbranch

/-- **Boldo §3 capstone: Kahan's branch algorithm is within `2·ulp(d)`** (radix 2,
real test). Combining the benign branch (`disc_branch_benign`) and the correction
branch (`disc_correction`): for the result

```
  d = if p + q ≤ 3·|p − q| then ◦(p − q) else ◦((p − q) + ◦(dp − dq))
```

of Kahan's discriminant algorithm with the *real* test `3|p − q| ≥ p + q`, the error
`|d − (b·b − a·c)| ≤ 2·ulp(d)`. This is the full result of Boldo (2009) §3 — every case
of the branch algorithm, both orientations, 0 `sorry`s. (The §4 reconciliation of the
real test with the *rounded* floating-point test `3·◦|p − q| ≥ ◦(p + q)` remains.) -/
theorem disc_branch_real_test (beta : radix) (hbeta : beta.val = 2)
    (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq g d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hg : g = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = if p + q ≤ 3 * |p - q|
              then round beta (FLX_exp prec) (Znearest choice) (p - q)
              else round beta (FLX_exp prec) (Znearest choice) ((p - q) + g)) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  rw [hd]
  by_cases htest : p + q ≤ 3 * |p - q|
  · rw [if_pos htest]
    exact disc_branch_benign beta hbeta prec hp choice a b c hpe hqe rfl htest
  · rw [if_neg htest]
    push_neg at htest
    exact disc_correction beta hbeta prec hp choice Fa Fb Fc hpe hqe hdp hdq hg rfl htest

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

/-! ## Relative-error calculus (after Boldo, `flocq/examples/Triangle.v`)

Boldo's proof of the sibling Kahan triangle-area algorithm threads a relative
error `e` through each operation via the predicate `rel_err x y e := |x−y| ≤
e·|y|` and a small composable algebra. We port the foundational layer here; it
is the backbone of the forthcoming `2u` assembly (and is reusable across the
whole Kahan family). `eps` in Boldo's notation is our `u_ro`.

Note: Boldo's `err_add` needs *nonnegative* operands, so it does NOT cover the
discriminant's cancelling subtraction `p − q`; that case goes through
Sterbenz-exactness (`disc_sterbenz_exact`) instead. -/

/-- Boldo's relative-error predicate: `x` approximates `y` to relative error `e`. -/
def rel_err (x y e : ℝ) : Prop := |x - y| ≤ e * |y|

/-- Weaken the relative-error bound (`err_aux`). -/
theorem rel_err_aux {x y e1 e2 : ℝ} (h : rel_err x y e1) (he : e1 ≤ e2) :
    rel_err x y e2 :=
  h.trans (mul_le_mul_of_nonneg_right he (abs_nonneg y))

/-- Exact values have zero relative error (`err_0`). -/
theorem rel_err_0 (x : ℝ) : rel_err x x 0 := by
  simp [rel_err]

/-- Relative error is preserved under negation (`err_opp`). -/
theorem rel_err_opp {x y e : ℝ} (h : rel_err x y e) : rel_err (-x) (-y) e := by
  unfold rel_err at h ⊢
  rw [show -x - -y = -(x - y) from by ring, abs_neg, abs_neg]
  exact h

/-- Rounding introduces relative error at most `u_ro` (`err_init`). -/
theorem rel_err_init (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (x : ℝ) :
    rel_err (round beta (FLX_exp prec) (Znearest choice) x) x (u_ro beta prec) := by
  unfold rel_err u_ro
  exact relative_error_N_FLX beta prec hp choice x

/-! ## D3: the FMA-based discriminant — error decomposition

The FMA-based algorithm (no branch test, hence no Gappa) computes:
```
  p  := RN(b·b)        q  := RN(a·c)
  dp := b·b − p        dq := a·c − q          (exact, via fma — see D0)
  s1 := RN(p − q)      s2 := RN(dp − dq)
  d  := RN(s1 + s2)
```
By the exact identity `(p − q) + (dp − dq) = b·b − a·c` (D1), the result `d`
differs from the true discriminant by exactly three rounding errors — the two
inner sums and the final sum:
`d − (b·b − a·c) = (d − (s1+s2)) + (s1 − (p−q)) + (s2 − (dp−dq))`.
Each is bounded by the *sharp* `v = u_ro/(1+u_ro)` relative error
(`relative_error_N_FLX'`). The sharp form (rather than the plain `u_ro`) is what
makes the eventual `2u` bound tight rather than `2u + O(u²)`. -/

/-- **FMA-discriminant error decomposition.**

`|d − (b·b − a·c)| ≤ v · (|s1+s2| + |p−q| + |dp−dq|)` with `v = u_ro/(1+u_ro)`,
for the FMA algorithm's intermediate values. General radix. -/
theorem disc_fma_error_decomp (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {p q dp dq s1 s2 d : ℝ}
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hs1 : s1 = round beta (FLX_exp prec) (Znearest choice) (p - q))
    (hs2 : s2 = round beta (FLX_exp prec) (Znearest choice) (dp - dq))
    (hd : d = round beta (FLX_exp prec) (Znearest choice) (s1 + s2)) :
    |d - (b * b - a * c)|
      ≤ u_ro beta prec / (1 + u_ro beta prec) * (|s1 + s2| + |p - q| + |dp - dq|) := by
  set v := u_ro beta prec / (1 + u_ro beta prec) with hv
  -- The three sharp relative-error bounds, one per rounding.
  have eout : |d - (s1 + s2)| ≤ v * |s1 + s2| := by
    rw [hd]; exact relative_error_N_FLX' beta prec hp choice (s1 + s2)
  have e1 : |s1 - (p - q)| ≤ v * |p - q| := by
    rw [hs1]; exact relative_error_N_FLX' beta prec hp choice (p - q)
  have e2 : |s2 - (dp - dq)| ≤ v * |dp - dq| := by
    rw [hs2]; exact relative_error_N_FLX' beta prec hp choice (dp - dq)
  -- Exact algebraic decomposition (using the D1 identity).
  have key : d - (b * b - a * c)
      = (d - (s1 + s2)) + (s1 - (p - q)) + (s2 - (dp - dq)) := by
    rw [hdp, hdq]; ring
  rw [key]
  have t1 : |(d - (s1 + s2)) + (s1 - (p - q)) + (s2 - (dp - dq))|
      ≤ |(d - (s1 + s2)) + (s1 - (p - q))| + |s2 - (dp - dq)| := abs_add_le _ _
  have t2 : |(d - (s1 + s2)) + (s1 - (p - q))|
      ≤ |d - (s1 + s2)| + |s1 - (p - q)| := abs_add_le _ _
  calc |(d - (s1 + s2)) + (s1 - (p - q)) + (s2 - (dp - dq))|
      ≤ |d - (s1 + s2)| + |s1 - (p - q)| + |s2 - (dp - dq)| := by linarith [t1, t2]
    _ ≤ v * |s1 + s2| + v * |p - q| + v * |dp - dq| := by linarith [eout, e1, e2]
    _ = v * (|s1 + s2| + |p - q| + |dp - dq|) := by ring

/-! ## D3: the opposite-sign (no-cancellation) 2u bound

The canonical Kahan determinant algorithm (John D. Cook's form), specialized to
the discriminant `b·b − a·c`:
```
  w := RN(a·c)        e := w − a·c        (e exact, via fma — D0)
  f := RN(b·b − w)    x := RN(f + e)
```
Here `b·b − a·c = (b·b − w) + e`, so the result has only TWO rounding errors:
`x − (b·b − a·c) = (f − (b·b − w)) + (x − (f + e))`.

When `a·c ≤ 0` (the discriminant is `b·b + |a·c|`, a sum of squares — *no
cancellation*), this is enough to prove the full `2u` relative bound directly,
with no grid/Gappa machinery. This is the regime Jeannerod–Louvet–Muller single
out, and it is exactly what CAD's positive-definite predicates hit.

The general (cancelling) case `a·c > 0` needs their grid-level argument and is
left for a faithful port of the published proof. -/

/-- **Kahan discriminant error decomposition (any sign).**

For the canonical algorithm, the result differs from `b·b − a·c` by exactly two
rounding errors (the `f`-round and the `x`-round):
`|x − (b·b − a·c)| ≤ v · (|b·b − w| + |f + e|)`, `v = u_ro/(1+u_ro)`.
General radix, no sign hypothesis. This is the unconditional scaffold; the
opposite-sign case below sharpens it to the full `2u`. -/
theorem disc_kahan_error_decomp (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ)
    {w e f x : ℝ}
    (he : e = w - a * c)
    (hf : f = round beta (FLX_exp prec) (Znearest choice) (b * b - w))
    (hx : x = round beta (FLX_exp prec) (Znearest choice) (f + e)) :
    |x - (b * b - a * c)|
      ≤ u_ro beta prec / (1 + u_ro beta prec) * (|b * b - w| + |f + e|) := by
  set v := u_ro beta prec / (1 + u_ro beta prec) with hv_def
  have hef : |f - (b * b - w)| ≤ v * |b * b - w| := by
    rw [hf]; exact relative_error_N_FLX' beta prec hp choice (b * b - w)
  have hex : |x - (f + e)| ≤ v * |f + e| := by
    rw [hx]; exact relative_error_N_FLX' beta prec hp choice (f + e)
  have hsplit : x - (b * b - a * c) = (f - (b * b - w)) + (x - (f + e)) := by
    rw [he]; ring
  calc |x - (b * b - a * c)|
      = |(f - (b * b - w)) + (x - (f + e))| := by rw [hsplit]
    _ ≤ |f - (b * b - w)| + |x - (f + e)| := abs_add_le _ _
    _ ≤ v * |b * b - w| + v * |f + e| := by linarith [hef, hex]
    _ = v * (|b * b - w| + |f + e|) := by ring

/-- **Kahan discriminant, opposite-sign case: relative error ≤ 2u.**

For `a·c ≤ 0`, the FMA algorithm `w = RN(a·c)`, `e = w − a·c`, `f = RN(b·b − w)`,
`x = RN(f + e)` computes `b·b − a·c` with relative error at most `2·u_ro`.
General radix; no format hypotheses needed (the fma step makes `e` exact, which
is what the equation `e = w − a·c` encodes). -/
theorem disc_kahan_opp_sign_2u (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (a b c : ℝ) (hac : a * c ≤ 0)
    {w e f x : ℝ}
    (hw : w = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (he : e = w - a * c)
    (hf : f = round beta (FLX_exp prec) (Znearest choice) (b * b - w))
    (hx : x = round beta (FLX_exp prec) (Znearest choice) (f + e)) :
    |x - (b * b - a * c)| ≤ 2 * u_ro beta prec * |b * b - a * c| := by
  -- Notation: u = unit roundoff, v = sharp relative error u/(1+u).
  have hu_nn : 0 ≤ u_ro beta prec := u_ro_pos beta prec
  set u := u_ro beta prec with hu_def
  set v := u / (1 + u) with hv_def
  have h1pu : (0 : ℝ) < 1 + u := by linarith
  have hvu : v * (1 + u) = u := by rw [hv_def]; field_simp
  have hv_nn : 0 ≤ v := by rw [hv_def]; positivity
  -- The sharp per-rounding bound, in `v` form.
  have rel : ∀ z : ℝ, |round beta (FLX_exp prec) (Znearest choice) z - z| ≤ v * |z| := by
    intro z; rw [hv_def, hu_def]; exact relative_error_N_FLX' beta prec hp choice z
  -- A reusable triangle inequality `|s - t| ≤ |s| + |t|`.
  have habs_sub : ∀ s t : ℝ, |s - t| ≤ |s| + |t| := fun s t => by
    calc |s - t| = |s + (-t)| := by ring_nf
      _ ≤ |s| + |(-t)| := abs_add_le _ _
      _ = |s| + |t| := by rw [abs_neg]
  -- The discriminant is nonnegative, and dominates |a·c|.
  have hD_nn : 0 ≤ b * b - a * c := by nlinarith [mul_self_nonneg b]
  have hQ_le_D : |a * c| ≤ b * b - a * c := by
    rw [abs_of_nonpos hac]; nlinarith [mul_self_nonneg b]
  -- Per-step error bounds.
  have he_bd : |e| ≤ v * |a * c| := by
    rw [he, hw]; exact rel (a * c)
  -- εf = f − (b·b − w);  |b·b − w| ≤ D(1+v).
  have hbw_eq : b * b - w = (b * b - a * c) - e := by rw [he]; ring
  have hbw : |b * b - w| ≤ (b * b - a * c) * (1 + v) := by
    calc |b * b - w| = |(b * b - a * c) - e| := by rw [hbw_eq]
      _ ≤ |b * b - a * c| + |e| := habs_sub _ _
      _ = (b * b - a * c) + |e| := by rw [abs_of_nonneg hD_nn]
      _ ≤ (b * b - a * c) + v * |a * c| := by linarith [he_bd]
      _ ≤ (b * b - a * c) + v * (b * b - a * c) := by
            have := mul_le_mul_of_nonneg_left hQ_le_D hv_nn; linarith
      _ = (b * b - a * c) * (1 + v) := by ring
  have hef : |f - (b * b - w)| ≤ v * ((b * b - a * c) * (1 + v)) := by
    calc |f - (b * b - w)| ≤ v * |b * b - w| := by rw [hf]; exact rel (b * b - w)
      _ ≤ v * ((b * b - a * c) * (1 + v)) := mul_le_mul_of_nonneg_left hbw hv_nn
  -- εx = x − (f + e);  f + e = D + εf, so |f + e| ≤ D(1 + v(1+v)).
  have hfe_eq : f + e = (b * b - a * c) + (f - (b * b - w)) := by rw [he]; ring
  have hfe : |f + e| ≤ (b * b - a * c) * (1 + v * (1 + v)) := by
    calc |f + e| = |(b * b - a * c) + (f - (b * b - w))| := by rw [hfe_eq]
      _ ≤ |b * b - a * c| + |f - (b * b - w)| := abs_add_le _ _
      _ = (b * b - a * c) + |f - (b * b - w)| := by rw [abs_of_nonneg hD_nn]
      _ ≤ (b * b - a * c) + v * ((b * b - a * c) * (1 + v)) := by linarith [hef]
      _ = (b * b - a * c) * (1 + v * (1 + v)) := by ring
  have hex : |x - (f + e)| ≤ v * ((b * b - a * c) * (1 + v * (1 + v))) := by
    calc |x - (f + e)| ≤ v * |f + e| := by rw [hx]; exact rel (f + e)
      _ ≤ v * ((b * b - a * c) * (1 + v * (1 + v))) := mul_le_mul_of_nonneg_left hfe hv_nn
  -- Assemble:  x − D = εf + εx.
  have hsplit : x - (b * b - a * c) = (f - (b * b - w)) + (x - (f + e)) := by rw [he]; ring
  -- Scalar fact:  v·(2 + 2v + v²) ≤ 2u.  (Multiply by (1−v) > 0 and use u(1−v) = v.)
  have hv_le_u : v ≤ u := by rw [hv_def]; exact div_le_self hu_nn (by linarith)
  have hu_lt1 : u < 1 := by rw [hu_def]; exact u_ro_lt_1 beta prec hp
  have h1mv_pos : (0 : ℝ) < 1 - v := by
    have := lt_of_le_of_lt hv_le_u hu_lt1; linarith
  have huv : u * (1 - v) = v := by linear_combination -hvu
  have hscalar : v * (2 + 2 * v + v * v) ≤ 2 * u := by
    nlinarith [huv, h1mv_pos, hv_nn,
      mul_nonneg (mul_nonneg hv_nn hv_nn) hv_nn,
      mul_nonneg (mul_nonneg (mul_nonneg hv_nn hv_nn) hv_nn) hv_nn]
  calc |x - (b * b - a * c)|
      = |(f - (b * b - w)) + (x - (f + e))| := by rw [hsplit]
    _ ≤ |f - (b * b - w)| + |x - (f + e)| := abs_add_le _ _
    _ ≤ v * ((b * b - a * c) * (1 + v))
          + v * ((b * b - a * c) * (1 + v * (1 + v))) := by linarith [hef, hex]
    _ = (b * b - a * c) * (v * (2 + 2 * v + v * v)) := by ring
    _ ≤ (b * b - a * c) * (2 * u) := mul_le_mul_of_nonneg_left hscalar hD_nn
    _ = 2 * u * |b * b - a * c| := by rw [abs_of_nonneg hD_nn]; ring

/-! ## Boldo §4: reconciling the real test with the floating-point test

The §3 proof uses the *real* test `3|p − q| ≥ p + q`. The actual program tests the
rounded quantities: `◦(p + q) ≤ ◦(3·|p − q|)` (with `◦(p − q) = p − q` exact in the
Sterbenz range, so `◦(|p − q|) = |p − q|`). The two tests can disagree (Boldo's 5-digit
`p = 27, q = 14`). §4 shows the `2·ulp(d)` bound survives both disagreements.

**First disagreement (§4.1):** real says correction (`3|p − q| < p + q`) but the program
runs *benign* (`◦(p + q) ≤ ◦(3·|p − q|)`), so `d = ◦(p − q) = p − q`. Lemmas 5–9 show
`δ ≤ 2·ulp d` anyway. These are stated for `q < p` (Boldo's WLOG); since here `d = p − q`
is the *exact* benign result, the orientation is handled at assembly by sign symmetry of
`◦(p − q)`. -/

/-- **Boldo §4 Lemma 5** (radix 2). First disagreement, the easy case `cexp q ≤ cexp d`:
with `d = p − q` exact, `δ = |dp − dq| ≤ ½(ulp p + ulp q) ≤ 3/2·ulp q ≤ 3/2·ulp d`. -/
theorem disc_fp_lemma5 (beta : radix) (hbeta : beta.val = 2) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a b c : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    {p q dp dq d : ℝ}
    (hpe : p = round beta (FLX_exp prec) (Znearest choice) (b * b))
    (hqe : q = round beta (FLX_exp prec) (Znearest choice) (a * c))
    (hdp : dp = b * b - p)
    (hdq : dq = a * c - q)
    (hde : d = round beta (FLX_exp prec) (Znearest choice) (p - q))
    (hq_pos : 0 < q) (hqp : q < p)
    (hbranch : 3 * |p - q| < p + q)
    (hed : cexp beta (FLX_exp prec) q ≤ cexp beta (FLX_exp prec) d) :
    |d - (b * b - a * c)| ≤ 2 * ulp beta (FLX_exp prec) d := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hp_pos : 0 < p := lt_trans hq_pos hqp
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have Fp : generic_format beta (FLX_exp prec) p := by
    rw [hpe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  have Fq : generic_format beta (FLX_exp prec) q := by
    rw [hqe]; exact generic_format_round beta (FLX_exp prec) hValid (Znearest choice) _
  -- `d = p − q` exactly (Lemma 1).
  have hpqF : generic_format beta (FLX_exp prec) (p - q) :=
    disc_branch_subtract_exact beta prec hp Fp Fq (le_of_lt hp_pos) hbranch
  have hd_eq : d = p - q := by
    rw [hde]; exact round_generic beta (FLX_exp prec) (Znearest choice) hpqF
  have hd_pos : 0 < d := by rw [hd_eq]; linarith
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  -- `δ = |dp − dq|`.
  have hdelta : d - (b * b - a * c) = -(dp - dq) := by
    have := disc_corrected_value (a := a) (b := b) (c := c) (p := p) (q := q) hdp hdq
    rw [hd_eq]; linarith [this]
  have hdelta_abs : |d - (b * b - a * c)| = |dp - dq| := by rw [hdelta, abs_neg]
  -- `|dp − dq| ≤ ½(ulp p + ulp q)`.
  have hbd := disc_corr_dpdq_bound beta prec hp choice a b c hpe hqe hdp hdq
  -- `p ≤ 2q` (Lemma 1), so `ulp p ≤ 2·ulp q`.
  have hp2q : p ≤ 2 * q := by nlinarith [hbranch, le_abs_self (p - q)]
  have hulp_p_le : ulp beta (FLX_exp prec) p ≤ 2 * ulp beta (FLX_exp prec) q := by
    rw [← ulp_two_mul_r2 beta hbeta prec hp q]
    apply ulp_le beta (FLX_exp prec) hValid hMon
    rw [abs_of_pos hp_pos, abs_of_pos (by linarith : (0:ℝ) < 2 * q)]; linarith
  -- `ulp q ≤ ulp d` (from `cexp q ≤ cexp d`).
  have hulp_qd : ulp beta (FLX_exp prec) q ≤ ulp beta (FLX_exp prec) d := by
    rw [ulp_neq_0 beta (FLX_exp prec) hq_ne, ulp_neq_0 beta (FLX_exp prec) hd_ne]
    exact bpow_le beta hed
  rw [hdelta_abs]
  linarith [hbd, hulp_p_le, hulp_qd, ulp_ge_0 beta (FLX_exp prec) q]

end LeanFlocq
