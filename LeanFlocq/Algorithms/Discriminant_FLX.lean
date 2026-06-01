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

end LeanFlocq
