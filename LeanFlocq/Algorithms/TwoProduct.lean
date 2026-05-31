/-
# Dekker's TwoProduct (error-free transformation for multiplication)

Given floats `x, y`, computes `r = round(x·y)` and an exact error term `e`
with `x · y = r + e`. The FMA-free construction (Dekker) splits each input
into high/low halves via Veltkamp, forms the four sub-products, and
reconstructs the error through a short summation chain.

This file is built incrementally, in chunks:
- **Chunk 1** (here): `generic_format_FLX_mult` — the product of a `p1`-digit
  and a `p2`-digit value is exact at precision `p1 + p2`. This makes three
  of the four Veltkamp sub-products exact unconditionally, and the fourth
  (`tx · ty`) exact when `prec` is even.

Reference: Pff `Pff2Flocq.v` `Dekker` section (682–976), `Pff.v`
`Dekker_aux`/`DekkerN` (17677–17910).
-/
import LeanFlocq.Algorithms.Veltkamp

namespace LeanFlocq

/-- **Product of low-precision values is exact.**

If `x` is representable with `p1` significant digits and `y` with `p2`, and
`p1 + p2 ≤ prec`, then `x · y` is representable with `prec` digits — the
rounding of the product is exact.

This is the core fact behind Dekker's TwoProduct: each sub-product of the
Veltkamp half-splits fits in the working precision.

Proof: write `x = Mx · β^cx`, `y = My · β^cy` canonically, so
`x · y = (Mx · My) · β^(cx+cy)`. Since `mag(x·y) ≤ mag(x) + mag(y)` and
`cexp = mag − prec`, we get `cexp(x·y) ≤ (mag x − p1) + (mag y − p2) +
(p1 + p2 − prec) ≤ cx + cy`, which is exactly the hypothesis of
`generic_format_F2R`. -/
theorem generic_format_FLX_mult (beta : radix) (p1 p2 prec : ℤ)
    (h_budget : p1 + p2 ≤ prec)
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp p1) x)
    (Fy : generic_format beta (FLX_exp p2) y) :
    generic_format beta (FLX_exp prec) (x * y) := by
  by_cases hxy : x * y = 0
  · rw [hxy]; exact generic_format_0 _ _
  have hx0 : x ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hy0 : y ≠ 0 := fun h => hxy (by rw [h, mul_zero])
  -- Canonical exponents and mantissas.
  set cx := cexp beta (FLX_exp p1) x with hcx_def
  set cy := cexp beta (FLX_exp p2) y with hcy_def
  set Mx := Ztrunc (scaled_mantissa beta (FLX_exp p1) x) with hMx_def
  set My := Ztrunc (scaled_mantissa beta (FLX_exp p2) y) with hMy_def
  have hx_eq : x = (Mx : ℝ) * bpow beta cx := Fx
  have hy_eq : y = (My : ℝ) * bpow beta cy := Fy
  -- Product as a single F2R at exponent cx + cy.
  have hxy_F2R : x * y = F2R (beta := beta) ⟨Mx * My, cx + cy⟩ := by
    show x * y = ((Mx * My : ℤ) : ℝ) * bpow beta (cx + cy)
    rw [hx_eq, hy_eq, bpow_plus]; push_cast; ring
  -- cexp as mag − prec for each.
  have hcx_eq : cx = mag beta x - p1 := by rw [hcx_def]; unfold cexp FLX_exp; rfl
  have hcy_eq : cy = mag beta y - p2 := by rw [hcy_def]; unfold cexp FLX_exp; rfl
  -- mag(x·y) ≤ mag(x) + mag(y).
  have h_mag_le : mag beta (x * y) ≤ mag beta x + mag beta y :=
    (mag_mult beta hx0 hy0).2
  -- cexp_prec(x·y) ≤ cx + cy.
  have h_cexp_le : cexp beta (FLX_exp prec) (x * y) ≤ cx + cy := by
    have : cexp beta (FLX_exp prec) (x * y) = mag beta (x * y) - prec := by
      unfold cexp FLX_exp; rfl
    rw [this, hcx_eq, hcy_eq]; omega
  -- Conclude via generic_format_F2R.
  rw [hxy_F2R]
  apply generic_format_F2R
  intro _
  rw [← hxy_F2R]
  exact h_cexp_le

end LeanFlocq
