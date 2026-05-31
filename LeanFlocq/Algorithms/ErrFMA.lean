/-
# ErrFMA: the exact error of a fused multiply-add (Boldo–Muller)

Given floats `a, b, c`, the FMA computes `r1 = round(a·b + c)` in one rounding.
Unlike TwoSum/TwoProduct, the error `a·b + c − r1` does not always fit in a
single float — ErrFMA produces two floats `r2, r3` with

    a·b + c = r1 + r2 + r3   (exactly).

The algorithm stacks the error-free transformations:

    r1 = round(a·b + c)              -- the FMA
    (u1, u2) = TwoProduct(a, b)      -- a·b = u1 + u2
    (α1, α2) = TwoSum(c, u2)         -- c + u2 = α1 + α2
    (β1, β2) = TwoSum(u1, α1)        -- u1 + α1 = β1 + β2
    γ = round(round(β1 − r1) + β2)
    (r2, r3) = TwoSum(γ, α2)

Setting: radix 2, FLX, round-to-nearest (the no-underflow case).

This file is built in stages:
- **E1** (here): the existential EFT interfaces (`twoproduct_eft`, `twosum_eft`)
  and the exact-algebra chain `a·b + c = β1 + β2 + α2` (`ErrFMA_chain`).
- **E2** (in progress): the crux exactness lemmas.
  - **L1 DONE** (`errfma_gat_exact`): `β1 − r1 ∈ F`, via the round-minus-round
    engine `round_minus_round_nearby_exact_FLX` in `RoundMinusRound_FLX.lean`.
  - **β2 = 0 DONE** (`ErrFMA_be2_zero` = Pff `FmaErr_aux1`): `a·b+c = r1+γ+α2`.
  - **L2 / β2 ≠ 0 REMAINING** (Pff `FmaErr_aux2`/`gaCorrect`) — see below.
- **E3** (pending): assembly into `a·b + c = r1 + r2 + r3`.

## E2 progress and the L2 roadmap (Boldo–Muller 2011, IEEE TC 60(2))

The whole result reduces to `γ = β1 + β2 − r1` exactly, i.e. two exactness
lemmas (`γ = round(round(β1 − r1) + β2)`):
  - **L1**: `round(β1 − r1) = β1 − r1`   (`β1 − r1 ∈ F`) — **DONE**.
  - **L2**: `round((β1 − r1) + β2) = (β1 − r1) + β2` — remaining.
Then `γ = (β1−r1)+β2 = β1+β2−r1`, and with the E1 chain `a·b+c = β1+β2+α2` we
get `a·b+c = r1 + γ + α2` (Boldo–Muller Theorem 2's conclusion verbatim).

**L1 — the engine.** Pff's `gatCorrect` reduces to `Subexact`: `β1 − r1` is
Sterbenz-exact because `β1 = ◦(u1+α1)` and `r1 = ◦(u1+α1+α2)` stay within a
factor of two (`α2` is at most half a ulp of each summand). The Flocq-native
engine is `round_minus_round_nearby_exact_FLX`: at radix 2 a nonzero float-sum
sits on the grid `β^min(cexp a, cexp b)` and `|α2|` is at most half of it, so the
two roundings keep the sign and stay within `[½, 3⁄2]·|sum|`. The output-form
relative bounds `err_le_uro_round_FLX` (= Pff `ClosestRounde{Le,Ge}Normal`) and
a boundary/bulk dichotomy give the tight factor of two; `sterbenz_abs` finishes.
All non-underflow side conditions are *vacuous* at FLX (the payoff of staying
FLX). Needs only radix 2 + `prec ≥ 3`.

**β2 = 0 (`FmaErr_aux1`) — DONE.** `γ = ◦(◦(β1−r1)+0) = β1−r1` (L1 + idempotency),
so `a·b+c = r1 + (β1−r1) + α2 = β1 + α2`, matching the chain at β2=0.

**L2 / β2 ≠ 0 (`FmaErr_aux2`/`gaCorrect`) — REMAINING.** Need
`(β1−r1) + β2 ∈ F`. Using `(β1−r1)+β2 = (a·b+c − r1) − α2`, the structure is:
  - **Dichotomy (Pff `Midpoint_aux`, GenericC/D, Pff.v 23856–24316, ~400 lines):**
    `β1 = r1` OR `cexp(β2) ≥ cexp(β1) − 2`. If `β1 = r1`, `(β1−r1)+β2 = β2 ∈ F`.
    Else β2 isn't tiny, and β1−r1 (cexp ≥ cexp(β1)−1 in radix 2) aligns with β2
    on grid `cexp(β1)−2`; the magnitude `|(β1−r1)+β2| < β^(cexp(β1)+1) ≤
    β^(prec−2+cexp(β1))` forces representability (Pff `BoundedL`).
  - **`be2MuchSmaller` (Pff.v 24596):** `MSB(α2) < LSB(β2)` — α2 entirely below
    β2's lowest set bit — the hypothesis Midpoint_aux needs.
  - **`Expr1`/`Expbe1` (Pff.v 24519/24555):** `|cexp(β1) − cexp(r1)| ≤ 1`, a
    radix-2 consequence of the factor-of-two bounds (the engine's machinery is
    in hand — these should be a short add).
Pff does this with **MSB/LSB bit-position machinery** modern Flocq lacks. The
Flocq-native path is a **midpoint argument**: if the tiny α2 flips the rounding
(`r1 ≠ β1`), then `β1+β2` sits within `|α2|` of a midpoint of the β1-grid, which
pins β2 near `±½ulp(β1)` and hence `cexp(β2) ≥ cexp(β1) − 2` (`round_N_eq_DN`,
`round_N_le_midp`, the Ulp perturbation family). Estimated ~600–900 Lean lines —
its own focused session. This is the genuine remaining hard core of ErrFMA.
-/
import LeanFlocq.Algorithms.TwoProduct
import LeanFlocq.Algorithms.EFT_FLX
import LeanFlocq.Algorithms.RoundMinusRound_FLX

namespace LeanFlocq

open radix (radix2)
open Classical

/-! ### Existential EFT interfaces

ErrFMA only consumes the abstract guarantees of TwoProduct and TwoSum — the
high word is `round(·)`, the low word is *some* float, and together they
reproduce the exact value. These wrappers expose exactly that, hiding the
(branching) construction of the low word. -/

/-- **TwoProduct as an existential EFT.** `a·b = round(a·b) + e` with `e ∈ F`. -/
theorem twoproduct_eft (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {s : ℤ} {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (hs2lo : prec ≤ 2 * s) (hs2hi : 2 * s ≤ prec + 1) :
    ∃ e, generic_format radix2 (FLX_exp prec) e ∧
      a * b = round radix2 (FLX_exp prec) (Znearest choice) (a * b) + e :=
  ⟨_, generic_format_round radix2 (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) _,
    TwoProduct_FLX_machine radix2 prec hp choice Fa Fb (Or.inl rfl) hs_lo hs_hi hs2lo hs2hi⟩

/-- **TwoSum as an existential EFT.** `a + b = round(a+b) + e` with `e ∈ F`,
no magnitude precondition. -/
theorem twosum_eft (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool) {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b) :
    ∃ e, generic_format radix2 (FLX_exp prec) e ∧
      a + b = round radix2 (FLX_exp prec) (Znearest choice) (a + b) + e := by
  refine ⟨_, ?_, TwoSum_FLX_correct prec hp choice Fa Fb⟩
  split_ifs <;>
    exact generic_format_round radix2 (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) _

/-! ### E1: the exact-algebra chain

Chaining the three EFTs gives `a·b + c = β1 + β2 + α2` with no rounding error —
the whole point being that the *error* `a·b + c − r1` is then `(β1−r1) + β2 + α2`,
which E2/E3 show is exactly `r2 + r3`. -/

/-- **ErrFMA algebra skeleton.** With `u1 = round(a·b)`, `α1 = round(c + u2)`,
`β1 = round(u1 + α1)`, the three error-free transformations chain to
`a·b + c = β1 + β2 + α2` exactly, where `u2, α2, β2 ∈ F` are the EFT low words.
This is the algebraic content; the FMA result `r1 = round(a·b + c)` enters only
in E2 (the error `a·b + c − r1 = (β1 − r1) + β2 + α2`). -/
theorem ErrFMA_chain (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {s : ℤ} {a b c : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (hs2lo : prec ≤ 2 * s) (hs2hi : 2 * s ≤ prec + 1) :
    ∃ u2 α2 β2 : ℝ,
      generic_format radix2 (FLX_exp prec) u2 ∧
      generic_format radix2 (FLX_exp prec) α2 ∧
      generic_format radix2 (FLX_exp prec) β2 ∧
      a * b = round radix2 (FLX_exp prec) (Znearest choice) (a * b) + u2 ∧
      c + u2 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2) + α2 ∧
      round radix2 (FLX_exp prec) (Znearest choice) (a * b)
          + round radix2 (FLX_exp prec) (Znearest choice) (c + u2)
        = round radix2 (FLX_exp prec) (Znearest choice)
            (round radix2 (FLX_exp prec) (Znearest choice) (a * b)
              + round radix2 (FLX_exp prec) (Znearest choice) (c + u2)) + β2 ∧
      a * b + c
        = round radix2 (FLX_exp prec) (Znearest choice)
            (round radix2 (FLX_exp prec) (Znearest choice) (a * b)
              + round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
          + β2 + α2 := by
  obtain ⟨u2, Fu2, hab⟩ := twoproduct_eft prec hp choice Fa Fb hs_lo hs_hi hs2lo hs2hi
  obtain ⟨α2, Fα2, hcu2⟩ := twosum_eft prec hp choice Fc Fu2
  have Fu1 : generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a * b)) :=
    generic_format_round radix2 (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) _
  have Fα1 : generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (c + u2)) :=
    generic_format_round radix2 (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) _
  obtain ⟨β2, Fβ2, huα1⟩ := twosum_eft prec hp choice Fu1 Fα1
  exact ⟨u2, α2, β2, Fu2, Fα2, Fβ2, hab, hcu2, huα1, by linarith [hab, hcu2, huα1]⟩

/-! ### E2 / L1: `β1 − r1` is representable

The crux exactness lemma. With `u1 = ◦(a·b)`, `u2 = a·b − u1`, `α1 = ◦(c + u2)`,
`β1 = ◦(u1 + α1)`, `r1 = ◦(a·b + c)`, the difference `β1 − r1` is exact. This is
Pff's `gatCorrect`: it applies the round-minus-round engine with the
perturbation `α2 = (c + u2) − α1`, whose magnitude is at most half a ulp of both
`u1` (via `|α2| ≤ |u2| ≤ ½ ulp u1`) and `α1` (it is α1's own rounding error). -/

/-- **L1 (`gatCorrect`).** `β1 − r1 ∈ F`, where `β1 = ◦(u1 + α1)` and
`r1 = ◦(a·b + c)`. -/
theorem errfma_gat_exact (prec : ℤ) (hp : 3 ≤ prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 be1 r1 : ℝ}
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b + c)) :
    generic_format radix2 (FLX_exp prec) (be1 - r1) := by
  have hp0 : 0 < prec := by omega
  have hValid := FLX_exp_valid prec hp0
  have hMon := FLX_exp_monotone prec
  have hNotFTZ := monotone_exp_not_FTZ hValid hMon
  set al2 := (c + u2) - al1 with hal2
  have Fu1 : generic_format radix2 (FLX_exp prec) u1 := by
    rw [hu1]; exact generic_format_round _ _ hValid _ _
  have Fal1 : generic_format radix2 (FLX_exp prec) al1 := by
    rw [hal1]; exact generic_format_round _ _ hValid _ _
  -- |u2| ≤ ½ ulp u1  (u2 is u1's rounding error)
  have hu2_err : |u2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) u1 := by
    have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (a * b)
    rw [← hu1] at h
    rw [hu2, abs_sub_comm]; exact h
  -- |α2| ≤ |u2|  (round-to-nearest is at least as close as the float c)
  have hal2_le_u2 : |al2| ≤ |u2| := by
    obtain ⟨_, hcl⟩ := round_N_pt radix2 (FLX_exp prec) hValid choice (c + u2)
    have hc := hcl c Fc
    rw [← hal1] at hc
    have hcu : |c - (c + u2)| = |u2| := by
      rw [show c - (c + u2) = -u2 from by ring, abs_neg]
    rw [hcu] at hc
    rw [hal2, abs_sub_comm]; exact hc
  have Hea : |al2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) u1 := le_trans hal2_le_u2 hu2_err
  have Heb : |al2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) al1 := by
    have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (c + u2)
    rw [← hal1] at h
    rw [hal2, abs_sub_comm]; exact h
  have hEng := round_minus_round_nearby_exact_FLX prec hp choice Fu1 Fal1 Hea Heb
  -- rewrite round(u1+al1) = be1 and round(u1+al1+al2) = r1
  have h1 : round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1) = be1 := hbe1.symm
  have hsum : u1 + al1 + al2 = a * b + c := by rw [hal2, hu2]; ring
  have h2 : round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1 + al2) = r1 := by
    rw [hsum]; exact hr1.symm
  rw [h1, h2] at hEng
  exact hEng

/-! ### E2, the `β2 = 0` branch (`FmaErr_aux1`)

When the inner TwoSum on `(u1, α1)` is exact (`β2 = 0`), the FMA error reduces to
`γ = ◦(β1 − r1) = β1 − r1` (L1 + idempotency), giving the three-term identity
`a·b + c = r1 + γ + α2` directly. -/

/-- **ErrFMA, `β2 = 0` case.** -/
theorem ErrFMA_be2_zero (prec : ℤ) (hp : 3 ≤ prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 al2 be1 be2 r1 gat ga : ℝ}
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hal2 : al2 = (c + u2) - al1)
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hbe2 : be2 = (u1 + al1) - be1)
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b + c))
    (hgat : gat = round radix2 (FLX_exp prec) (Znearest choice) (be1 - r1))
    (hga : ga = round radix2 (FLX_exp prec) (Znearest choice) (gat + be2))
    (hbe2z : be2 = 0) :
    a * b + c = r1 + ga + al2 := by
  have hp0 : 0 < prec := by omega
  have hValid := FLX_exp_valid prec hp0
  -- L1: be1 − r1 ∈ F
  have hL1 : generic_format radix2 (FLX_exp prec) (be1 - r1) :=
    errfma_gat_exact prec hp choice Fc hu1 hu2 hal1 hbe1 hr1
  -- gat = be1 − r1
  have hgat_eq : gat = be1 - r1 := by
    rw [hgat]; exact round_generic radix2 (FLX_exp prec) (Znearest choice) hL1
  -- ga = gat (since be2 = 0 and gat ∈ F)
  have hga_eq : ga = be1 - r1 := by
    rw [hga, hbe2z, add_zero, hgat_eq]
    exact round_generic radix2 (FLX_exp prec) (Znearest choice) hL1
  -- be1 = u1 + al1 (β2 = 0)
  have hbe1_eq : be1 = u1 + al1 := by rw [hbe2z] at hbe2; linarith
  -- algebra
  rw [hga_eq, hal2, hu2, hbe1_eq]; ring

end LeanFlocq
