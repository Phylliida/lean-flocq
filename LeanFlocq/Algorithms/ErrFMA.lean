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
- **E2** (pending): the crux exactness lemmas.
- **E3** (pending): assembly into `a·b + c = r1 + r2 + r3`.

## E2 roadmap (from the paper pass — Boldo–Muller 2011, IEEE TC 60(2))

The whole result reduces to proving `γ = β1 + β2 − r1` exactly (then the final
`Fast2Sum`/`TwoSum` splits `γ + α2` into `r2 + r3` and `a·b+c = r1+r2+r3`).
Since `γ = round(round(β1 − r1) + β2)`, this needs two exactness lemmas:
  - **L1**: `round(β1 − r1) = β1 − r1`   (i.e. `β1 − r1 ∈ F`)
  - **L2**: `round((β1 − r1) + β2) = (β1 − r1) + β2`
Then `γ = (β1−r1)+β2 = β1+β2−r1`, and with the E1 chain `a·b+c = β1+β2+α2` we
get `a·b+c = r1 + γ + α2` (Boldo–Muller Theorem 2's conclusion verbatim).

**Hypotheses at FLX:** radix even (2 ✓) and `prec ≥ 3` (we have `prec ≥ 4`). All
of the paper's non-underflow side conditions (`β^(emin+k) ≤ |·|`, `r1` normal,
`ea+ex ≥ emin+p−1`) are *vacuous* at FLX — that's the payoff of staying FLX.

**Reference proof:** Coq `flocq/src/Pff/Pff.v`, section starting line 23446
("was file FmaErr.v"), theorem `FmaErr` (line 24973) = `a*x+y = r1+ga+al2`,
assembled from `FmaErr_aux1` (case `β2 = 0`, short — `γ = round(β1−r1)` and
`β1−r1 ∈ F` directly) and `FmaErr_aux2` (case `β2 ≠ 0`, the hard one). The
`Pff2Flocq.v` `ErrFMA_correct` (line 1057) is the Flocq-side wrapper that calls
`FmaErr` after bridging formats. This is ~1700 lines of old-Pff-formalism Coq —
the "complex, many subcases" the paper warns about — so E2 is a genuine
multi-session *port* (math, not transcription), not a quick lemma.

**Mathematical engine:** the Pff proof rests on relative-error bounds for
round-to-nearest — `ClosestRoundeLeNormal` (`|round z| ≤ |z|/(1 − u/2)`) and
`ClosestRoundeGeNormal` (`|z| ≤ |round z|·(1 + u/2)`), where `u = β^(1−prec)` —
plus magnitude case analysis tying `ulp(β1)` to `ulp(α1)`/`ulp(u1)`. Our
`Prop/Relative.lean` `u_ro` family is the Flocq-native counterpart of those
relative bounds; L1's representability of `β1 − r1` is the load-bearing step.
-/
import LeanFlocq.Algorithms.TwoProduct
import LeanFlocq.Algorithms.EFT_FLX

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

end LeanFlocq
