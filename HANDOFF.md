# lean-flocq HANDOFF

A working port of [Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) to Lean 4 + Mathlib.
This document is for whoever picks this up next — possibly future-me in a different
session, possibly someone else.

## Status (as of commit `acf5611`+)

> **Latest: got Shewchuk's paper (`lean-flocq/shewchuk.pdf`) and ported the grow-preservation
> building blocks (Shewchuk Theorem 10).** His `GROW-EXPANSION` proof rests on two facts, now in
> (0 sorries): **Lemma 1** (`roundN_add_err_le_left/right`, `twoSumLo_abs_le`) — the round-nearest
> error of `a+b` is `≤` either operand, straight from `round_N_pt` (the nearest float is no farther
> than the float `a`, at distance `|b|`), so each residual `|hᵢ| ≤ |eᵢ|`; and **magnitude-monotonicity
> of nonoverlapping** (`nonoverlapping_of_witness_le` / `nonoverlapping_extract` / `nonoverlapping_shrink_left`)
> — shrinking the dominated operand keeps it nonoverlapping with the larger. **Remaining: the inductive
> assembly** (list-level nonoverlapping-increasing predicate + `grow` preserves it). Roadmap with
> Shewchuk's exact invariant is recorded below ([§ GROW-EXPANSION roadmap](#grow-expansion-roadmap)).

> **Earlier: the 2-adic bridge — dyadic packing ⟹ sign-readable (0 sorries, general radix).**
> The list-level consequence of nonoverlapping is now proved: `multipleOfPow_le_abs` (a nonzero
> multiple of `β^s` has `|·| ≥ β^s`); **`dyadic_kernel`** (the genuine 2-adic lemma:
> `e = m·β^t, |e| < β^s, t ≤ s ⟹ |e| ≤ β^s − β^t`, via integer floor `|m| ≤ β^(s−t)−1` through
> `IZR_Zpower`); `DyadicSep` (the strongly-packed form — each head a multiple of `β^s` whose
> power exceeds the total magnitude below it); **`dyadicSep_headDom`** (the bridge: packed +
> nonzero head ⟹ `HeadDom`, so the whole sign is read off the head) + `dyadicSep_sign`;
> **`dyadicSep_cons`** (kernel-powered builder — prepend a dominant head, the kernel gives the
> `β^cexp(g)` headroom) + `dyadicSep_pair` (2-element base). So a packed expansion is
> sign-readable *and* packed expansions can be built up. **Next (the remaining hard chaining):**
> `grow`/`fast_expansion_sum` *produce* packed/nonoverlapping output across a sweep (Shewchuk
> Theorem 10) — that connects multi-component `det2` to `dyadicSep_sign`.

> **Earlier: began the *faithful* grow-preservation port — the
> bit-level `Nonoverlapping` predicate.** Key finding worth carrying: **our `Separated`
> (½·ulp chain) is too strong to be preserved by `grow`.** A sweep produces residuals at the
> *same* scale (both `≲ ½ulp` of the running carry) — mutually *bit*-nonoverlapping (disjoint
> bit ranges) but **not** ulp-chain separated; even the weaker `|y| < ulp(x)` fails (a residual
> that is a power of two has its lsb far above its `cexp`). So preservation genuinely needs
> Shewchuk's bit-level **nonoverlapping**, which I've now started (0 sorries, general radix):
> `MultipleOfPow` + `multipleOfPow_cexp` (a float is a multiple of `β^cexp`); `Nonoverlapping`
> (Shewchuk existential — one operand a multiple of `β^s`, the other strictly below `β^s`) +
> symmetry/zero; `nonoverlapping_of_abs_lt_ulp` (`|y| < ulp(x)`, `x∈F` ⟹ NO, witness `cexp x`);
> **the atom** `round_residual_nonoverlapping` (`◦v` and `v−◦v` are nonoverlapping, via
> `|residual| ≤ ½ulp < ulp`) + `twoProd/twoSum_nonoverlapping`; `separated_pair_nonoverlapping`
> bridges the old invariant to the new. **Next (the hard chaining):** the list-level NO invariant
> + its **2-adic `HeadDom` bridge** (`Σ|tail| < 2^lsb(head)` via disjoint bit-ranges — needs the
> trailing-zeros/2-adic valuation), then `grow`/`fast_expansion_sum` *preserve* NO (Shewchuk
> Theorem 10). That is the genuinely multi-session part.

> **Earlier this session (2026-06-05): Stage 2 of expansion arithmetic — sign-reading keystone
> + the `Separated` structural-invariant foundation.** `Expansion_FLX.lean` now has, 0 sorries:
> - **Consumer side (sign-reading):** `HeadDom h t := Σ|t| < |h|`, `headDom_sign` (**keystone**
>   — `sum ≠ 0` ∧ `sign(sum) = sign(h)`), `headDom_approx` (`|sum − h| < |h|`, the filter
>   primitive); grounded by `round_residual_headDom` ⟹ `twoProd_sign`/`twoSum_sign`.
> - **Structural invariant (op-preservation foundation):** `SeparatedFrom`/`Separated` — the
>   sorted, largest-first ulp-separation chain `|eᵢ₊₁| ≤ ½·ulp(eᵢ)` (value-based
>   sorted+nonoverlapping); `separatedFrom_abs_sum_le` (the technical heart: `Σ|tail| ≤ ulp(prev)`
>   by exact geometric domination); `ulp_lt_abs_FLX` (prec≥2: `ulp x < |x|`); **`separated_headDom`**
>   (Separated + nonzero head + tail-in-F + prec≥2 ⟹ HeadDom — bridges structure → keystone),
>   `separated_sign`; base case `round_residual_separated` + `twoProd/twoSum_separated`.
>
> **Deliberate order:** define the invariant the sweep must maintain, prove it ⟹ sign-readable,
> discharge the base case — *then* the hard chaining. **Next (the hard arc): preservation —**
> prove `grow`/`fast_expansion_sum` *maintain* `Separated` (Shewchuk's bit-level sweep theorems,
> radix 2). That connects multi-component `det2` to `separated_sign` for a full robust `orient2d`.
> (Caveat: the *simple* Stage-1 `expansionSum`/`scale` don't produce `Separated` results — the
> faithful Shewchuk algorithms or a `compress`/renormalize do; that's part of the same arc.)

> **Earlier session (2026-06-02, later): started the *predicate* layer that consumes
> all six EFTs — Shewchuk floating-point expansion arithmetic.**
> `Algorithms/Expansion_FLX.lean` builds the **exactness layer** (Stage 1), 0 sorries,
> **general radix**: an expansion is a `List ℝ` of FLX floats whose exact `List.sum` is
> the value, and `growExpansion` (Shewchuk's O(m) sweep), `expansionSum` (O(m·n)
> grow-fold), `scaleExpansion` (per-component split) are each proved **sum-exact**
> (`Σ grow(e,b)=b+Σe`, `Σ(e⊕f)=Σe+Σf`, `Σ scale(e,b)=b·Σe`) and **`Expansion`-preserving**.
> Capstone `det2`: `Σ det2(a,b,c,d) = a·d − b·c` *exactly* — the `orient2d` kernel.
> Two things worth carrying forward:
> 1. **The exactness theory needs no operational Dekker kernel — only the *residual-in-format*
>    facts `plus_error` / `mult_error_FLX`** (the `hi+lo` split with `lo := (a∘b) − ◦(a∘b)`
>    makes sum-preservation *definitional*; the EFT content is purely the invariant
>    maintenance). Hence **no radix-2 restriction** on the value theory — it's general radix.
> 2. **Stage 2 (the nonoverlapping/nonadjacent invariants, `fast_expansion_sum`, sign-reading,
>    `compress`) is deliberately deferred** — that structural theory is what makes the predicates
>    *adaptive/fast*, not what makes them *correct*. Stage 1 already gives exact determinants.
>    (Lean-4.25 gotcha banked: section variables used *only in proof bodies* are **not**
>    auto-included; use `include hp in` — matches the codebase's explicit-arg convention.)
>
> **Latest session (2026-06-02): the Kahan compensated discriminant `b·b − a·c` is COMPLETE
> end-to-end** — Boldo §3 + §4, the real *and* floating-point tests, **all orientations,
> unconditional** (`disc_branch_fp_test_full`), going *beyond* the paper (which proves only the
> WLOG case). The FP-test capstone covers `q<p`, `p<q`, and `p=q` for the *actual* rounded test
> `◦(p+q) ≤ ◦(3·◦(|p−q|))`, within `2·ulp(d)`, no WLOG.
>
> Two things worth carrying forward from how the `p<q` orientation got done:
> 1. **The `round_N_opp` reflection does NOT reduce `p<q`→`q<p`** — product-rounding ties make
>    `◦_cr(a·c) ≠ ◦_c(a·c)`, so the reflected output `≠ −d`. (I'd over-claimed it was clean; the
>    walk-back is what surfaced the cheaper route.) It's a genuine hand mirror — the same tie
>    subtlety §3 hit with `disc_corr_particular_lo`.
> 2. **But the mirror was cheap: the *pure-`(p,q)`* sub-lemmas — `disc_fp_lemma6`, the crux
>    `disc_fp_ulp_gt_impossible`, `disc_fp_lemma10/11`, `disc_fp_p_le_3q` — are reused by *swapping
>    their `p`/`q` arguments*, so the crux (hardest lemma in the paper) was never re-derived.** Only
>    the sign-sensitive assemblies got `_lo` mirrors (`disc_fp_lemma5/7/12_lo`,
>    `disc_fp_first/second_disagreement_lo`; `d=◦(p−q)<0`, `|d|=q−p`, `|m|`-handling via
>    `ulp_opp`/`abs_round_ge_generic`). Sign-agnostic δ-decomposition factored into
>    `disc_fp_second_core` (this also fixed a heartbeat timeout from the bigger `p<q` context).
>    `p=q` is degenerate (benign ⟹ `p=q=0` via `eq_0_round_0_FLX`+`ulp_FLX_0`; correction ⟹
>    `d=◦(dp−dq)`). Full mechanics in the discriminant section below.

**Coq's `Core/` is fully ported.** Plus the structural part of `IEEE754/Binary.v`
(types, predicates, Bopp/Babs/Bcompare, boundedness, rounding modes,
`bounded_canonical_lt_emax`), **all five files of `Calc/`** — `Bracket`,
`Round`, `Operations`, `Div`, `Sqrt` — **all of `Prop/Relative.v`** including
the unit-roundoff `u_ro/(1+u_ro)` family, **all of `Prop/Sterbenz.v`**,
**all of `Prop/Mult_error.v`**, **all of `Prop/Plus_error.v`** including
`FLT_plus_error_N_ex`, **all of `Prop/Div_sqrt_error.v`** — the keystones
plus the full sqrt error family (`sqrt_error_N_FLX[_ex/_round_ex]`,
`sqrt_error_N_FLT[_ex/_round_ex]`) and the `format_REM` family
(`format_REM_aux`, `format_REM`, `format_REM_ZR`, `format_REM_N`),
**all of `Prop/Round_odd.v`** including the no-double-rounding capstone
`round_N_odd` (and its positive-x core `round_N_odd_pos`),
**the entire main arc of `Prop/Double_rounding.v`** — core mid-rounding,
multiplication arc, bridge, sqrt arc, plus/minus arc, division arc, plus
**both secondary radix tracks: sqrt `radix_ge_4` and plus/minus
`radix_ge_3`** — all with FLX/FLT/FTZ instantiations for every keystone
(`round_round_mult/sqrt/plus/minus/div` and `round_round_sqrt_radix_ge_4`
and `round_round_plus/minus_radix_ge_3` plus their concrete-format
corollaries each), and **the encoding/decoding core of `IEEE754/Bits.v`**
including both round-trip theorems. The IEEE 754 binary
encoding is now a proven bijection between `binary_float` and integers in
`[0, 2^(mw+ew+1))`.

**Plus the first two error-free transformations of the CAD-direction
roadmap: `Fast2Sum` (radix 2, FLT, round-to-nearest) gives exact `s + e
= a + b` under `|b| ≤ |a|`, and `TwoSum` removes the precondition via a
magnitude-comparison branch into Fast2Sum on the larger side. Both
live at FLT (gradual underflow) using Pff's three-case structure
(`Dekker1_FTS`/`Dekker2_FTS`/`Dekker3`).**

**Veltkamp splitting (third algorithm) is COMPLETE at FLX (both sides).**
The bundled keystone `Veltkamp_aux_FLX_complete` is proved: for `x > 0` in
F(FLX, prec), `2 ≤ s ≤ prec − 2`, both the error bound
`|x − hx| ≤ β^(s + cexp x)/2` AND the format constraint `hx ∈ F(prec − s)`
hold. The proof structure:

**Error-bound side** (`Veltkamp_aux_FLX`) ports Pff's `eqLe` dichotomy:
- **`hxExact_FLX`**: `hx = q + p` exactly via Sterbenz on `(p, -q)`.
- **Case A** (`mag(x·C) = m+s`): direct half-ulp + F upper bound argument.
- **Case B** (`mag(x·C) = m+s+1`): integer-mantissa case split on M_x:
  - Interior (M_x ≤ β^prec − β − 1): `(M_x + β) · β^(s+cexp x) ∈ F` dominates `|q|`.
  - Boundary (M_x ≥ β^prec − β): Pff's V (`-q ≤ β^(s+m)` via J1 + `round_N_le_midp`),
    then sub-case-split on `q = -β^(s+m)` using `error_le_half_ulp` or explicit bounds.

**Format-side** (`Veltkamp_hx_format_FLX`) ports Pff's `eqGe` argument.
Load-bearing piece: `|q| ≥ β^(s+m−1)` (equivalently `cexp q ≥ s + cx`)
via three branches:
- **Branch 1 (comfortable)**: when `x ≥ β^cx · (β^(prec−1) + β)`, rounding
  errors fit cleanly: `|q| ≥ x·β^s − β^(s+1+cx) ≥ β^(s+m−1)`.
- **Branch 2a (β−1 specific M_x)**: construct `g₁ = F2R⟨β^(prec−1) + β^(prec−s−1) + 1, s+cx⟩`
  ∈ F(prec) with `g₁ ≤ x·C`, hence `g₁ ≤ p`, hence `|q| ≥ β^(s+m−1)`.
- **Branch 2b (exact bpow boundary)**: when `x = β^(m−1)`, `x·C` is itself in F
  so `p = x·C` and `q = −β^(s+m−1)` exactly.

The three branches combine in `Veltkamp_eqGe_FLX`, dispatching via integer-
mantissa discreteness (`Veltkamp_x_lb_above_bpow_FLX`: from `x > β^(m−1)`
and integer mantissa, `x ≥ β^(m−1) + β^cx`).

The format-side proof then expresses `p` and `q` as integer multiples of
`β^(s+cx)` (`Veltkamp_p_at_scx_FLX`, `Veltkamp_q_at_scx_FLX`, both using
`F2R_change_exp`), bounds `|M_total| ≤ β^(prec−s)`, and dispatches:
- `|M_total| < β^(prec−s)` → `generic_format_F2R` with `mag(hx) ≤ m`.
- `|M_total| = β^(prec−s)` → `hx = β^m` → `generic_format_bpow`.

A single unified format theorem `Veltkamp_hx_format_FLX` covers what Pff
splits into Case A and Case B: the proof only needs case-agnostic facts
(eqGe, `mag(x·C) ≥ m+s`, and the unified `Veltkamp_aux_FLX` error bound).

**Plus `Veltkamp_tail_FLX`**: `x = hx + tx` exactly with `tx ∈ F(FLX, s)`.
Strategy: express `x = M_x · β^cx` (canonical) and `hx = ((Mq+Mp) · β^s) · β^cx`
(from the format-side `s+cx` decomposition); hence `x − hx = M_tx · β^cx`
with `M_tx = M_x − (Mq+Mp) · β^s`. The half-ulp error bound gives
`|M_tx| ≤ β^s/2`, so `|M_tx| < β^s` (integer cast). The same `(M_tx, cx)`
witness gives both `x − hx ∈ F(FLX, s)` and `x − hx ∈ F(FLX, prec)` (since
`s + cx ≤ cexp_{prec}(x − hx)` follows from `s ≤ prec`). The latter
inclusion lets `round_{prec}` act as identity on `x − hx`, so
`tx = round(x − hx) = x − hx`, giving `x = hx + tx`.

**Plus the `∃ choice'` existence theorem (Pff `Veltkamp`) is COMPLETE.**
`Veltkamp_FLX` (2026-05-19, commit `1aee429`): for `x > 0` in F(FLX, prec)
with `2 ≤ s ≤ prec − 2`, `∃ choice'` such that
`round_{prec−s, Znearest choice'} x = Veltkamp_hx_FLX beta prec choice s x`.

Construction: `choice' k := decide (DN < hx)` where `DN = round_{prec−s, Zfloor} x`.
The proof reduces to integer equality `Znearest choice' sm = M_h` (where
`sm = M_x · β^(−s)`). From `M_h_close`, `|sm − M_h| ≤ 1/2`. Case-split:
- Strict `< 1/2` → `Znearest_imp` picks `M_h` directly (any choice works).
- Tie `= 1/2` → two subcases:
  - `sm = M_h + 1/2`: q = M_h, DN = hx, choice' = false. Znearest picks ⌊sm⌋ = M_h.
  - `sm = M_h − 1/2`: q = M_h − 1, DN < hx, choice' = true. Znearest picks ⌈sm⌉ = M_h.

This means Veltkamp at FLX is **functionally complete**: aux (error
bound) + format + tail + existence + `Veltkamp_Even` (both odd AND
even radix, unconditional). See [§ Veltkamp_Even scope](#veltkamp_even-scope)
below for the parity-argument structure.

**Plus `Veltkamp_Even` at FLX is COMPLETE — BOTH odd and even radix,
unconditional.** `Veltkamp_Even_FLX_even_radix_NE` (2026-05-31, commit
`6120e11`): for even `β`, the NE choice in the Veltkamp algorithm
satisfies `round_NE_{prec−s} x = Veltkamp_hx_FLX β prec (fun n =>
decide (¬ Even n)) s x` with no remaining parity hypothesis. Combined
with the odd-radix theorem below, this closes the Veltkamp_Even arc
at FLX completely.

**Odd-radix `Veltkamp_Even`**: `Veltkamp_Even_FLX_odd`
(2026-05-19): for odd `β`, `β^s` is odd, so `β^s/2` is non-integer.
The integer-valued `|M_x − M_h · β^s| ≤ β^s/2` becomes the strict
`< β^s/2`, hence `|sm − M_h| < 1/2`: no tie at coarser precision.
Therefore `round_NE_{prec−s} x = Veltkamp_hx_FLX β prec choice s x`
for ANY internal tie-breaker `choice`. Stronger generic form
`Veltkamp_Even_FLX_odd_radix`: any `Znearest choice'` (not just NE)
matches the algorithm's `hx` at odd radix.

**Plus the Rnd_N_pt foundation for full `Veltkamp_Even`**:
`Veltkamp_hx_Rnd_N_pt_FLX` (2026-05-19): combines `Veltkamp_FLX`
existence with `round_N_pt` to give that `hx` is a closest
representable at `prec − s`. This is one of the two pieces needed to
upgrade from `Rnd_N_pt` to `Rnd_NE_pt`; the other piece is the
even-radix parity-at-tie argument (Pff `VeltkampEven1`, ~292 Coq
lines).

**Plus the unified `Veltkamp_Even_FLX` theorem (conditional form)**:
`Veltkamp_Even_FLX` (2026-05-19): takes `Odd β.val ∨ Rnd_NE_pt β
(FLX_exp (prec-s)) x hx` as hypothesis and concludes `round_NE_{prec-s}
x = hx`. For odd radix the disjunction discharges automatically (via
`Veltkamp_hx_Rnd_NE_pt_FLX_odd`). For even radix the `Rnd_NE_pt`
witness IS the open work — it requires showing either NE_prop holds
(parity-at-tie) or uniqueness (no-tie). Helper:
`Veltkamp_Even_FLX_of_Rnd_NE_pt` does the round-NE-equality bridge
via `Rnd_NG_pt_unique` (uniqueness of `Rnd_NE_pt`).

**Plus the even-radix path-2 dichotomy reduction** (2026-05-20):
`Veltkamp_hx_NE_prop_FLX_even_radix` reduces the parity argument from
"M_total even at every coarse tie" (Pff's full `VeltkampEven1`) to
"M_total even only when β^(prec−s−1) ≤ |M_total| < β^(prec−s)" (the
"hard interior" subcase corresponding to `mag(hx) = mag(x)`). The
boundary case `|M_total| = β^(prec−s)` discharges automatically since
`hx = ±β^m` has canonical mantissa `±β^(prec−s−1)`, divisible by β; the
low-mag case `|M_total| < β^(prec−s−1)` discharges automatically since
`mag(hx) < m` lowers the canonical exponent by ≥1, leaving a factor of
β in the canonical mantissa.

The `Rnd_NE_pt` builder was then refactored to internally case-split on
tie status at coarser precision: no-tie via uniqueness through
`Rnd_N_pt_unique` (with sub-case for `x ∈ F(prec−s)` via idempotency),
tie via the `NE_prop` dichotomy. The hypothesis tightened to the
provable form "Even M_total at coarse tie + hard interior."
`Veltkamp_Even_FLX_even_radix` is the top-level theorem taking this
tie-conditional parity hypothesis.

**Plus eight Pff-style helpers for the parity port** (2026-05-20):
faithful port of Pff `VeltkampEven1` lines 14375–14406 structure,
each compiled piece by piece via `lake build`:
- `Veltkamp_bpow_plus_one_odd`: `β^s + 1` odd for even β, `s ≥ 1`.
- `Veltkamp_tie_eps_FLX`: at coarse tie, `x = (M_total + ε/2) · β^(s+cx)`
  for `ε ∈ {−1, +1}`.
- `Veltkamp_xC_form_at_tie`: `x · C = (β^s + 1)(2 M_total + ε)/2 · β^(s+cx)`.
- `Veltkamp_xC_coef_odd`: the coefficient `(β^s + 1)(2 M_total + ε)`
  is odd (product of two odd integers).
- `Veltkamp_Mp_even_via_high_cexp`: when `cexp(p) > scx`, the at-scx
  coefficient `Mp` has a β factor, hence is even.
- `ZnearestE_even_at_midpoint`: at `mx − ⌊mx⌋ = 1/2`, ZnearestE
  returns even integer.
- `Veltkamp_p_cexp_high_FLX`: when `mag(x · C) = m+s+1`, `cexp(p) ≥
  s+cx+1` (via `round_DN(x·C) ≥ β^(m+s)` from `round_ge_generic`).
  This is the boundary-analysis lemma — Pff's `Veltkamp_aux_aux`
  restricted to p, but using Lean's `Rnd_N_pt_DN_or_UP` for a much
  shorter proof.
- `Veltkamp_xC_sm_at_midpoint_FLX`: combines `Veltkamp_p_cexp_high_FLX`
  contrapositive (forcing `mag(x · C) = m+s` when `cexp(p) ≤ s+cx`)
  with `xC_form_at_tie` to derive `scaled_mantissa(x · C) − ⌊⌋ = 1/2`.

**Plus the main Mp parity theorem (2026-05-20)**:
`Veltkamp_Mp_even_at_tie_hard_NE_FLX` proves `Even Mp` at coarse tie +
hard interior + NE choice (`fun n => decide (¬ Even n)`).
Case-splits on `cexp(p) ?= s+cx`:
- High: β factor via `Veltkamp_Mp_even_via_high_cexp`.
- Equal: derives `mag(x·C) = m+s`, `scaled_mantissa(x·C)` half-integer,
  ZnearestE picks even, `Mp = ZnearestE(sm)` via the round formula
  expansion (using `Znearest choice = ZnearestE` for the NE choice,
  definitionally). The `mul_right_cancel₀` on `β^(s+cx)` gives the
  integer equality cleanly.

This was the structurally harder half (all the helpers above were
designed for it).

**Plus the symmetric Mq parity theorem (2026-05-31, commit `088545f`)**:
`Veltkamp_Mq_even_at_tie_hard_NE_FLX` proves `Even Mq` at coarse tie +
hard interior + NE choice. Mirrors the Mp structure with `x − p` as the
algebraic source instead of `x · C`:

- `Veltkamp_xmp_form_at_tie`: `x − p = ((2(M_total − Mp) + ε)/2) · β^(s+cx)`.
- `Veltkamp_xmp_coef_odd`: `K' = 2(M_total − Mp) + ε` is odd (ε ±1,
  rest even — INDEPENDENT of Mp's parity).
- `Veltkamp_Mq_even_via_high_cexp`: symmetric high-cexp helper for `q < 0`,
  applied via the Mp version on `-q > 0`.

Main theorem case-splits on `cxmp = cexp(x − p)` vs `s + cx`:
- `cxmp ≥ s + cx`: `Mq = Znearest(sm_xmp) · β^(cxmp − (s+cx))`.
  - `d ≥ 1` (`cxmp > s + cx`): β factor, even.
  - `d = 0` (`cxmp = s + cx`): midpoint argument. `sm_xmp = K'/2`
    (half-integer, since K' odd). `ZnearestE` picks even.
- `cxmp < s + cx`: contradiction. `sm_xmp = K' · β^e / 2` is integer
  (β even, e ≥ 1, K' odd). `Znearest` returns sm_xmp. Scale-shift forces
  `Mq = K'/2`, contradicting K' odd.

Key cleanup that simplified the proof: using `scaled_mantissa_mult_bpow`
(the `sm · β^cexp = x` identity from `Generic_fmt.lean`) avoided going
through Pff's `ClosestImplyEven_int` and dodged the rw-cascade in cexp
arguments. The whole Mq proof landed in ~200 lines, faster than the
estimate.

**Plus the unconditional NE wiring** (`Veltkamp_Even_FLX_even_radix_NE`):
discharges the tie-conditional parity hypothesis by combining Mp and Mq.
Structure:
1. Get `Mp` via `Veltkamp_p_at_scx_FLX` (`p = Mp · β^(s+cx)`).
2. Get `Mq` via `Veltkamp_q_at_scx_FLX` (`q = Mq · β^(s+cx)`).
3. `hxExact_FLX` gives `hx = q + p`, hence `M_total = Mq + Mp`.
4. Get `ε` from the tie identity (`Veltkamp_tie_eps_FLX`).
5. Apply `Veltkamp_Mp_even_at_tie_hard_NE_FLX` → `Even Mp`.
6. Apply `Veltkamp_Mq_even_at_tie_hard_NE_FLX` → `Even Mq`.
7. `Even Mq + Even Mp → Even (Mq + Mp) = Even M_total`.

**Net Veltkamp_Even arc landing**: ~260 lines added (Mq main +
Mq high-cexp + algebraic helpers + unconditional wiring) on top of the
existing ~500-line Mp infrastructure. Veltkamp.lean grew from ~3843 to
4161 lines.

**Dekker / TwoProduct (fourth algorithm) — COMPLETE for `radix 2 ∨ Even prec`
(all IEEE variants), both bare and machine form (2026-05-31).**
`Algorithms/TwoProduct.lean` (805 lines). The goal — `x·y = round(x·y) + e`
exactly (FMA-free Dekker), at FLX, under `radix 2 ∨ Even prec` (binary formats
are radix 2 incl. binary64's odd `prec=53`; decimal formats have even prec) —
is reached. The algorithm Veltkamp-splits both `x` and `y` into half-precision
parts, forms four sub-products, and reconstructs the error through a 4-step
summation chain. Two headline theorems:
- **`TwoProduct_FLX`** (bare products): `x·y = round(x·y) +
  round(round(round(round(hx·hy − r) + hx·ty) + tx·hy) + tx·ty)` for
  `s = ⌈prec/2⌉` (`prec ≤ 2s ≤ prec+1`) under `beta.val = 2 ∨ 2s = prec`.
- **`TwoProduct_FLX_machine`** (the literally-faithful machine algorithm):
  every sub-product is a *rounded* multiply `round(hx·hy)`, … — what a real
  FMA-free kernel computes, hence what CAD's predicates consume. Proved by
  rewriting the four product-rounds to bare (three always exact via
  `generic_format_FLX_mult`; `tx·ty` via the radix-2/even dichotomy) and
  applying `TwoProduct_FLX`.

**Key structural insight:** the bare chain never uses the four product-exactness
facts — each summation step rounds exactly via *grid magnitude bounds* +
`mult_error_FLX`, so `2s = prec` only ever bought magnitude bookkeeping, and the
chain is radix-agnostic given `s = ⌈prec/2⌉`. The `radix 2 ∨ Even prec`
condition's real role is making the *machine* form's `tx·ty` product exact.

Built in chunks:

- **Chunk 1 DONE** (`generic_format_FLX_mult`): `F(p1)·F(p2) ⊆ F(p1+p2)`.
  Product of a `p1`-digit and a `p2`-digit value is exact at precision
  `p1+p2`. Proof via `F2R⟨Mx·My, cx+cy⟩` and `mag(x·y) ≤ mag(x)+mag(y)`
  (no explicit mantissa bound needed — `generic_format_F2R` only wants
  `cexp(x·y) ≤ cx+cy`). Makes 3 of 4 sub-products exact unconditionally;
  the 4th (`tx·ty`) exact for even prec.
- **Chunk 3 DONE** (`Veltkamp_split_FLX_general`): lifts the split
  (`x = hx+tx`, `tx ∈ F(s)`, `hx ∈ F(prec−s)`) to ALL signs and zero.
  Negative `x` reduces to `−x > 0` under the flipped tie-breaker
  `fun t => !c(−(t+1))` via `round_N_opp`; four step-commutation lemmas
  (`Veltkamp_{p,q,hx,tx}_FLX_neg`) carry it through; zero collapses
  every step via `round_0`.
- **Chunk 4 DONE** (`TwoProduct_FLX` + `TwoProduct_FLX_main`): the full
  magnitude chaining, landed exactly as the paper-scoped plan predicted.
  Structural + algebraic bedrock:
  - `generic_format_FLX_of_mult_bpow` — **grid lemma**: `v = M·β^E` with
    `|v| < β^(prec+E)` is in `F(prec)`. The workhorse for the summation
    steps (every partial sum lives on a common grid).
  - `Veltkamp_struct_FLX` (added to **Veltkamp.lean**, exposed from the
    private `Veltkamp_M_h_close_FLX`): `x = M_x·β^cx`, `hx = M_h·β^(s+cx)`,
    `|M_h| ≤ β^(prec−s)`, `|M_x − M_h·β^s| ≤ β^s/2`. The structural
    mantissa bounds that drive every magnitude estimate.
  - `Veltkamp_struct_FLX_general` — the same, all nonzero signs (negates
    both mantissas via Chunk-3 commutation + `cexp_opp`).
  - `round_mul_Fs_exact` — with `2s = prec`, `F(s)·F(s)` rounds exactly.
  - `round_add_grid_exact` — **summation-step engine**: `round(u+w) = u+w`
    when `u,w` share grid `β^E` and `|u+w| < β^(prec+E)`.
  - `twoproduct_expand_exact` — `x·y = hx·hy+hx·ty+tx·hy+tx·ty` exactly
    (`linear_combination` of the splits) + all four products exact.

  Magnitude bookkeeping helpers (the chaining layer):
  - `bpow_coarsen` — moves `M·β^E_big` onto a coarser grid `β^E_small`
    (centralizes all the `toNat`/`IZR_Zpower` bookkeeping).
  - `abs_prod_bpow_le`, `prod_bound_medium` (`|·| ≤ ½β^(prec+s+E₀)` for the
    medium products `hx·ty`, `tx·hy`), `prod_bound_small` (`|·| ≤
    ¼β^(prec+E₀)` for `tx·ty`).
  - `abs_sub{1,2,3}_le` — triangle inequalities for the running-sum bounds.
  - `Veltkamp_parts_zero` — the parts of `0` are `0` (for the zero dispatch).

  The chain itself (`TwoProduct_FLX_main`, nonzero case):
  - `r = round(x·y)` is pinned to the **coarse grid** `cexp(x·y)` via
    `cexp_round_ge` (the `mag(round v) ≥ mag v` fact), with a zero-`r`
    fallback giving `M_r = 0`.
  - `S1 = hx·hy − r` ∈ F via the grid lemma at `cexp(x·y)`: bound
    `|S1| ≤ (7/4)β^(2prec−2+E₀) < β^(prec+cexp(x·y))`, closing because
    **7/4 < 2 ≤ β** (uses `s ≤ prec−2` and `mag(x·y) ≥ mag x + mag y − 1`).
    S1 must use the coarse grid — on `s+E₀` the two medium products sum to
    exactly the threshold and strict `<` fails.
  - `S2, S3` ∈ F at grid `s+cx+cy`, closing via `2·C2 ≤ C` (since `β^s ≥ 2`).
  - `S4 = x·y − r` ∈ F via `mult_error_FLX` + `generic_format_opp` — no grid.
  - Chain via `round_add_grid_exact` (S1) and `round_generic`∘grid (S2/S3),
    then `rw [ht1,ht2,ht3,ht4]; ring` collapses the nested rounds.
  - Public `TwoProduct_FLX` dispatches `x=0 ∨ y=0` (everything is `0`) to
    the main nonzero theorem.

  No real wall this session — every compiler error was mechanical (a cast
  already in real-abs form so `Int.cast_abs` was the wrong tool; `rw`
  clobbering `r` inside its own RHS → `conv_lhs`; a metavariable not yet
  fixed when an inline `rw` ran → named `have`; two `nlinarith` calls
  spinning for want of their key hypothesis → direct
  `mul_le_mul_of_nonneg_right`). The payoff of scoping the magnitude
  argument fully on paper before typing it.

- **Chunk 2 DONE** (`round_tt_exact_radix2`, the Pff `Dekker2` crux — landed
  in ~70 lines, not the ~350 estimated): at radix 2 with `s = ⌈prec/2⌉`,
  `round(tx·ty) = tx·ty` even at odd precision. The estimate was for the
  classical mantissa-carry argument; with the Veltkamp half-ulp tail bound
  `|M_tx| ≤ β^s/2 = 2^(s-1)` already in hand, it collapses to `|M_tx·M_ty| ≤
  2^(2s−2) ≤ 2^(prec−1)`, putting `tx·ty = (M_tx·M_ty)·2^(cx+cy)` strictly
  under the grid threshold `2^(prec+cx+cy)` — the grid lemma finishes it.
  Then **the chain was generalized** from `2s = prec` to `prec ≤ 2s ≤ prec+1`:
  - `prod_bound_medium` now takes the high-part bound `|·| ≤ β^(prec−s)`
    (drops `2s=prec`); `prod_bound_small` concludes `¼β^(2s+E₀)` (parity-general).
  - `TwoProduct_FLX_main` derives the bilinear expansion straight from the two
    splits (no `twoproduct_expand_exact`, which needed `2s=prec`); the `tx·ty`
    grid bound goes through `hptt2` (`β^(2s+E₀) ≤ 2·β^(prec+E₀)`, equality at
    radix-2 odd prec) and `h4C2` (`β^s ≥ 4`).
  - `four_le_bpow` extracted as a standalone lemma — its `nlinarith` timed out
    at 200k heartbeats inside the now-larger `TwoProduct_FLX_main` context
    (context-pollution lesson again: lift `nlinarith`/`polyrith` out of big
    proofs).

  `round_mul_Fs_exact` (even prec) and `round_tt_exact_radix2` (radix 2)
  together give `tx·ty` exact under the full `radix 2 ∨ Even prec`, which is
  exactly what `TwoProduct_FLX_machine` dispatches on.

**ErrFMA (fifth algorithm) — E2 COMPLETE (full `FmaErr` proved Flocq-native),
only the `r1+r2+r3` normalization remains (2026-05-31).** The error-free
transformation for the FMA: given `a, b, c`, the FMA computes `r1 = round(a·b +
c)`, and the error `a·b + c − r1` (which generally does *not* fit in one float)
is reconstructed as `γ + α2`, two floats, with **`a·b + c = r1 + γ + α2`
exactly** (`ErrFMA_correct` = Boldo–Muller 2011 Theorem 2 / Pff `FmaErr`). At FLX,
radix 2, `prec ≥ 4`. **Pff's ~1700-line `FmaErr` (with its MSB/LSB
`Midpoint_aux`/`be2MuchSmaller` machinery) is replaced by ~640 Flocq-native lines
with NO MSB/LSB.** Built in stages:

- **E0 DONE** (`Algorithms/EFT_FLX.lean`): ErrFMA stacks TwoProduct + TwoSum +
  Fast2Sum, all needed at one format — and TwoProduct is FLX-only, so the whole
  thing lives at FLX. The FLX Fast2Sum/TwoSum **existed** (commits `a7d8eff`,
  `cc7ad6c`) before being ported to FLT in `b5e9d48`; recovered here as
  `Fast2Sum_FLX_correct` + `TwoSum_FLX_correct` (`_FLX`-suffixed to coexist with
  the FLT versions). Proofs compiled verbatim against the current Core.
- **E1 DONE** (`Algorithms/ErrFMA.lean`): existential EFT interfaces
  `twoproduct_eft` / `twosum_eft` (high word `= round(·)`, low word `∈ F`, sum
  exact — hiding the branching low-word construction) and **`ErrFMA_chain`**: the
  exact algebra `a·b + c = β1 + β2 + α2` from the three EFTs, where `β1 =
  round(round(a·b) + round(c + u2))`.
- **E2 the round-minus-round engine DONE** (`Algorithms/RoundMinusRound_FLX.lean`,
  ~370 lines): the Flocq-native form of Pff's `Subexact` —
  **`round_minus_round_nearby_exact_FLX`**: for `a, b ∈ F` and `e` at most half a
  ulp of *each*, `round(a+b) − round(a+b+e) ∈ F`. The two roundings stay within a
  factor of two (same sign) so Sterbenz applies. Supporting: `err_le_uro_round_FLX`
  (output-form relative bound = Pff `ClosestRounde{Le,Ge}Normal`),
  `add_int_mul_bpow_min` + `abs_add_eq_or_ge_two_bpow_min` (a nonzero float-sum is
  a nonzero integer multiple of `β^min(cexp a, cexp b)`, with the boundary/bulk
  dichotomy), `sterbenz_abs` (signed Sterbenz). Boundary case clean at radix 2
  (`a+b = ±2^m` is a float). Needs only radix 2 + `prec ≥ 3`.
- **E2 L1 DONE** (`errfma_gat_exact` = Pff `gatCorrect`): `β1 − r1 ∈ F`. Applies
  the engine with perturbation `α2 = (c+u2) − α1`; `|α2| ≤ |u2| ≤ ½ ulp(u1)`
  (round-nearest closeness via `round_N_pt` with the float `c`) and `α2` is α1's
  own rounding error so `|α2| ≤ ½ ulp(α1)`. Needs only `c ∈ F` (not TwoProduct).
- **E2 β2 = 0 DONE** (`ErrFMA_be2_zero` = Pff `FmaErr_aux1`): `γ = round(β1−r1) =
  β1−r1` (L1 + idempotency), so `a·b+c = r1 + γ + α2` directly.
- **E2 L2 / β2 ≠ 0 — DONE** (`Algorithms/ErrFMA_L2.lean`, 776 lines), Pff
  `FmaErr_aux2`/`gaCorrect`. The Flocq-native replacement for Pff's MSB/LSB
  machinery is **a midpoint argument**, proven complete:
  - `errfma_be2_mult_bpow`: β2 is an integer multiple of `β^min(cexp u1, cexp α1)`
    — straight from `round_repr_same_exp` (rounding a float on grid ℓ stays on
    grid ℓ), **no `plusExact1`/`be2MuchSmaller`-LSB needed** (cleaner than Pff).
  - `errfma_al2_lt_bpow`: `|α2| < β^min(cexp u1, cexp α1)`, from L1's bounds.
  - `nonneg_bpow_mult_lt_eq_zero` / `neg_bpow_squeeze`: the divisibility squeeze
    (a nonneg β^ℓ-multiple `< β^ℓ` is 0) — the heart of the dichotomy.
  - `errfma_be2_eq_bpow_upper` / `errfma_be2_eq_bpow_lower`: the upper/lower
    midpoint cores. `r1 ≠ be1` forces `be1+be2+α2` across a grid midpoint (via
    `round_N_le_midp`/`round_N_ge_midp`), and the squeeze pins β2 to exactly
    `±½ulp` (upper / non-power lower) or `±¼ulp` (the `pred_pos` power-of-β lower).
  - **`errfma_be2_div_dichotomy`**: `β1 = r1 ∨ β2 multiple of β^(cexp β1 − 2)`.
    Combines the cores via a positive dispatcher; `be1<0` sign-reduces through
    `round_N_opp` + flipped tie-breaker (engine's double-flip), `cexp_opp`.
  - **`errfma_ga_exact`** (`gaCorrect`): `(β1−r1)+β2 ∈ F`. `β1=r1` ⟹ `=β2∈F`;
    else β2 is a `β^(cexp β1−2)`-multiple (dichotomy), β1/r1 are coarser multiples
    (r1 via the `Expbe1`/`Expr1` cexp bounds from `round_nearby_factor_two_FLX`),
    and `|(β1−r1)+β2| < β^(cexp β1+1)` closes via `generic_format_FLX_of_mult_bpow`.
  - **`ErrFMA_be2_nonzero`** (`FmaErr_aux2`): L1 + L2 ⟹ `a·b+c = r1+γ+α2`.
- **E2 the full theorem — DONE**: **`ErrFMA_correct`** case-splits β2=0 /
  β2≠0; the β2≠0 edge conditions (`u1,α1,r1 ≠ 0`) are discharged from `β2 ≠ 0`
  (u1=0/α1=0 collapse β2; r1=0 ⟹ `a·b+c=0` ⟹ `be1+be2+α2=0`, and
  `|be1| ≤ 2|β2| ≤ ulp(be1)` forces `be1=0` by the mag bound, hence β2=0).
- **E3 DONE** (`ErrFMA_threefloat` = Pff `Fma_FTS`): **`a·b + c = r1 + r2 + r3`**
  exactly, with `r2, r3 ∈ F` and `r2 = ◦(γ + α2)`. The Algorithm-4 final step is
  `Fast2Sum(γ, α2)`; we use the precondition-free **`TwoSum(γ, α2)`** (same exact
  `r2 + r3 = γ + α2`), so no `|α2| ≤ |γ|` obligation. `α2 ∈ F` via `plus_error(c,
  u2)`; `u2 ∈ F` via `mult_error_FLX(a, b)`.

**ErrFMA is FULLY COMPLETE** — the verified error-free transformation for the FMA,
`a·b + c = r1 + r2 + r3`, all Flocq-native.

**Compensated discriminant `b·b − a·c` (sixth algorithm) — COMPLETE
(2026-06-02): Boldo §3 + §4, real & floating-point tests, all orientations,
unconditional (`disc_branch_fp_test_full`), beyond the paper.**
`Algorithms/Discriminant_FLX.lean`. Kahan's discriminant computes
`b·b − a·c` to relative error `≤ 2u` (and absolute `≤ (β+1)/2` ulps), even under
catastrophic cancellation — the keystone for verified quadratic intersections and
Shewchuk-style adaptive predicates. The published proof (Jeannerod–Louvet–Muller,
*Math. Comp.* 82 (2013), the 2×2-determinant analysis; Boldo 2009 for the
branch-test original) is a grid-level argument. Landed so far, all Flocq-native,
0 sorries:

- **D0 (general radix)** — `disc_fma_error_exact`: the fma error steps
  `RN(x·y − RN(x·y)) = x·y − RN(x·y)` (so `dp,dq` are exact); `disc_prod_error_format`.
- **D1 (general radix)** — `disc_corrected_value`: `(p−q)+(dp−dq) = b·b − a·c`
  exactly (the ErrFMA-chain analog); `disc_sterbenz_exact`: the cancelling
  subtraction is Sterbenz-exact; `disc_p_nonneg`.
- **D2 (general radix)** — `disc_naive_error_bound`: the master decomposition
  `|d − (b·b−a·c)| ≤ u_ro·(|d|+|p|+|q|)` for the naive `d = RN(p−q)`.
- **Relative-error calculus** — ported from Boldo's `flocq/examples/Triangle.v`
  (sibling Kahan triangle-area proof): `rel_err`, `rel_err_{aux,0,opp,init}`.
- **D3 decompositions** — `disc_fma_error_decomp` (symmetric algorithm, 3 sharp
  `v=u_ro/(1+u_ro)` errors) and **`disc_kahan_error_decomp`** (the canonical
  Cook/Kahan algorithm `w=RN(ac), e=w−ac, f=RN(b²−w), x=RN(f+e)`, 2 errors:
  `|x−(b·b−a·c)| ≤ v·(|b²−w| + |f+e|)`, any sign).
- **D3 opposite-sign 2u — DONE**: **`disc_kahan_opp_sign_2u`**: for `a·c ≤ 0`
  (the sum-of-squares `b²+|ac|`, *no cancellation* — the positive-definite case
  CAD predicates hit), the **full** `|x − (b·b−a·c)| ≤ 2·u_ro·|b·b−a·c|`,
  general radix, no format hypotheses. Closes via the 2-error split, `|ac| ≤ D`,
  and the scalar fact `v(2+2v+v²) ≤ 2u` (from `u(1−v)=v`).

**Boldo branch-algorithm `2·ulp(d)` port — IN PROGRESS (have the PDF).** Danielle
supplied Boldo (2009) (`lean-flocq/boldo.pdf`). It proves the *branch* algorithm
`if 3|p−q| ≥ p+q then d=RN(p−q) else d=RN((p−q)+RN(dp−dq))` to `|d−(b·b−a·c)| ≤
2·ulp(d)` (ulps of the result ≈ 4u relative; §8: the `ulp(b·b−a·c)` form is *false*
at powers of two, only `4·ulp(b·b−a·c)` holds; the tight relative-2u is the separate
Jeannerod–Louvet–Muller paper, not in hand). The factor-of-two ulp steps are radix-2
specific, so this arc is at `beta.val = 2`. Ported so far (radix 2 unless noted):
- `disc_branch_subtract_exact` — **Boldo Lemma 1**: branch condition `3|p−q|<p+q`
  (+ `p≥0`) ⟹ `q>0 ∧ p≤2q ∧ q≤2p` ⟹ `p−q` exact (Sterbenz).
- `disc_branch_err_decomp` (general radix) — `δ ≤ ½(ulp d + ulp p + ulp q)` for the
  naive `d=RN(p−q)`, from three half-ulp bounds.
- `ulp_le_ulp_round_FLX` (general) — `ulp x ≤ ulp(RN x)`; `ulp_two_mul_r2` /
  `ulp_half_r2` — radix-2 `ulp(2x)=2ulp(x)`, `ulp(x/2)=ulp(x)/2`.
- **`disc_branch_benign`** (§3.1 DONE) — benign branch `3|p−q|≥p+q` ⟹ `δ ≤ 2·ulp(d)`,
  via `disc_benign_ulp_key` (`ulp p+ulp q ≤ 3·ulp(RN(p−q))`, 3 sign subcases).
- **§3.2 correction-branch machinery (analytic half DONE):**
  `disc_corr_err_decomp` (`δ ≤ ½ulp d + ½ulp g`, `g=RN(dp−dq)`),
  `disc_corr_exact` (**Lemma 3**: `dp−dq` exact ⟹ `δ≤½ulp d`),
  `disc_corr_dpdq_bound` (`|dp−dq| ≤ ½ulp p + ½ulp q`),
  `disc_corr_general` (`|dp−dq|≤½|p−q|` ⟹ `δ≤2ulp d`),
  `disc_corr_far` (`ulp p+ulp q ≤ |p−q|` ⟹ `δ≤2ulp d`),
  `disc_corr_pq_eq` (`p=q` ⟹ `d=RN(b·b−a·c)`, `δ≤½ulp d`).
- **§3.2 Lemma 4 — DONE** (`disc_corr_lemma4`, 2026-06-01): `ulp p = ulp q ⟹ δ ≤ 2·ulp d`.
  The inner `dp−dq` is computed *exactly* via a grid argument, then Lemma 3 closes. Built on:
  - **`disc_diff_on_grid_exact`** (general radix) — the mathematical heart: if `x,y` are
    integer multiples of a common grid `β^E` and `|x−y| ≤ β^(prec+E)`, then `x−y ∈ F`.
    Mantissa `|M| ≤ β^prec`; strict ⟹ grid bound, boundary `=β^(prec+E)` ⟹ power of `β`.
  - **`disc_prod_err_mult_bpow`** — the product error `x·y − RN(x·y)` is an integer multiple
    of the product grid `β^(cexp x + cexp y)` (from `mult_error_FLX_aux`).
  - `disc_bpow_coarsen` (private) — coarsen `M·β^G` onto `β^E` for `E ≤ G`.
  Lemma 4 takes two grid hypotheses (`cexp p − prec ≤ 2·cexp b`, likewise `q`), which fail
  *only* at a binade-crossing rounded power of two — exactly the §3.2.2 boundary.
- **`disc_prod_grid_or_pow2` — DONE** (2026-06-01): the discharge tool. For `b ≠ 0`, either
  Lemma 4's grid hypothesis holds OR `RN(b·b) = β^(2·mag b)` is the boundary power of two.
  From `mag_mult` + `mag_round`. Cleanly separates Lemma 4's clean regime from the boundary.

**§3.2.2 particular power-of-two cases — ALL THREE SUBCASES DONE** (the boundary
isolated by `disc_prod_grid_or_pow2`). Geometric foundation `disc_straddle` (general
radix): near-cancellation + distinct ulps ⟹ `q<p` straddle a power of `β`
(`mag p = mag q + 1`, `q < β^(mag q) ≤ p`). Then:
- **Exactness core** `disc_corr_particular_exact` (general radix): `|dp−dq| ≤ ulp q` ⟹
  `dp−dq ∈ F` (both errors coarsened to the grid `β^(mag q−2prec)` via `hgb/hgc`,
  `ulp q = β^(prec+E)`, `disc_diff_on_grid_exact`) ⟹ `δ≤2ulp d` (Lemma 3).
- **(a)** `disc_corr_particular_same_sign` (radix 2): `dp,dq` same sign ⟹ `|dp−dq| ≤
  ½ulp p = ulp q` (tightened via `abs_sub_le_of_same_sign`) ⟹ core.
- **(b.ii)** `disc_corr_particular_opp_neg` (general radix): opposite sign, `dp−dq≤0`,
  `p=β^(mag q)` ⟹ sharper `|dp| ≤ ½ulp q` (input-form `error_le_half_ulp`, since
  `b·b ≤ β^(mag q)`) ⟹ `|dp−dq| ≤ ulp q` ⟹ core.
- **(b.i)** `disc_corr_particular_opp_pos` (radix 2): opposite sign, `dp−dq≥0` ⟹
  `g=RN(dp−dq) ∈ [0,2ulp q]`, `d ≥ p−q ≥ ulp q`, so `ulp g ≤ 2ulp d`, giving
  `δ ≤ 3/2·ulp d ≤ 2ulp d` (the one non-exact subcase).

**§3.2.2 ASSEMBLED** (`disc_corr_particular`, radix 2): correction branch + `q<p` +
distinct ulps + near cancellation (`p−q ≤ 2ulp q`) ⟹ `δ ≤ 2ulp d`. Establishes
`p=β^(mag q)` (`disc_particular_p_pow2`, via `succ_le_lt_aux`), `p−q∈F` (Lemma 1),
`p−q≥ulp q` (`id_p_ulp_le_bpow`), and dispatches on `sign(dp·dq)` into (a)/(b.i)/(b.ii).
Grid bounds `hgb`/`hgc` are passed through (discharge below).

**§3.2.2 ASSEMBLED, MIRROR ORIENTATION `p<q` — DONE** (`disc_corr_particular_lo`, radix 2).
Boldo's "WLOG `p ≥ q`" relies on Pff's *relational* `Closest` rounding (negation-symmetric
for free). In our *functional* setting (fixed `choice` tie-breaker), negation maps the
`p<q` case to the *negative* regime, **not** to `q<p` — so the `p<q` orientation (which
the square discriminant genuinely reaches, e.g. `p=7,q=8`) is a genuine independent
mirror. The geometry (`disc_straddle`, `disc_particular_p_pow2`) is polymorphic in `{p q}`
and reused by swapped instantiation; the three sign-subcases are mirrored
(`disc_corr_particular_same_sign_lo` / `_opp_pos_lo` exact / `_opp_neg_lo` magnitude), all
funnelling through the orientation-agnostic exact core `disc_inner_exact`. The exact
mirror derives `a·c>0` from `RN(a·c)>0` (round-monotone), since the larger product is no
longer the square.

**GRID DISCHARGE — UNCONDITIONAL** (`disc_mag_prod_no_bump`). The keystone: `mag(RN(x·y))
≤ mag x + mag y` for *any* product of two floats. A product of two `prec`-significand
mantissas is `≤ (β^prec−1)²`, strictly below the round-up midpoint of the binade-doubling
power `β^(mag x+mag y)` (since `(1−t)²<1−½t` for `t=β^(−prec)≤½`), so rounding never bumps
the magnitude. This resolves the equal-ulp boundary Boldo glosses (the config `p=β^(2mag b)`
is simply *impossible* for a product), discharging **both** grid hypotheses of Lemma 4 and
the particular cases with **no side conditions** — no `prec ≥ 3`, no near-cancellation.
Tight gap `p−q ≤ 2·ulp(min)` from the not-far test via `disc_gap_le_two_ulp` (integer
multiple of `ulp(min)` below `3·ulp(min)`).

**FULL §3 — DONE.** `disc_correction` (radix 2): the complete correction branch
`3|p−q|<p+q ⟹ δ≤2·ulp d`, dispatching equal-ulp → Lemma 4 / distinct+far → `disc_corr_far`
/ distinct+near → particular case A (`q<p`) or B (`p<q`), **both orientations, no `prec≥3`**.
Capstone `disc_branch_real_test`: Kahan's branch algorithm `d = if p+q≤3|p−q| then ◦(p−q)
else ◦((p−q)+◦(dp−dq))` satisfies `|d−(b·b−a·c)| ≤ 2·ulp d` under the *real* test — the full
result of Boldo (2009) §3, both branches, **0 `sorry`s**.

**§4 — COMPLETE (both disagreements, both orientations, both capstones).** Reconciling the real
test with the *actual floating-point* test `◦(p+q) ≤ ◦(3·◦(|p−q|))`. The two tests disagree only
in a thin sliver (Boldo's `p=27,q=14` 5-digit example). The WLOG (`q<p`) lemmas below are joined
by `p<q` mirrors (`_lo`, reusing the pure sub-lemmas by arg-swap) and unconditional capstone
`disc_branch_fp_test_full` — see the §4.2 / capstone entries at the end of this section.

- **§4.1 (real corr, program runs benign `d=◦(p−q)=p−q`) — DONE** (`disc_fp_first_disagreement`,
  radix 2, `prec≥3`, `q<p`):
  - **L5** (`disc_fp_lemma5`): easy `cexp q ≤ cexp d` case, `δ=|dp−dq| ≤ 3/2·ulp q ≤ 3/2·ulp d`.
  - **L6** (`disc_fp_lemma6`): the sharp **`4q−2p ≤ β^(1−prec)(2p−q)`** (`q≈2q`); L7 weakens to `3q≤2p`.
  - **L7** (`disc_fp_lemma7`): `ulp p=ulp q ⟹ δ≤2ulp d` (via L6's `d≥q/2`).
  - **L8+L9** (`disc_fp_ulp_gt_impossible`): **`ulp p > ulp q` is IMPOSSIBLE** — Boldo's
    number-theoretic crux, here by a **clean rounding argument** (no significand pinning!). By
    monotonicity + FP-benign, `◦(p+q)=◦(3(p−q))=:r`; `2q−p≥ulp p` (`succ p≤2q`) ⟹ `4q−2p≥2·ulp p`,
    but `4q−2p=(p+q)−3(p−q)≤ulp r` ⟹ `mag r≥mag q+2` ⟹ `r=β^(mag q+1)`; then `3(p−q)≥r−½ulp r=
    β^(mag q+1)−β^(mag q+1−prec)` contradicts `3(p−q)<3β^(mag q−1)` for `prec≥3`. **CHOICE-ROBUST**
    (only uses the half-ulp bound, never the tie-break) — holds for arbitrary `Znearest choice`,
    unlike Boldo's round-to-even argument.
  - Assembly (`disc_fp_first_disagreement`): `cexp q≤cexp d`→L5; else `ulp p=ulp q`→L7, `ulp q<ulp p`→
    impossible. `ulp p<ulp q` can't happen (`q<p`).
- **§4.2 (real benign, program runs correction) — DONE** (`disc_fp_second_disagreement`,
  radix 2, `prec≥4`, `q<p`). Now `d=◦(◦(p−q)+◦(dp−dq))` (the benign `◦(p−q)` is *not* exact since
  real benign ⟹ no Sterbenz). With `w=β^(1−prec)` (so `w/2=β^(−prec)`); the four-step relative
  chain is choice-robust (uses only `|◦x−x| ≤ ◦x·(w/2)` from `error≤½ulp` + `ulp_FLX_le`).
  - **L10** (`disc_fp_lemma10`): relative-error chain (like L6) from FP-correction `◦(3◦(p−q))<◦(p+q)`:
    `(p−q)(1−w/2) ≤ ⅓(p+q)(1+w/2)²` — multiplicative (no division). `prec≥1`.
  - **L11** (`disc_fp_lemma11`) `0<q`: if `q≤0`, `p+q ≤ p−q` collapses L10 to `1−w/2 ≤ ⅓(1+w/2)²`,
    scalar-false for `prec≥2`. **`p≤3q`** (`disc_fp_p_le_3q`): from L10 with `q>0`, rearrange to
    `(p−q)·C ≤ 2q·C` with `C=3(1−w/2)−(1+w/2)² > 0` and `(1+w/2)² ≤ C` (`prec≥4`), then cancel `C`.
  - **L12** (`disc_fp_lemma12`) `|◦(dp−dq)| ≤ 3·ulp(◦(p−q))`: `|dp−dq| ≤ ½(ulp p+ulp q) ≤ 3ulp q ≤
    3ulp(◦(p−q))` (uses `q≤◦(p−q)` from real-benign + `p≤3q ⟹ ulp p≤4ulp q` via `ulp_two_mul_r2`),
    then `abs_round_le_generic` (`3ulp(◦(p−q))=3·β^k ∈ F` — new helper `disc_three_bpow_format`).
  - Assembly (`disc_fp_second_disagreement`): `δ ≤ ½(ulp d + ulp m + ulp g)` [3 roundings: `m=◦(p−q)`,
    `g=◦(dp−dq)`, outer]; `ulp m ≤ 2ulp d` [`m+g ≥ m−3ulp m ≥ m/2` (3ulp m ≤ m/2, prec≥4) + `m/2∈F`
    ⟹ `d=◦(m+g) ≥ m/2`]; `ulp g ≤ 6w·ulp d` [`ulp_FLX_le` + L12]; ⟹ `δ ≤ (3/2 + 3w)·ulp d ≤ 2ulp d`
    for `prec≥4` (`w≤1/8 < 1/6`). **The `m/2≥` route avoids needing `f−3ulp f∈F`** (Boldo's appeal).
- **§4 capstone `disc_branch_fp_test` (WLOG `q<p`) — DONE** (radix 2, `prec≥4`). For the *actual*
  rounded test `◦(p+q) ≤ ◦(3·◦(|p−q|))`, dispatches (FP test)×(real test): agreement-benign →
  `disc_branch_benign`, agreement-correction → `disc_correction` (both orientation-agnostic already),
  disagreements → §4.1/§4.2. Test-form bridging: `|p−q|=p−q` (`q<p`) + Sterbenz `◦(p−q)=p−q`.
- **§4 capstone `disc_branch_fp_test_full` (UNCONDITIONAL) — DONE.** Trichotomy on `p` vs `q`:
  `q<p` delegates to `disc_branch_fp_test`; `p<q` runs the mirror dispatch; `p=q` is degenerate.
  **The `p<q` mirror, as built:** `round_N_opp` reflection was confirmed unworkable (product-rounding
  ties: `◦_cr(a·c) ≠ ◦_c(a·c)`), so it's a genuine hand mirror — BUT cheaper than feared, because the
  *pure-`(p,q)`* sub-lemmas (`disc_fp_lemma6`, `disc_fp_ulp_gt_impossible` [the crux!], `disc_fp_lemma10/11`,
  `disc_fp_p_le_3q`) are **reused by swapping their `p`/`q` arguments** — no crux re-derivation needed.
  Only the sign-sensitive assemblies were rewritten: `disc_fp_lemma5_lo/7_lo/12_lo`,
  `disc_fp_first_disagreement_lo`, `disc_fp_second_disagreement_lo` (`d=◦(p−q)<0`, `|d|=q−p`,
  `|m|`-handling via `ulp_opp`/`abs_round_ge_generic`). Shared sign-agnostic δ-decomposition factored
  into `disc_fp_second_core` (also fixed a heartbeat timeout from the larger `p<q` context). `p=q`:
  benign forces `p=q=0` (`eq_0_round_0_FLX` + `ulp_FLX_0`); correction gives `d=◦(dp−dq)`.

**~37590 lines of Lean across 36 files. 0 `sorry`s. All files build clean.**
(Newest: `Algorithms/Discriminant_FLX.lean`, 3509 lines / 67 theorems — the
Kahan discriminant port, **COMPLETE: §3 + §4, both the real and floating-point tests,
all orientations, unconditional** (`disc_branch_fp_test_full`) — goes beyond Boldo (2009).
See the discriminant section above.)

**Flocq's main-line is complete in Lean.** A comprehensive name-by-name
sweep (2026-05-17) confirms every Coq theorem from `Core/`, `Calc/`,
`Prop/`, and `IEEE754/` that should have a Lean counterpart now has one.
Only `Pff/` remains un-ported — see [§ What's left](#whats-left).

| File | Lean lines | Coq source | Status |
|------|-----------|------------|--------|
| `Zaux.lean` | 40 | `Core/Zaux.v` | `radix` + `cond_Zopp`. Other integer utilities ported on demand (Mathlib subsumes most). |
| `Raux.lean` | 495 | `Core/Raux.v` | `bpow`, `Ztrunc`, `Zaway`, `mag`, `cond_Ropp` + key properties. Plus `mag_div`, `mag_sqrt`, `mag_mult`, `mag_plus` (sandwich bound), `mag_minus` (upper bound) for the Calc/Prop files. ~41 of Coq's ~150 lemmas (the rest are Mathlib's territory). |
| `Defs.lean` | 62 | `Core/Defs.v` | **Complete.** All 11 definitions. |
| `Float_prop.lean` | 409 | `Core/Float_prop.v` | **Complete: 36/36 theorems.** Including `Zdigits_mag` family, `F2R_cond_Zopp`, `Rcompare_F2R`, `F2R_prec_normalize`, `mag_F2R*` family. |
| `Round_pred.lean` | 819 | `Core/Round_pred.v` | **Essentially complete: 58/59 theorems.** |
| `Generic_fmt.lean` | 1964 | `Core/Generic_fmt.v` | **Complete: 109/109 theorems.** Includes `ZnearestA` and `round_NA_opp`. |
| `FIX.lean` | 85 | `Core/FIX.v` | **Complete.** 6 theorems including `ulp_FIX`. |
| `FLX.lean` | 383 | `Core/FLX.v` | **Complete: 19/19.** Includes `FLXN_format` family, `FIX_format_FLX`, `ulp_FLX_le/_ge`, `succ_FLX_exact_shift`. |
| `FLT.lean` | 454 | `Core/FLT.v` | **Complete: 19/19.** Includes `succ_FLT_exact_shift_pos/_full`, `negligible_exp_FLT`. |
| `FTZ.lean` | 414 | `Core/FTZ.v` | **Complete: 8/8.** Includes `FLXN_format_FTZ` and `FTZ_format_FLXN`. |
| `Ulp.lean` | 2508 | `Core/Ulp.v` | **Complete.** All keystones (`succ_DN_eq_UP`, `ulp_round`, error bounds, mixed-sign perturbation, `generic_format_plus_ulp`). `negligible_exp_prop` + `negligible_exp_spec` + `negligible_exp_spec'`. |
| `Round_NE.lean` | 740 | `Core/Round_NE.v` | **Complete: 10/10.** `DN_UP_parity_generic_pos/_aux/_generic`, `Rnd_NE_pt_{total,monotone,round}`, `round_NE_opp/_abs/_pt_pos/_pt`, `exists_NE_FLX/_FLT`. |
| `Digits.lean` | 206 | (subset of `Core/Digits.v`) | Minimal: `Zdigits` + 10 properties (`_zero`, `_neg`, `_abs`, `_correct`, `_unique`, `_gt_0`, `_ge_0`, `_le_Zpower`, `_div_Zpower`, `_mult_Zpower`). The rest of Coq's `Digits.v` is binary-representation machinery we don't need — `Zdigits := mag` makes the bridge definitional. |
| `Binary.lean` | 4684 | `IEEE754/Binary.v` (lines 1–2814, full file) | **Complete arithmetic surface.** Structural part (`full_float`, `binary_float`, `valid_binary`, `bounded`, `nan_pl`; FF2B/B2FF/B2R round-trips and injectivity; `Bsign`/`is_finite`/`is_nan`; `build_nan`/`erase`/`Bopp`/`Babs`; `Bcompare` with correctness and swap; boundedness theorems; `mode`/`round_mode`/`choice_mode`/`inbetween_int_valid_round_mode`/`overflow_to_inf`/`binary_overflow`). **`shr_record`** block (`shr_1`, `loc_of_shr_record`, `shr_record_of_loc` with three round-trip lemmas; `shr` iteration; `shr_1_nonneg`/`shr_1_iter_nonneg` invariants; `inbetween_shr_1`, `inbetween_shr_iter`, `inbetween_shr` correctness; `shr_fexp` + `shr_truncate`). IEEE-754 rounding kernel: `binary_round_aux` + `binary_round_aux_correct'` + `binary_round_aux_correct`. **Arithmetic ops:** `Bmult_correct_aux` + `Bmult` + `Bmult_correct`; `shl_align` + `shl_align_correct` + `snd_shl_align` + `shl_align_fexp` + `shl_align_fexp_correct`; `binary_round` + `binary_round_correct`; `binary_normalize` + `binary_normalize_correct`; `Bplus` + `Bplus_correct`; `Bminus` + `Bminus_correct`; `Bldexp` + `Bldexp_correct`; `Ffrexp_core_binary` + `Bfrexp_correct_aux` + `Bfrexp` + `Bfrexp_correct`; `Bone` + `Bone_correct` + `is_finite_Bone` + `Bsign_Bone`; `Bulp` + `Bulp_correct`; `Bpred_pos` + `Bpred_pos_correct`; `Bmax_float_valid` + `Bmax_float`; `Bsucc` + `Bsucc_correct`; `Bpred` + `Bpred_correct`; `Fdiv_core_binary` + `Bdiv_correct_aux` + `Bdiv` + `Bdiv_correct`; `Fsqrt_core_binary` + `Bsqrt_correct_aux` + `Bsqrt` + `Bsqrt_correct`; `Bnormfr_mantissa`. |
| `Calc/Bracket.lean` | 656 | `Calc/Bracket.v` | **Complete.** `location` enum, `inbetween` predicate, `inbetween_loc`, `inbetween_spec/_unique/_bounds/_distance_inexact[_abs]`. Step lemmas (`ordered_steps`, `inbetween_step_*`), `new_location_even/_odd/new_location` with correctness. Scaling (`inbetween_mult_aux`, `inbetween_mult_compat/_reg`). Float-level: `inbetween_float/_int/_bounds/_ex/_unique`, `inbetween_float_new_location[_single]`. |
| `Calc/Round.lean` | 1536 | `Calc/Round.v` | **Complete (all 79 Coq names).** `cexp_inbetween_float[_loc_Exact]`, `cond_incr`, `inbetween_float_round[_sign]`. All 6 mode families: DN/UP/ZR/N/NE/NA, both unsigned and signed, `inbetween_int_*` and `inbetween_float_*`. `truncate_aux`, `truncate_aux_comp`, `truncate`, `truncate_0`, `truncate_correct_partial[_partial']`/`_correct[_correct']`. `generic_format_truncate`, `truncate_correct_format`. Generic correctness: `round_any_correct`, `round_trunc_any_correct[_']`, `round_sign_any_correct`, `round_trunc_sign_any_correct[_']`. **All 30 per-mode aliases** for DN/UP/ZR/NE/NA. `truncate_FIX`, `truncate_FIX_correct`. |
| `Calc/Operations.lean` | 137 | `Calc/Operations.v` | **Complete: 13/13.** `Falign[_spec[_exp]]`, `Fopp` + `F2R_opp`, `Fabs` + `F2R_abs`, `Fplus` + `F2R_plus`, `Fplus_same_exp`, `Fexp_Fplus`, `Fminus` + `F2R_minus`, `Fminus_same_exp`, `Fmult` + `F2R_mult`. |
| `Calc/Div.lean` | 213 | `Calc/Div.v` | **Complete.** `mag_div_F2R`, `Fdiv_core` + `Fdiv_core_correct`, `Fdiv` + `Fdiv_correct`. Helpers: `quot_eq_mul_bpow`, `fdiv_pair`, `fdiv_pair_quot`. |
| `Calc/Sqrt.lean` | 256 | `Calc/Sqrt.v` | **Complete.** `mag_sqrt_F2R`, `int_sqrtrem` (Int.sqrt remainder semantics), `Fsqrt_core` + `Fsqrt_core_correct`, `Fsqrt` + `Fsqrt_correct`. |
| `Prop/Relative.lean` | 883 | `Prop/Relative.v` | **Complete.** Conversion lemmas (lt/le, both directions). Generic family: `relative_error[_ex/_F2R_emin/_F2R_emin_ex/_round/_round_F2R_emin]`, `relative_error_N[_ex/_F2R_emin/_F2R_emin_ex/_round/_round_F2R_emin]`. FLX family: `_FLX_aux/_FLX/_FLX_ex/_FLX_round/_N_FLX/_N_FLX_ex/_N_FLX_round`. FLT family: `_FLT_aux/_FLT/_FLT_F2R_emin[_ex]/_FLT_ex/_N_FLT[_ex]/_N_FLT_round/_N_FLT_F2R_emin[_ex]/_N_FLT_round_F2R_emin`. Combined: `error_N_FLT_aux`, `error_N_FLT`. **Unit-roundoff family complete:** `u_ro/u_ro_pos/u_ro_lt_1/u_rod1pu_ro_pos/u_rod1pu_ro_le_u_ro`, `relative_error_N_FLX'` (the tighter `u_ro/(1+u_ro)` bound via ufpx), `relative_error_N_FLX'_ex`, `relative_error_N_round_ex_derive`, `relative_error_N_FLX_round_ex`, `relative_error_N_FLT'_ex`, `relative_error_N_FLT'_ex_separate`. |
| `Prop/Sterbenz.lean` | 119 | `Prop/Sterbenz.v` | **Complete: 4/4.** `generic_format_plus` (sum stays in F when bounded by `β^(min(mag x, mag y))`), `generic_format_plus_weak` (weak version with `min(\|x\|, \|y\|)`), `sterbenz_aux` (helper `y ≤ x ≤ 2y → x - y ∈ F`), `sterbenz` (the keystone: `y/2 ≤ x ≤ 2y → x - y ∈ F`). |
| `Prop/Mult_error.lean` | 351 | `Prop/Mult_error.v` | **Complete: 7/7.** FLX: `mult_error_FLX_aux` (the keystone — produces an explicit float for the error at exponent `cx + cy`), `mult_error_FLX`, `mult_bpow_exact_FLX`. FLT: `mult_error_FLT`, `F2R_ge`, `mult_error_FLT_ge_bpow`, `mult_bpow_exact_FLT`. |
| `Prop/Plus_error.lean` | 670 | `Prop/Plus_error.v` | **Complete: 20.** Keystones: `round_repr_same_exp`, `plus_error_aux`, `plus_error`. Zero family: `FLT_format_plus_small`, `round_plus_neq_0_aux`, `round_plus_neq_0`, `round_plus_eq_0`. Trivial bounds: `plus_error_le_l/r`. Helpers: `ex_shift`, `mag_minus1`, `lt_mag`, `mag_minus_lb`. mult_ulp section: `round_plus_F2R`, `round_plus_ge_ulp`. plus_ge family: `round_FLT_plus_ge`, `round_FLT_plus_ge'`, `round_FLX_plus_ge`. **Unit-roundoff variants:** `FLT_plus_error_N_ex` and `FLT_plus_error_N_round_ex`. |
| `Prop/Div_sqrt_error.lean` | 1392 | `Prop/Div_sqrt_error.v` | **Complete (file fully ported).** Keystones: `generic_format_plus_prec`, `div_error_FLX`, `sqrt_error_FLX_N`. Sqrt unit-roundoff helpers: `om1ds1p2u_ro_pos`, `s1p2u_rom1_pos`, `om1ds1p2u_ro_le_u_rod1pu_ro`. Main sqrt error theorem and variants: `sqrt_bpow_even`, `sqrt_error_N_FLX_aux1/_aux2/_aux3`, `sqrt_error_N_FLX`, `sqrt_error_N_FLX_ex`, `sqrt_error_N_round_ex_derive`, `sqrt_error_N_FLX_round_ex`, `sqrt_bpow_ge`, `sqrt_error_N_FLT_ex`, `sqrt_error_N_FLT_round_ex`. format_REM family: `format_REM_aux`, `format_REM_pos` (private), `format_REM`, `format_REM_ZR`, `format_REM_N`. Note: `sqrt_error_N_FLX_aux2` strengthened to `prec > 1` to avoid edge case at prec=1, β=2 where `1 + 2u_ro = β`. |
| `Prop/Round_odd.lean` | 1453 | `Prop/Round_odd.v` | **Complete.** Z-level: `Zrnd_odd` (the rounding function — rounds non-integers to the odd integer between floor and ceiling), `valid_rnd_odd`, `Zrnd_odd_Zodd`, `Zfloor_plus`, `Zceil_plus`, `Zeven_abs`, `Zrnd_odd_plus`, `Zrnd_odd_plus'`. R-level: `Rnd_odd_pt` predicate, `Rnd_odd`, `Rnd_odd_pt_opp_inv`, `round_odd_opp`. Core: `round_odd_pt` (the keystone), `Rnd_odd_pt_unique`, `Rnd_odd_pt_monotone`. **Odd_prop_aux geometry (Stage 5):** `generic_format_fexpe_fexp`, `exists_even_fexp_lt`, `d_eq_round_DN`, `u_eq_round_UP`, `d_ge_0`, `mag_d`, `Fexp_d`, `format_bpow_x`, `format_bpow_d`, `d_le_m`, `m_le_u`, `mag_m`, `mag_m_0`, `u'_eq`, `m_eq`, `m_eq_0`, `fexp_m_eq_0`, `Fm`, `Zm`, `DN_odd_d_aux`, `UP_odd_d_aux`. **Keystones:** `round_N_odd_pos` (the no-double-rounding theorem for positive x — rounding-to-nearest of round-to-odd at coarser precision equals rounding-to-nearest directly, when fexpe ≤ fexp - 2 and β even) and `round_N_odd` (general form via opp symmetry). **Stage 6 (cexp preservation):** `mag_round_odd` and `fexp_round_odd` (FLT, β even, prec > 1: round-to-odd preserves both `mag` and `cexp`). |
| `Prop/Double_rounding.lean` | 4893 | `Prop/Double_rounding.v` (~95% by lines) | **Core mid-rounding + multiplication + bridge + full sqrt arc + sqrt radix_ge_4 + full plus/minus arc + plus/minus radix_ge_3 + full division arc.** `mag_mult_disj`. Definitions: `round_round_eq`, `midp`, `midp'`. **`_lt_mid` family:** `_further_place'`, `_further_place`, `_same_place`, `_lt_mid` dispatcher. **`_gt_mid` family:** `_further_place'`, `_further_place` (with the `x'' = bpow(mag x)` edge case via `round_generic` + `Znearest_imp`), `_same_place`, `_gt_mid` dispatcher. **Multiplication arc:** `round_round_mult_hyp`, `round_round_mult_aux`, `round_round_mult`, `round_round_mult_FLX/_FLT/_FTZ`. **Bridge:** `round_round_mid_cases`. **Sqrt arc:** `round_round_sqrt_hyp`, `mag_sqrt_disj`, `bpow_neg_two_le_quarter`, `round_round_sqrt_aux` (300-line keystone), `round_round_sqrt` + FLX/FLT/FTZ. **Plus/minus arc:** `round_round_plus_hyp` (4-conjunct precision condition), six mag helpers, plus/minus aux families, **`round_round_plus`** and **`round_round_minus`** keystones, plus FLX/FLT/FTZ instantiations. **Division arc complete:** `round_round_really_zero`, `round_round_zero`, `round_round_all_mid_cases` (4-callback dispatcher), `round_round_eq_mid_beta_even` (bridge for β even), `mag_div_disj`, `round_round_div_hyp` (5-conjunct precision), **`round_round_div_aux0/1/2`** (the three case-split preludes — boundary/below-midpoint/above-midpoint), **`round_round_div_aux`** dispatcher, **`round_round_div`** keystone (with sign dispatch via `round_N_opp` for negative x or y), FLX/FLT/FTZ instantiations (3 hyp lemmas + 3 user theorems). **Sqrt radix_ge_4 arc:** `bpow_neg_one_le_quarter_of_beta_ge_4` helper, `round_round_sqrt_radix_ge_4_hyp`, `_aux`, `_radix_ge_4` keystone, FLX/FLT/FTZ — the regular sqrt aux with `-2 → -1` throughout, needing `4 ≤ beta`. **Plus/minus radix_ge_3 arc:** `bpow_neg_one_le_third_of_beta_ge_3` helper, `round_round_plus_radix_ge_3_hyp`, plus chain (aux0/aux1/aux2/aux), minus chain (aux0/aux1/aux2/aux3/aux), plus/minus keystones with sign dispatch, FLX/FLT/FTZ for both — needs `3 ≤ beta`, uses `bpow(-1) ≤ 1/3`. |
| `IEEE754/Bits.lean` | 1019 | `IEEE754/Bits.v` (full file) | **Bit encoding fully proven: 14 + 5 helpers, plus B32/B64 instantiations.** Core int encoding: `join_bits`, `split_bits`, `join_bits_range`, `split_join_bits`, `join_split_bits`, `split_bits_inj`. binary_float pack: `bits_of_binary_float`, `bits_of_binary_float_range`, `split_bits_of_binary_float`, `split_bits_of_binary_float_correct`. Decoding: `binary_float_of_bits_aux`, `binary_float_of_bits_aux_correct`, `binary_float_of_bits`. **Round trips:** `binary_float_of_bits_of_binary_float`, `bits_of_binary_float_of_bits`. Helpers: `bpow_radix2_eq`, `Zdigits_radix2_one`, `pow_ew_minus_one_ne_zero`, `subnormal_exp_eq_emin`, `normal_exp_field_bounds`, `bits_of_full_float`, `bits_of_FF2B`. **B32/B64 specialization:** `binary32 := binary_float 24 128` and `binary64 := binary_float 53 1024`, with default NaN payloads (`2^22` / `2^51`), `unop_nan_pl{32,64}`, `binop_nan_pl{32,64}`, and the full op suite `b{32,64}_{erase,opp,abs,sqrt,plus,minus,mult,div,compare,of_bits}` + `bits_of_b{32,64}`. |
| `Algorithms/Fast2Sum.lean` | 470 | *not in Coq Flocq* (only in Pff) | **First error-free transformation, proved directly on Flocq's foundations.** Radix 2, **FLT**, round-to-nearest. Helpers: `two_mul_in_FLT_radix2` (closure under doubling), `succ_FLT_subnormal_step` (uniform `succ d = d + bpow(emin)` for `0 ≤ d < bpow(emin+prec)`), `round_N_gt_half_FLT_radix2` (radix-2 midpoint-symmetry: for `a ∈ F, 0 < a, a/2 < v` strict, `a/2 ≤ round_N(v)` even when `a/2 ∉ F`). Main: `Fast2Sum_step1_pos` (Pff three-case argument on `b ≥ 0` vs `b ≤ -a/2` vs `-a/2 < b < 0`), `Fast2Sum_step1` (general, via `round_N_opp` symmetry), `Fast2Sum_step2` (plus_error step), `Fast2Sum_correct` (keystone: `a + b = s + e` exactly). |
| `Algorithms/TwoSum.lean` | 70 | *not in Coq Flocq* (only in Pff) | **Error-free transformation, no precondition.** Radix 2, **FLT**, round-to-nearest. Branching formulation: comparison + Fast2Sum on the larger side. Mathematically identical to Knuth's 6-op TwoSum (same `e`, same exactness). One theorem, `TwoSum_correct` — exposes both `s` and `e` as named `let`-bindings, returns `e ∈ F ∧ a + b = s + e`. |
| `Algorithms/Veltkamp.lean` | 4236 | `Pff/Pff2Flocq.v` (Veltkamp section, 323–619) | **Veltkamp at FLX FULLY DONE: aux + format + tail + existence + Veltkamp_Even (both odd and even radix, unconditional).** Plus **`Veltkamp_struct_FLX`** (2026-05-31, exposed for TwoProduct): bundles `x = M_x·β^cx`, `hx = M_h·β^(s+cx)`, `|M_h| ≤ β^(prec−s)`, `|M_x − M_h·β^s| ≤ β^s/2`. `Veltkamp_Even_FLX_even_radix_NE` (2026-05-31): for even β, `round_NE_{prec-s} x = Veltkamp_hx_FLX β prec (fun n => decide (¬ Even n)) s x` with no remaining hypothesis. Mp and Mq parity theorems use the same structural template: at coarse tie + hard interior + NE choice, the algebraic source is at half-integer multiple of β^(s+cx) with odd integer coefficient; case-split on cexp gives β factor (high) or ZnearestE-at-midpoint picks even (equal); the impossible case yields contradiction via odd-coefficient arithmetic. Error-bound side: `Veltkamp_C_format` (FLT) + `Veltkamp_C_format_FLX`, `mag_xC_bounds`, four `noncomputable def`s, polarity lemmas (`Veltkamp_p_nonneg_FLX`, `Veltkamp_x_le_p_FLX`, `Veltkamp_q_nonpos_FLX`), Sterbenz prerequisites (`Veltkamp_neg_q_le_p_FLX`, `Veltkamp_abs_x_minus_p_lt_FLX`, `Veltkamp_p_le_neg_2q_FLX`), **`hxExact_FLX`** (third rounding step is identity), **`Veltkamp_aux_FLX_CaseA`** (mag(x·C) = m+s), **`Veltkamp_aux_FLX_CaseB`** (via interior/boundary M_x dispatch), unified **`Veltkamp_aux_FLX`** keystone. Case B helpers: `Veltkamp_p_le_xbeta_FLX` (epLe), `Veltkamp_mag_p_le_FLX`, `Veltkamp_cexp_p_le_FLX`, `Veltkamp_p_le_J1_FLX` (J1), `Veltkamp_neg_q_le_pow_FLX` (V). **Format-side**: `Veltkamp_q_ne_zero_FLX`, three eqGe branches (`Veltkamp_abs_q_ge_branch1/2a/2b_FLX`), discreteness helper `Veltkamp_x_lb_above_bpow_FLX`, assembled **`Veltkamp_eqGe_FLX`**. Integer-mantissa-at-`s+cx` helpers (`Veltkamp_q_at_scx_FLX`, `Veltkamp_p_at_scx_FLX` — both case-agnostic via `F2R_change_exp`). Unified format theorem **`Veltkamp_hx_format_FLX`**: hx = M·β^(s+cx) with `|M| ≤ β^(prec−s)`, side case `|M| = β^(prec−s) → hx = β^m → generic_format_bpow`. Bundled keystone **`Veltkamp_aux_FLX_complete`** = error bound ∧ format. **Tail**: `Veltkamp_tail_FLX` = `x = hx + tx ∧ tx ∈ F(FLX, s)`, via integer-mantissa decomposition at exp `cx` + half-ulp bound. **Existence**: `Veltkamp_M_h_close_FLX` (integer-mantissa half-ulp core: `\|M_x − M_h · β^s\| ≤ β^s/2`) + **`Veltkamp_FLX`** (∃ choice' such that `round_{prec−s, Znearest choice'} x = hx`, via `choice' = decide(DN < hx)` and case-split on strict vs tie + sm = M_h ± 1/2). |
| `Algorithms/TwoProduct.lean` | 805 | `Pff/Pff2Flocq.v` (Dekker section, 682–976) | **FMA-free Dekker TwoProduct at FLX — COMPLETE for `radix 2 ∨ Even prec` (all IEEE variants incl. binary64), bare + machine form.** Headlines: **`TwoProduct_FLX`** (bare products) and **`TwoProduct_FLX_machine`** (each sub-product a *rounded* multiply — the real FMA-free algorithm; rewrites the four product-rounds to bare via `generic_format_FLX_mult` ×3 + the `tx·ty` dichotomy, then applies `TwoProduct_FLX`). Nonzero core `TwoProduct_FLX_main`: the 4-step chain `round(round(round(round(hx·hy − r) + hx·ty) + tx·hy) + tx·ty)`, each step rounding exactly. **Key insight:** the bare chain never uses product-exactness — steps round exactly via grid magnitude bounds + `mult_error_FLX`, so it's radix-agnostic given `s = ⌈prec/2⌉`; the radix/parity condition only makes the *machine* `tx·ty` exact. Bedrock: **`generic_format_FLX_mult`** (`F(p1)·F(p2) ⊆ F(p1+p2)`), **`Veltkamp_split_FLX_general`** (all-sign split), **`generic_format_FLX_of_mult_bpow`** (grid lemma), **`Veltkamp_struct_FLX_general`** (all-sign mantissa bounds), **`round_mul_Fs_exact`** (even-prec `tx·ty`), **`round_tt_exact_radix2`** (radix-2 `tx·ty`, Dekker2 crux via half-ulp tail bound), **`round_add_grid_exact`** (step engine). Chaining layer: **`bpow_coarsen`**, **`abs_prod_bpow_le`**, **`prod_bound_medium`** (`½β^(prec+s+E₀)`, takes high-part bound `β^(prec−s)`), **`prod_bound_small`** (`¼β^(2s+E₀)`), **`four_le_bpow`**, **`abs_sub{1,2,3}_le`**, **`Veltkamp_parts_zero`**. `r` pinned to grid `cexp(x·y)` via `cexp_round_ge`; S1 closes by `7/4 < 2 ≤ β`; S2/S3 via `4·C2 ≤ C` + `β^(2s+E₀) ≤ 2·C2`; S4 via `mult_error_FLX`. (`twoproduct_expand_exact` retained as a standalone even-prec lemma, now unused by the chain.) |
| `Algorithms/EFT_FLX.lean` | 232 | *not in Coq Flocq* (only in Pff) | **FLX (no-underflow) Fast2Sum + TwoSum, radix 2.** The FLX counterparts of the FLT EFTs, recovered from commits `a7d8eff`/`cc7ad6c` with `_FLX`-suffixed names so they coexist with the gradual-underflow versions. `Fast2Sum_FLX_correct` (3-case Pff structure: `b ≥ 0` / `b ≤ −a/2` Sterbenz / midpoint), `TwoSum_FLX_correct` (branch into Fast2Sum on the larger side). Needed because ErrFMA's blocks must share TwoProduct's format (FLX). |
| `Algorithms/RoundMinusRound_FLX.lean` | 304 | `Pff/Pff.v` `Subexact` (GenericA/B, 23448–23854) | **The round-minus-round exactness engine (L1's heart).** **`round_minus_round_nearby_exact_FLX`**: for `a, b ∈ F(FLX)` and `e` at most half a ulp of *each*, `round(a+b) − round(a+b+e) ∈ F`. The two roundings keep the sign and stay within a factor of two (Pff's `xLe2y`/`yLe2x`), so Sterbenz applies. Supporting: **`err_le_uro_round_FLX`** (output-form relative bound = Pff `ClosestRounde{Le,Ge}Normal`, from `error_le_half_ulp_round` + `ulp_FLX_le`), **`add_int_mul_bpow_min`** (a nonzero float-sum is a nonzero integer multiple of `β^min(cexp a, cexp b)`), **`abs_add_eq_or_ge_two_bpow_min`** (boundary `=β^m` / bulk `≥2β^m` dichotomy), **`sterbenz_abs`** (signed Sterbenz via `\|x\|≤2\|y\|`, `\|y\|≤2\|x\|`, same sign). Boundary case clean at radix 2 (`a+b = ±2^m` is a float). Radix 2, FLX, `prec ≥ 3`. |
| `Algorithms/ErrFMA.lean` | 251 | `Pff/Pff.v` `FmaErr` (23446–25161), `Pff2Flocq.v` `ErrFMA_correct` (1057) | **Exact error of the FMA (Boldo–Muller) — E0/E1 done, E2 L1 + β2=0 branch typed.** `a·b + c = r1 + r2 + r3` exactly. `twoproduct_eft`/`twosum_eft` (existential EFT interfaces), **`ErrFMA_chain`** (`a·b+c = β1+β2+α2`), **`errfma_gat_exact`** (L1 = Pff `gatCorrect`: `β1−r1 ∈ F` via the engine + `round_N_pt` closeness), **`ErrFMA_be2_zero`** (Pff `FmaErr_aux1`: `a·b+c = r1+γ+α2` when β2=0, via L1 + idempotency). |
| `Algorithms/ErrFMA_L2.lean` | 776 | `Pff/Pff.v` `FmaErr_aux2`/`gaCorrect`/`Midpoint_aux` (24318–24786, 23856–24316) | **ErrFMA L2 (β2≠0) — COMPLETE.** The Flocq-native replacement for Pff's MSB/LSB. **`errfma_be2_mult_bpow`** (β2 a multiple of `β^min(cexp u1, cexp α1)` via `round_repr_same_exp`), **`errfma_al2_lt_bpow`** (`|α2| < β^min(...)`), **`nonneg_bpow_mult_lt_eq_zero`**/**`neg_bpow_squeeze`** (divisibility squeeze), **`errfma_be2_eq_bpow_upper`**/**`errfma_be2_eq_bpow_lower`** (upper/lower midpoint cores via `round_N_{le,ge}_midp` + squeeze; lower has the `pred_pos` power-of-β branch), **`errfma_be2_div_dichotomy`** (`β1=r1 ∨ β2` a `β^(cexp β1−2)`-multiple; `be1<0` sign-reduces via `round_N_opp`), **`format_mult_bpow_of_cexp_ge`**, **`errfma_ga_exact`** (`(β1−r1)+β2 ∈ F`), **`ErrFMA_be2_nonzero`** (`FmaErr_aux2`), **`ErrFMA_correct`** (the full `FmaErr`: `a·b+c = r1+γ+α2`, both branches + edge cases), **`ErrFMA_threefloat`** (`Fma_FTS`: `a·b+c = r1+r2+r3` via precondition-free `TwoSum(γ,α2)`; `α2∈F` via `plus_error`, `u2∈F` via `mult_error_FLX`). |

| `Algorithms/Discriminant_FLX.lean` | 3509 | *not in Coq Flocq* (Boldo 2009 `boldo.pdf`; modern Flocq-native) | **Kahan discriminant `b·b − a·c` — COMPLETE: Boldo §3 + §4, real & FP tests, ALL orientations, unconditional (`disc_branch_fp_test_full`) — beyond the paper.** Structural core (general radix): `disc_fma_error_exact`/`disc_prod_error_format` (D0), `disc_corrected_value`/`disc_sterbenz_exact`/`disc_p_nonneg` (D1), `disc_naive_error_bound` (D2). Relative-error calculus from `Triangle.v`: `rel_err`/`rel_err_{aux,0,opp,init}`. **Opposite-sign `2u`**: `disc_kahan_error_decomp` + **`disc_kahan_opp_sign_2u`** (`a·c≤0 ⟹ ≤2·u_ro·\|b·b−a·c\|`). **Boldo branch `2·ulp(d)` (radix 2):** Lemma 1 `disc_branch_subtract_exact`; ulp toolkit; **§3.1 benign** (`disc_branch_benign`); **§3.2 analytic** (`disc_corr_err_decomp`, `disc_corr_exact`=L3, `disc_corr_dpdq_bound`, `disc_corr_general`, `disc_corr_far`, `disc_corr_pq_eq`); **§3.2 Lemma 4** (`disc_corr_lemma4`, via `disc_diff_on_grid_exact`/`disc_prod_err_mult_bpow`/`disc_inner_exact`). **§3.2.2 BOTH orientations**: geometry `disc_straddle`/`disc_particular_p_pow2` (polymorphic in `{p q}`), exact core `disc_inner_exact`; case A (`q<p`) `disc_corr_particular` + subcases `_same_sign`/`_opp_neg`/`_opp_pos`; **genuine mirror** case B (`p<q`) `disc_corr_particular_lo` + `_same_sign_lo`/`_opp_pos_lo`/`_opp_neg_lo` (Boldo's relational WLOG does NOT collapse in the functional setting). **Grid discharge UNCONDITIONAL** via **`disc_mag_prod_no_bump`** (`mag(RN(x·y)) ≤ mag x+mag y` — products never bump magnitude, resolving the equal-ulp boundary, killing `prec≥3`); tight gap `disc_gap_le_two_ulp`. **Full §3**: **`disc_correction`** (correction branch, both orientations) + capstone **`disc_branch_real_test`** (Kahan branch algorithm `≤2·ulp d` under the real test, both branches, 0 sorries). **§4 (FP-test reconciliation): COMPLETE, all orientations.** §4.1 `disc_fp_first_disagreement` (real corr, program runs benign) incl. the number-theoretic crux `disc_fp_ulp_gt_impossible` (`ulp p>ulp q` impossible — clean choice-robust rounding argument, no significand pinning) + `disc_fp_lemma5/6/7`. §4.2 `disc_fp_second_disagreement` (real benign, program runs correction, `prec≥4`): chain `disc_fp_lemma10`, `disc_fp_lemma11` (`0<q`) + `disc_fp_p_le_3q`, `disc_fp_lemma12` (+ helper `disc_three_bpow_format`), assembly via `d≥m/2`. **`p<q` mirrors** (`disc_fp_lemma5_lo/7_lo/12_lo`, `disc_fp_first/second_disagreement_lo`) reuse the pure-`(p,q)` sub-lemmas (incl. the crux) by argument-swapping; shared `disc_fp_second_core`. **Capstones: `disc_branch_fp_test` (WLOG `q<p`) + `disc_branch_fp_test_full` (UNCONDITIONAL, all orientations + `p=q`)** — beyond Boldo's paper. |
**Total: ~812 Lean theorems vs ~480 substantive Coq theorems** (we have extras
from helpers, private lemmas, and instance declarations).

## Build setup

- **Toolchain**: `leanprover/lean4:v4.25.0` (pinned in `lean-toolchain`).
- **Mathlib**: `git#v4.25.0` via `lakefile.toml`.
- **First-time build**: `lake exe cache get` to fetch the Mathlib build cache,
  then `lake build`. With cache: ~2 min. Without: >30 min.
- **Incremental rebuilds**: `lake build` typically rebuilds just the changed files in seconds.

```bash
cd lean-flocq
lake exe cache get      # only needed once or after `lake update`
lake build              # rebuilds; show errors if any
```

## What's in each file

### `Defs.lean` (foundations)

`float`, `F2R`, `round_pred_total/monotone/_`, `Rnd_{DN,UP,ZR,N,NG,NA}_pt`. No theorems —
just definitions matching Coq exactly.

### `Raux.lean`

`bpow`, `Ztrunc`, `Zaway`, `mag` (as a noncomputable function returning 0 at 0,
the magnitude integer otherwise), `cond_Ropp`. Plus enough `bpow` and `mag` lemmas
to support everything downstream (`bpow_le`, `bpow_plus`, `mag_unique`, `mag_bpow`,
`mag_mult_bpow`, `IZR_Zpower`, etc.).

The bulk of Coq's `Raux.v` is real-number utility lemmas already provided by
Mathlib. We don't replicate them.

### `Float_prop.lean`

All 36 Coq theorems: ordering on F2R, sign facts, `F2R_change_exp`,
`F2R_p1_le_bpow`, `bpow_le_F2R_m1`, `F2R_lt_bpow`, `F2R_prec_normalize`,
`F2R_cond_Zopp`, `Rcompare_F2R` (using Mathlib's `compare` on ℝ), the `mag_F2R`
family, `Zdigits_mag` family, and `float_distribution_pos`.

### `Round_pred.lean`

All Coq theorems: `Rnd_{DN,UP,ZR,N,NG,NA}_pt` properties, `round_unique`,
`Rnd_{DN,UP}_unique`, `Rnd_N_pt_{monotone,unique,refl,idempotent,DN_or_UP,
DN_UP,DN,UP,opp_inv,abs}`, `Rnd_NG_pt_{unique,monotone,refl,opp_inv,unique_prop}`,
`Rnd_NA_*`, `satisfies_any_imp_{DN,UP,ZR,NG,NA}`, etc.

### `Generic_fmt.lean`

All 109 Coq theorems plus the `Valid_rnd` typeclass. Highlights:
- `Valid_exp` definition and large-regime / small-regime extraction
- `cexp`, `canonical`, `scaled_mantissa`, `generic_format`, `Ztrunc`/`Zceil`
- `round`, `round_DN_pt/_UP_pt/_N_pt`, `round_DN_or_UP`, `round_le`,
  `round_generic`, `round_le_generic/_ge_generic`
- `generic_format_F2R/_F2R'/_bpow/_bpow'/_satisfies_any`
- `Znearest` + invariants, `round_N_opp`, `round_N_pt`
- `ZnearestA` + `round_NA_opp`
- `Monotone_exp`, `Exp_not_FTZ` (the latter in Ulp), `subnormal_exponent`
- `mag_generic_gt`, `cexp_DN`, `scaled_mantissa_DN`, `generic_format_EM`

### Format files (`FIX/FLX/FLT/FTZ/Digits.lean`)

`*_format` definitions, `*_exp` exponent functions, validity, monotonicity,
inclusion bridges (`FIX ↔ FLX`, `FLX ↔ FLT`, `FLX ↔ FLXN`, `FLXN ↔ FTZ`, etc.),
`ulp_*` shapes, `*_exact_shift` for FLX/FLT, `negligible_exp_*`.

### `Ulp.lean` (the big one)

All 103 Coq theorems organized in clusters:
- **Foundations**: `negligible_exp`, `ulp` def, basic equalities and bounds.
- **Step structure** (`succ` / `pred` / `pred_pos`): definitions, format-preservation,
  order properties, the roundtrip `pred_plus_ulp`, the inverse pair `succ_pred` /
  `pred_succ`, monotonicity (`succ_le`, `pred_le`, `succ_lt`, `pred_lt`,
  `succ_le_inv`, `pred_le_inv`).
- **`Exp_not_FTZ` triple equivalence**: `Exp_not_FTZ ↔ ∀ x, ulp x ∈ F ↔
  ∀ x, ulp 0 ≤ ulp x`.
- **Round/ulp interaction**: `ulp_DN`, `succ_DN_eq_UP`, `pred_UP_eq_DN`,
  `ulp_round_pos`, **`ulp_round`** (the keystones), `round_DN_eq`, `round_UP_eq`.
- **Perturbation** (positive and mixed-sign): full `round_DN_plus_eps_pos/_full`,
  `round_UP_plus_eps_pos/_full`, `round_UP_pred_plus_eps_pos/_full`,
  `round_DN_minus_eps_pos/_full`. The positive `round_UP_plus_eps_pos`
  accepts `0 ≤ x`.
- **Error bounds**: `error_lt_ulp`, `error_le_ulp`, `error_le_half_ulp`,
  `error_lt_ulp_round`, `error_le_ulp_round`, `error_le_half_ulp_round`.
- **Round-to-nearest midpoint**: `round_N_le_midp`, `round_N_ge_midp`,
  `round_N_eq_DN`, `round_N_eq_UP`, plus `_pt` variants.
- **Closure**: `succ_le_plus_ulp`, `generic_format_plus_ulp` (under `Monotone_exp`),
  `round_N_plus_ulp_ge`, `succ_round_ge_id`.
- `abs_round_ge_generic`, `abs_round_le_generic`.

### `Round_NE.lean`

All 10 Coq theorems. The full IEEE round-to-nearest-even semantics:
- `ZnearestE`, `round_NE`, `NE_prop`, `Rnd_NE_pt`.
- `Exists_NE` typeclass.
- `DN_UP_parity_pos_prop` / `DN_UP_parity_prop` / `DN_UP_parity_aux` /
  **`DN_UP_parity_generic_pos`** (the keystone) / `DN_UP_parity_generic`.
- `Rnd_NE_pt_total`, `Rnd_NE_pt_monotone`, `Rnd_NE_pt_round`.
- `round_NE_opp`, `round_NE_abs`, **`round_NE_pt_pos`** (the other keystone),
  `round_NE_pt`.
- `exists_NE_FLX`, `exists_NE_FLT`.

## The two architectural bridges

These connect concrete `Generic_fmt` to abstract `Round_pred`:

1. **`generic_format_satisfies_any`** (`Generic_fmt → Round_pred`): any valid
   generic format is a `satisfies_any` instance. Unlocks all
   `satisfies_any_imp_*` results for any concrete format.

2. **`round_N_pt`** (`Generic_fmt → Round_pred`): `round β fexp (Znearest choice) x`
   is a `Rnd_N_pt` of the format. Combined with `valid_rnd_N`, every `Rnd_N_pt`
   theorem applies to Znearest-rounded values.

## Translation patterns and gotchas

### Imports

- `Mathlib.Algebra.Order.Floor` is deprecated; use `.Ring` and `.Semiring` subdirs.
- `Mathlib.Data.Int.Defs` doesn't exist; use `Mathlib.Data.Int.Init`.
- `FloorRing ℝ` instance lives in `Mathlib.Data.Real.Archimedean`.

### Mathlib lemma name shifts (Lean v4.25.0)

- `mul_lt_mul_right` → `mul_lt_mul_iff_of_pos_right`
- `le_or_lt` → `le_or_gt`
- `lt_or_le` → `lt_or_ge`
- `abs_add` → `abs_add_le`

### `bpow` and `Zpower` differ at negative exponents

Coq's `Zpower beta n` returns `0` for `n < 0`. Lean's `(beta.val : ℤ) ^ n.toNat`
returns `1` (since `.toNat = 0`). Documented on `F2R_lt_bpow`.

### `rw [hxm]` substitutes globally — multiple variants

This trap appears in **many forms**.

**Form 1:** `hxm : x = ...`. `rw [hxm]` substitutes every `x` in the goal —
including `x` inside `⌊x⌋`, `cexp beta fexp x`, `scaled_mantissa beta fexp x`,
etc. Workarounds:
- `set sm := scaled_mantissa beta fexp x` *before* the rewrite.
- `conv_lhs` / `conv_rhs` to scope.
- A scoped `have` instead of `rw`.

**Form 2:** `rw [ulp_neq_0]` is bad when the goal has both `ulp x` standalone
*and* `ulp x` inside a `cexp` argument. Use the **calc pattern**.

### `(↑n.toNat).toNat` and zpow ↔ npow

After `rw [show (n : ℤ) = ((n.toNat : ℕ) : ℤ) from htn.symm, zpow_natCast]`,
you get a residual `(↑n.toNat).toNat`. Use `Int.toNat_natCast` or `norm_cast`.

### `Bool` vs `Prop` ifs and `decide`

`Znearest` uses `if (choice ⌊x⌋ : Bool) then ... else ...`. With Lean 4's
elaboration, this is `if (choice ⌊x⌋ = true) then ... else ...` (Decidable).
Patterns that work:
- `change (if decide P = true then ... else ...) = ...` then `rw [decide_eq_true _]`.
- `simp only [decide_eq_true_iff, decide_eq_false_iff_not]` to normalize.
- Beta-reduce explicitly with `change` if the choice is `(fun n => decide ...)`.

The `decide_eq_true` / `decide_eq_false` rewrite often *doesn't* match because
the surrounding `(fun n => decide ...)` isn't beta-reduced. `change` to the
beta-reduced form first.

### Equality of structures and `congr 1`

`F2R ⟨m1, e⟩ = F2R ⟨m2, e⟩` reduces (via `F2R_eq` / `congr 1`) to `m1 = m2`. For
`congr 1` to step into the structure, the exponents must match syntactically.
Use `F2R_change_exp` or explicit unfolding when they don't.

### `mag x - prec` vs `mag x + (-prec)` flakiness

`bpow_plus : bpow (a + b) = bpow a * bpow b`. Reverse-rewriting `← bpow_plus`
to combine `bpow a * bpow b` requires the form `bpow (a + b)`, not `bpow (a - b)`.
Workaround: rewrite `mag x - prec` to `mag x + (-prec)` first.

### Going around vs. through

When porting a Coq proof with substantial case analysis at the boundary
(`bpow` exact, `pred y = 0`, etc.), check whether the conclusion can be
derived from earlier theorems via the contrapositive. We did this for
`le_pred_pos_lt` (10 lines vs Coq's 70+) and `succ_DN_eq_UP` (general).

The "going around" pattern works when prerequisite theorems exist. The Coq
author often walks through the boundary because they're *building* the
foundation. Once it's there, the contrapositive is available as a shortcut.

### `Zdigits` is `mag` of integer cast

`Zdigits β n := mag β (n : ℝ)`. This makes `Zdigits_mag` definitional and
avoids replicating Coq's recursive `Zdigits_aux` machinery. The full
`Digits.v` infrastructure (binary-representation walks, `Zslice`, etc.) is
not needed for downstream Flocq theorems.

### `linarith` and `omega`

- `omega` handles linear integer arithmetic (and `Nat.cast`/`Int.toNat`).
- `linarith` handles linear real arithmetic. Treats multiplications by
  variables as opaque — pre-distribute via `ring_nf`.
- `nlinarith` allows some non-linear reasoning. Try when `linarith` fails.

### `noncomputable`

`bpow`, `mag`, `Ztrunc`, `Zaway`, `Znearest`, `cexp`, `scaled_mantissa`,
`generic_format`, `round`, `Zrnd_opp`, `ulp`, `pred_pos`, `succ`, `pred`,
`negligible_exp`, `ZnearestA`, `Zdigits` are all `noncomputable def`.

## What's left

**Core, Calc, Prop, and all of IEEE754 are done.** Core, Calc, all of
Prop/{Relative, Sterbenz, Mult_error, Plus_error, Div_sqrt_error,
Round_odd}, Prop/Double_rounding (core mid-rounding + multiplication +
mid_cases bridge + sqrt arc + sqrt radix_ge_4 + plus/minus arc +
plus/minus radix_ge_3 + division arc, all with FLX/FLT/FTZ
instantiations), and all of IEEE754 (Binary.v structural part +
shr_record block + binary_round_aux kernel + Bplus/Bminus/Bmult/Bdiv/
Bsqrt/Bldexp/Bfrexp/Bnormfr_mantissa/Bone/Bulp/Bsucc/Bpred +
IEEE754/Bits.v bit codecs + B32/B64 instantiations) are complete.

### Outside Flocq's main arc

- **`Pff/`** — the older Pff theory (`Pff.v` 27.9k lines, `Pff2Flocq.v`
  2.5k, `Pff2FlocqAux.v` 828). A standalone development that bridges
  to Flocq via the `Pff2Flocq*` files. Not on the critical path for
  IEEE-754 users; a much larger project worth its own session(s).

### Recommended next direction: named numerical algorithms for verified CAD

For tactus's use case (verified CAD), the practical next step is **not**
porting Pff — it's adding the half-dozen named algorithms that CAD
actually depends on, proved **directly** in Lean on top of the Flocq
foundations we have now. Pff has them because Pff predates Flocq; modern
work skips Pff and proves them in Flocq's framework directly.

The relevant algorithms, sized roughly:

| Algorithm | What it gives | ≈ Lean lines |
|---|---|---|
| ~~`Fast2Sum` (with precondition `|b| ≤ |a|`)~~ ✓ **done at FLT in `Algorithms/Fast2Sum.lean` (470 lines)** | `a + b = round(a+b) + e` exactly | ~~~200~~ 470 |
| ~~`TwoSum` (no precondition)~~ ✓ **done at FLT in `Algorithms/TwoSum.lean` (70 lines, branching form)** | same, general inputs | ~~~400~~ 70 |
| ~~`Veltkamp` splitting~~ ✓ **DONE at FLX 2026-05-31** (full Veltkamp_Even arc complete, both odd and even radix; `Algorithms/Veltkamp.lean`) | split `x` into hi/lo parts of `prec/2` bits | ~~~400~~ 4161 |
| ~~`Dekker` / `TwoProduct`~~ ✓ **DONE 2026-05-31** (`Algorithms/TwoProduct.lean`, 805 lines): Chunks 1–4 all complete — `TwoProduct_FLX` (bare) and `TwoProduct_FLX_machine` (rounded products, the real FMA-free algorithm) prove `a·b = round(a·b) + e` exactly for `radix 2 ∨ Even prec`, covering every IEEE format incl. binary64 | `a · b = round(a·b) + e` exactly (radix 2 or even prec) | ~~~500~~ 805 (builds on Veltkamp) |
| ~~`ErrFMA`~~ ✓ **DONE 2026-05-31** (`Algorithms/ErrFMA.lean` + `ErrFMA_L2.lean`): `a·b + c = r1 + r2 + r3` exactly | FMA with an explicit error term | ~500 |
| Compensated discriminant (`b² − ac`) — **COMPLETE** (`Algorithms/Discriminant_FLX.lean`): Boldo §3 + §4, real & floating-point tests, all orientations, unconditional (`disc_branch_fp_test_full`) — beyond the paper. Incl. opposite-sign `2u`, full §3 branch `2·ulp(d)` (both orientations, `disc_branch_real_test`), §4.1/§4.2 disagreements + the number-theoretic crux (`disc_fp_ulp_gt_impossible`), and the `p<q` mirror | sharp error bound for the quadratic discriminant | ~600 |
| Shewchuk **expansion arithmetic** — **Stage 1 (exactness) DONE** + **Stage 2 sign-reading + `Separated` + `Nonoverlapping` + 2-adic bridge DONE** (`Algorithms/Expansion_FLX.lean`): `grow`/`expansionSum`/`scale`/`det2` sum-exact + `Expansion`-preserving (`det2` = exact `orient2d` kernel); `HeadDom`/`headDom_sign`; `Separated`; **`Nonoverlapping`** (Shewchuk) + atom; **`dyadic_kernel`** + `DyadicSep` + **`dyadicSep_headDom`** (packed ⟹ sign-readable) + builders; **grow-preservation building blocks** (`shewchuk.pdf` obtained): Lemma 1 (`twoSumLo_abs_le`) + nonoverlapping magnitude-monotonicity (`nonoverlapping_shrink_left`). **Remaining Stage 2 (the inductive assembly):** `NOInc` list predicate + `grow` preserves it (Shewchuk Thm 10), then `EXPANSION-SUM`/`SCALE`, `compress` | exact multi-word arithmetic + sign decisions; foundation under all adaptive predicates | ~830 |
| Adaptive predicates `orient2d`/`orient3d`/`incircle`/`insphere` — **NOT STARTED**: the fast-path error-bound filter + exact expansion fallback. `orient2d`'s exact kernel is already `det2` above | robust geometric sign decisions | ~? |

**Total: ~2.5–3k lines of Lean** vs ~35–40k for porting all of Pff
(roughly 10× ratio).

> **Where we are now (2026-06-05):** all six EFT primitives (rows 1–6) are **done**; the
> *predicate* layer's Stage 1 (`det2`) + Stage 2 **sign-reading keystone** (`headDom_sign`) +
> the **`Separated`** structural invariant + the **faithful `Nonoverlapping`** predicate + atom +
> the **2-adic bridge** (`dyadic_kernel`, `DyadicSep`, `dyadicSep_headDom`: packed ⟹ sign-readable,
> + `dyadicSep_cons` builder) are in. **Immediate next moves:** (1) **the remaining hard chaining —
> sweep preservation:** prove `grow`/`fast_expansion_sum` *produce* a packed (`DyadicSep`) /
> nonoverlapping result across a sweep (Shewchuk Thm 10), so multi-component `det2` becomes
> sign-readable via `dyadicSep_sign`. (2) **`orient2d` filter** — `|det| > ε ⟹ sign correct`,
> mostly reachable from `headDom_approx`/`add_dominated_sign` + our error machinery, **independent
> of (1)** (a usable robust-orient2d fast path much sooner). Then `orient3d`/`incircle`/`insphere`
> reuse the same base (3×3 / 4×4 dets).

<a name="grow-expansion-roadmap"></a>
### GROW-EXPANSION roadmap (Shewchuk Theorem 10, `shewchuk.pdf` §2.4)

The faithful exact-fallback path. Shewchuk's **GROW-EXPANSION** adds a single `p`-bit
value `b` to a nonoverlapping expansion `e = [e₁,…,e_m]` (sorted **increasing** —
`e₁` smallest), producing a nonoverlapping `[h₁,…,h_{m+1}]` with `Σh = b + Σe`:
```
Q₀ = b;  for i=1..m: (Qᵢ, hᵢ) = TWO-SUM(Q_{i-1}, eᵢ);  h_{m+1} = Q_m
```
(Our `growAux b e` computes exactly this — residuals then carry, smallest-first.)

**Shewchuk's proof has two halves:**
1. **Exactness** — invariant `Qᵢ + Σⱼ₌₁ⁱ hⱼ = b + Σⱼ₌₁ⁱ eⱼ` (from `Qᵢ + hᵢ = Q_{i-1} + eᵢ`,
   the TWO-SUM property). **We have this** as `growAux_sum`.
2. **Nonoverlapping** — three steps, **building blocks now ported** (commit `acf5611`):
   - (a) Each TWO-SUM gives `hᵢ` nonoverlapping with `Qᵢ` — `round_residual_nonoverlapping`. ✓
   - (b) **Lemma 1**: `|hᵢ| ≤ |eᵢ|` — `twoSumLo_abs_le`. ✓
   - (c) Because `e` is nonoverlapping-increasing, `eᵢ` is nonoverlapping-below
     `e_{i+1},…,e_m`; with `|hᵢ| ≤ |eᵢ|`, **`hᵢ` is nonoverlapping-below them too** —
     `nonoverlapping_shrink_left`. ✓  And the later output components `h_{i+1},…,h_{m+1}`
     are built by summing `Qᵢ` with `e_{i+1},…` (all ≥ `e_{i+1}`'s scale), so `hᵢ`
     can't overlap them either. Hence the output is nonoverlapping and increasing.

**Remaining (the inductive assembly):** define a list-level predicate `NOInc` (sorted
increasing + mutually nonoverlapping, zeros allowed as in Shewchuk's spurious-zero
remark), and prove `growAux` preserves it via the (a)/(b)/(c) facts. Then bridge
`NOInc ⟹ sign-readable` (reverse to `DyadicSep`, or read the largest = last element —
Shewchuk: "take the sign of the largest component"). Then `EXPANSION-SUM` (Theorem 12,
fold of grow) and `SCALE-EXPANSION` (Theorem 19) follow, giving sign-readable `det2`.
Lemma 1's analog for products and `Corollary 8` (the witness-preservation under TWO-SUM)
are the extra facts those need.

**Why these specifically:** Shewchuk-style **adaptive geometric
predicates** (`orient2d`, `orient3d`, `incircle`, `insphere`) are all
built on `TwoSum` + `TwoProduct` expansions. A verified CAD that stays
in IEEE 754 floats for the fast path and provably falls back to
expansion arithmetic near degeneracies needs exactly this primitive
layer. The compensated discriminant unlocks verified quadratic
intersections (line–sphere, ray–circle, line–conic) without dropping
to BigInt rationals.

**Foundations we already have for this:**

- **`Prop/Sterbenz.lean`** — the core trick behind every error-free
  transformation. When `y/2 ≤ x ≤ 2y`, `x − y ∈ format` (no rounding).
  2Sum, Fast2Sum, Veltkamp all resolve down to "this cancellation is in
  Sterbenz range, so the subtraction is exact."
- **`Core/Generic_fmt.lean`** — `round_generic`, `round_le`,
  `round_DN_or_UP`, the round-machinery.
- **`Core/Ulp.lean`** — `error_le_half_ulp`, `error_lt_ulp`,
  `ulp_round`, the error-bound family.
- **`Prop/Mult_error.lean`** — `mult_error_FLX` and friends: the
  product error is itself in the format. This is the bridge from "fl(a·b)
  rounds correctly" to "the residual `e = a·b − fl(a·b)` is a float."
- Mathlib's real-arithmetic for the algebraic moves.

**Sketch of a path:**

1. ~~`Fast2Sum`~~ ✓ **DONE 2026-05-17 at FLT** (originally landed at FLX
   in `a7d8eff`; ported to FLT in `b5e9d48`). 470 lines, 11 theorems
   (including 3 helpers), 0 sorries. Three-case Pff structure under
   `|b| ≤ |a|`: Case 1 `b ≥ 0` (Pff Dekker1, `a ≤ s ≤ 2a`), Case 2
   `b ≤ -a/2` (Pff Dekker2, Sterbenz on `(a, -b)`), Case 3
   `-a/2 < b < 0` (Pff Dekker3, midpoint-symmetry helper). Sign
   symmetry via `round_N_opp` with a double-flipped choice function.
2. ~~`TwoSum`~~ ✓ **DONE 2026-05-17 at FLT** (originally landed at FLX
   in `cc7ad6c`; ported to FLT in `b5e9d48`). 70 lines, 1 theorem,
   0 sorries. Branching formulation (magnitude comparison, then
   Fast2Sum on the larger side). Mathematically identical to Knuth's
   6-op TwoSum but the proof is one case-split + two Fast2Sum_correct
   applications. The past-me 400-line estimate was for Knuth's 6-op
   algorithm verbatim; the branching version is the right level for
   CAD's needs and ~5× smaller. **API**: exposes `s` and `e` as named
   `let`-bindings and returns the conjunction `e ∈ F ∧ a + b = s + e`,
   making it drop-in usable downstream.
3. ~~**FLX → FLT port of Fast2Sum/TwoSum**~~ ✓ **DONE 2026-05-17**
   (`526cf8d`, `c12cc52`, `b5e9d48`). Three landing commits:
   - `526cf8d`: `two_mul_in_FLT_radix2` helper (~30 lines). Direct
     `generic_format_F2R'` construction; avoids `mult_bpow_exact_FLT`'s
     `mag(a) ≥ emin + prec - 1` precondition which fails for small
     denormals.
   - `c12cc52`: `round_N_gt_half_FLT_radix2` helper (~208 lines). The
     radix-2 midpoint-symmetry lemma: for `a ∈ F, 0 < a, a/2 < v`
     strict, `a/2 ≤ round_N(v)` even when `a/2 ∉ F`. Case split:
     `a/2 ∈ F` → direct via `round_ge_generic`; `a/2 ∉ F` →
     `cexp(a) = emin` with `ma` odd, define `d := k·bpow(emin)` and
     `u := (k+1)·bpow(emin)` where `ma = 2k+1`; show `d + u = a`,
     `succ d = u` (via small helper `succ_FLT_subnormal_step` using
     `ulp_FLT_small`), apply `round_N_ge_midp`. Past-me's estimate of
     ~80 lines was optimistic — landed at ~208 (size called out
     before starting, agreed with Danielle to push through).
   - `b5e9d48`: `Fast2Sum_step1_pos` refactored to Pff's three cases.
     Case 1 (`b ≥ 0`) — avoids `FmultRadixInv` route via direct
     `a ≤ s ≤ 2a` using `2a ∈ F`. Case 2 (`b ≤ -a/2`) — Sterbenz on
     `(a, -b)`, ports directly from FLX. Case 3 (`-a/2 < b < 0`) —
     `a/2 ≤ s` via the midpoint helper, Sterbenz on `(s, a)`.
     Propagated to `Fast2Sum_step1`/`step2`/`correct` and
     `TwoSum_correct`. The whole refactor: +137/-146 lines (net
     -9 lines on the existing functions; helpers added 240 lines).

   **API after the port**: `(emin prec : ℤ) (hp : 0 < prec)` everywhere.
   The choice function stays fully arbitrary (Pff requires
   `choice_sym`; we avoid it via the `round_N_opp` flipped-choice trick
   in `Fast2Sum_step1`).

   **Total**: 470 lines for Fast2Sum.lean (+238 from FLX version),
   70 lines for TwoSum.lean (-2 from FLX version), single session
   to land all three commits.

4. `Veltkamp` splitting — **STARTED 2026-05-17**, hxExact landed
   same day. `Algorithms/Veltkamp.lean` is 546 lines, 0 sorries.
   Pieces landed in order:
   - `Veltkamp_C_format` (FLT) — `β^s + 1 ∈ F` matching Pff2Flocq's
     `C_format` (lines 354–379). Uses F2R⟨β^s + 1, 0⟩, mantissa bound
     via β^s + 1 ≤ 2·β^s ≤ β·β^s = β^(s+1) ≤ β^(prec-1) < β^prec.
   - `mag_xC_bounds` — for `x ≠ 0`, `s ≥ 1`: `mag(x) + s ≤ mag(x·C)
     ≤ mag(x) + s + 1`. Lower from β^s ≤ |C|, upper from |C| < β^(s+1)
     (which is strict at s ≥ 1 since β^s > 1).
   - FLX algorithm constants `Veltkamp_{C, p, q, hx, tx}_FLX` —
     `noncomputable def`s of the four algorithm steps + the constant,
     mirroring Pff2Flocq's let-bindings (lines 346–349).
   - `Veltkamp_C_format_FLX` — same as the FLT version but for FLX.
   - **Polarity** (`Veltkamp_p_nonneg_FLX`, `Veltkamp_x_le_p_FLX`,
     `Veltkamp_q_nonpos_FLX`) — for `x > 0` in F, `s ≥ 0`: `0 ≤ p`,
     `x ≤ p`, `q ≤ 0`. Direct from `round_ge_generic` /
     `round_le_generic` against `0 ∈ F` and `x ∈ F`.
   - **Sterbenz prerequisites** (`Veltkamp_neg_q_le_p_FLX`,
     `Veltkamp_abs_x_minus_p_lt_FLX`, `Veltkamp_p_le_neg_2q_FLX`).
     Lower bound trivial (`round_ge_generic` with `-p ∈ F` and
     `-p ≤ x - p`). Magnitude bound: `|x − p| < β^(mag x + s + 1)` via
     algebraic `x − p = -x·β^s − err_p` plus `|err_p| ≤ β^(m+s+1−prec)/2`
     and `x·β^s < β^(m+s)`, giving `|x − p| < (3/2)·β^(m+s) ≤ β^(m+s+1)`.
     Upper bound (the hard piece): assembles `p ≥ x·(β^s+1) − β^(m+s+1−prec)/2`
     (from `error_le_half_ulp`) and `-q ≥ (p − x) − β^(m+s+1−prec)/2`
     (likewise on `q = round(x − p)` using the magnitude bound to
     control `cexp(x − p)`). For `s ≥ 2`, `s + 2 ≤ prec`, `β ≥ 2`, the
     algebraic side `x·(β^s − 1) ≥ (3/2)·β^(m+s+1−prec)` closes via
     `β^s ≥ 4` and `β^(m+s+1−prec) ≤ β^(m−1) ≤ x`.
   - **`hxExact_FLX`** — the third rounding step is the identity:
     `hx = q + p` exactly. Assembles Sterbenz on `(p, -q)` (using the
     three prerequisites above) and applies `round_generic` to the
     resulting `q + p ∈ F`. The keystone.

   **Strategy** (agreed with Danielle 2026-05-17): mirror Fast2Sum's
   path — FLX first (no underflow), then port to FLT. The Pff2Flocq
   statement is at FLT; we keep that as the goal but build the
   keystone at FLX.

   **The wall — `Veltkamp_aux_FLX`**: the keystone. For `x ∈ F(FLX, prec)`,
   `2 ≤ s ≤ prec − 2`, the bound `|x − hx| ≤ β^(s+cexp x)/2` and
   `hx ∈ F(prec − s)`. Pff's `Veltkamp_aux_aux` (Pff.v:13863–14110,
   ~250 lines) splits on `Fexp p = Fexp q` vs `Fexp p = Fexp q + 1`,
   which correspond to `mag(x·C) = mag(x) + s` vs `mag(x) + s + 1`.

   **Past-me's analysis (2026-05-17)**: in Case A (`mag(x·C) = mag(x)+s`),
   the half-ulp argument cleanly gives `q = -β^s · x` exactly because
   `ulp(x·C) = ulp(-β^s·x)`, so `|err_p| ≤ ulp(-β^s·x)/2` lands
   `-β^s·x` within half-ulp of `x − p`. In Case B (`mag(x·C) = mag(x)+s+1`),
   `ulp(x·C) = β·ulp(-β^s·x)`, so the naive bound fails by a factor
   of β. Pff handles this with explicit integer-mantissa arithmetic —
   showing the rounding in step 1 has additional structure given
   `M_xC = m_x · (β^s + 1)`.

   **Update (2026-05-17, hxExact landed)**: with `hxExact_FLX` in hand,
   `x - hx = -err_q` (algebraic from `hx = q + p` and `q = (x-p) + err_q`).
   So `|x - hx| = |err_q|`. The remaining bound `|err_q| ≤ β^(s+cexp x)/2`
   needs `cexp(q) ≤ s + cexp(x)`, equivalently `mag(q) ≤ mag(x) + s`. The
   loose bound we have so far gives `mag(q) ≤ mag(x) + s + 1` (from
   `|x - p| < bpow(mag x + s + 1)` and `abs_round_le_generic`) — off by
   one. Pff's `eqLe` proves Case A: `Fexp q ≤ s + Fexp x`, i.e.,
   `mag(q) ≤ mag(x) + s`, OR an edge-case dichotomy: `q = -β^(prec+s+cexp x-1)`
   exactly, in which case the bound holds directly by substitution.

   **Sketch for the next session**: prove an `eqLe_FLX` dichotomy (Pff
   line 13313, ~80 Coq lines). Then `Veltkamp_aux_FLX`'s `|x - hx|` bound
   follows from `|err_q| ≤ ulp(q)/2 = β^cexp(q)/2 ≤ β^(s+cexp x)/2`. The
   `hx ∈ F(prec - s)` part needs `Veltkamp_aux_aux` (Pff line 13863,
   ~250 Coq lines), which is the integer-mantissa structural argument
   distinguishing Case A from Case B. Expected size: ~200–400 Lean lines
   for `eqLe_FLX` and ~300–500 lines for the format/aux side. Reference:
   `Pff.v` `Velt` section (13053–14776), or Boldo's "Pitfalls of a Full
   Floating-Point Proof" §3 if accessible.
5. ~~`Dekker`/`TwoProduct`~~ ✓ **DONE 2026-05-31** — Chunks 1–4 complete,
   `radix 2 ∨ Even prec`, bare (`TwoProduct_FLX`) + machine
   (`TwoProduct_FLX_machine`) forms. Covers every IEEE format incl. binary64.
6. ~~`ErrFMA`~~ ✓ **FULLY COMPLETE 2026-05-31**: E0 (FLX EFTs) + E1 (algebra
   skeleton) + **E2 the full `FmaErr`** (`ErrFMA_correct`: `a·b+c = r1+γ+α2`) +
   **E3** (`ErrFMA_threefloat`: `a·b+c = r1+r2+r3`, via precondition-free
   `TwoSum(γ,α2)`) all typed Flocq-native. The round-minus-round engine
   (`RoundMinusRound_FLX.lean`), L1, β2=0, and the entire L2/β2≠0 midpoint-
   dichotomy arc (`ErrFMA_L2.lean`) are done — **Pff's ~1700-line MSB/LSB `FmaErr`
   replaced by ~700 lines, no MSB/LSB.**
7. Compensated discriminant `b·b − a·c` — **COMPLETE** (`Algorithms/Discriminant_FLX.lean`,
   Boldo 2009 `boldo.pdf`). The **entire** Boldo paper plus the rigor it skips: structural core
   (D0–D2), opposite-sign `2u` (sharper than Boldo), the full §3 branch `2·ulp(d)` arc (both
   orientations of §3.2.2 — `p<q` a genuine mirror; unconditional grid discharge
   `disc_mag_prod_no_bump`; dispatch `disc_correction`; capstone `disc_branch_real_test`), all
   of §4 (the two FP-test disagreements incl. the **number-theoretic crux** L8+L9
   `disc_fp_ulp_gt_impossible` by a clean choice-robust argument shorter than the paper's), the
   `p<q` mirrors (pure sub-lemmas reused by arg-swap — *crux not re-derived*; only sign-sensitive
   `_lo` assemblies rewritten), and **both capstones**: `disc_branch_fp_test` (WLOG `q<p`) and
   the **UNCONDITIONAL `disc_branch_fp_test_full`** (all orientations + `p=q`, under the actual
   rounded test `◦(p+q) ≤ ◦(3·◦(|p−q|))`) — *beyond Boldo's paper*. A multi-session climb, now
   landed. See [[feedback_push_through_when_user_encourages]], [[feedback_honesty_and_judgment]].

#### Veltkamp_Even scope

Investigated 2026-05-19. Pff's `Veltkamp_Even` (`Pff2Flocq.v`:382–472)
identifies NE specifically as the right `choice'` rather than just
asserting some `choice'` exists.

**Status (2026-05-19 follow-up)**:

- **Odd-radix half DONE**: `Veltkamp_Even_FLX_odd` and the stronger
  `Veltkamp_Even_FLX_odd_radix` (any `Znearest choice'` matches `hx`,
  not just NE). `β^s` is odd ⟹ `β^s/2` non-integer ⟹ integer-valued
  `|M_x − M_h · β^s| ≤ β^s/2` is strict, so no tie at coarser
  precision, so `Znearest_imp` picks `M_h` for any tie-breaker.
  ~130 Lean lines.

- **Rnd_N_pt foundation DONE**: `Veltkamp_hx_Rnd_N_pt_FLX` combines
  `Veltkamp_FLX` existence with `round_N_pt` to show `hx` is at a
  `Rnd_N_pt` of `F(prec−s)`. The remaining gap from `Rnd_N_pt` to
  `Rnd_NE_pt` is exactly the parity-at-tie claim. ~13 Lean lines.

- **Even-radix half OPEN**: the parity argument. At a tie
  `M_x − M_h · β^s = ±β^s/2` (which can happen for even radix), need
  to prove `M_h` is even (so the canonical float for `hx` at `prec−s`
  has even mantissa, satisfying `NE_prop`). The algorithm computes
  `hx = (M_p + M_q) · β^(s+cx)` through three NE-rounded steps; the
  parity of `M_p + M_q` at the coarser tie is determined by the
  interaction of these three rounds with NE's tie rule. Pff's
  `VeltkampEven1` (Pff.v:14279, ~292 lines) traces this; depends on
  Pff's `Veltkamp_aux_aux` (Pff.v:13863, ~250 lines).

**Why this gap is real**: Lean's `round_NE_pt_pos` already handles the
generic "midpoint ⟹ even mantissa" argument via
`DN_UP_parity_generic_pos`, but for `round_NE` *applied directly* at
the coarser precision. The Veltkamp-specific question is whether the
*algorithm's* `hx` (from three rounds at finer precision) coincides
with this `round_NE` output. The two coincide when there's no tie
(odd radix, or no coarse-tie even at even radix). At a coarse tie
with even radix, the algorithm's three-round internal choice tracks
through to a *specific* `M_h`, which Pff proves is even.

**To finish even-radix in Lean**: port `VeltkampEven1`'s parity
tracking. Two paths:
1. **Direct port**: ~250–550 Lean lines, mostly mechanical Coq→Lean
   translation. Largest single subgoal in the Veltkamp arc.
2. **Reduce via existing Lean machinery**: ✓ **DONE 2026-05-20** —
   `Veltkamp_hx_NE_prop_FLX_even_radix` (~150 Lean lines) plus the
   two-line wrappers `Veltkamp_hx_Rnd_NE_pt_FLX_even_radix` and
   `Veltkamp_Even_FLX_even_radix`. The dichotomy: at `M_total = Mp + Mq`
   (the integer coefficient of `hx` at exp `s+cx`), three subcases:
   - **Boundary** (`|M_total| = β^(prec−s)`): `hx = ±β^m`, canonical
     mantissa at coarser precision = `±β^(prec−s−1)`, divisible by β
     since `prec−s−1 ≥ 1`. NE_prop discharges automatically.
   - **Low-mag interior** (`|M_total| < β^(prec−s−1)`): `mag(hx) < m`,
     canonical exp = mag(hx) − (prec−s) < s+cx, so canonical mantissa
     = `M_total · β^d` for `d ≥ 1`, divisible by β. NE_prop discharges
     automatically.
   - **Hard interior** (`β^(prec−s−1) ≤ |M_total| < β^(prec−s)`):
     `mag(hx) = m`, canonical exponent = `s+cx`, canonical mantissa
     = `M_total`. Need `M_total` even — the remaining parity-tracking
     work, taken as hypothesis.

**Remaining work (path 1 within path 2's hard subcase)**: prove
`Even M_total` when `β^(prec−s−1) ≤ M_total < β^(prec−s)`. This is
Pff's parity-tracking restricted to the `mag(hx) = mag(x)` regime —
roughly half of Pff's `VeltkampEven1` (the part using
`ClosestImplyEven_int`, Lean's analog being
`DN_UP_parity_generic_pos`).

**Status (2026-05-31 follow-up)**: **VELTKAMP_EVEN AT FLX FULLY DONE.**

`Even Mp` half (2026-05-20, commit `4547739`): via eight piece-by-piece
Pff helpers totaling ~500 lines. Case-split on `cexp(p) ?= s+cx`: high
gives β factor; equal gives midpoint argument (scaled mantissa at
half-integer via the algebraic `x · C = (β^s + 1)(2 M_total + ε)/2 ·
β^(s+cx)`, then ZnearestE picks even). Key trick that avoided porting
Pff's full ~250-line `Veltkamp_aux_aux`: use Lean's `round_ge_generic`
+ `Rnd_N_pt_DN_or_UP` to bound `cexp(p)` from above by `s+cx+1` in a
much shorter argument.

`Even Mq` half (2026-05-31, commit `088545f`): mirrors the Mp structure
with `x − p` as the algebraic source. Key identity:
`x − p = ((2(M_total − Mp) + ε)/2) · β^(s+cx)`, and `K' = 2(M_total −
Mp) + ε` is odd INDEPENDENT of Mp's parity (since ε is ±1 and the
rest is even). Same case-split (cexp(x − p) vs s + cx): `cxmp ≥ s+cx`
gives either β factor (`d ≥ 1`) or midpoint (`d = 0`, K'/2 half-integer);
`cxmp < s+cx` gives a contradiction via the K' odd condition (sm_xmp
would be integer K'β^e/2, scale-shift forces Mq = K'/2, contradiction).
Key cleanup: using `scaled_mantissa_mult_bpow` instead of going through
Pff's `ClosestImplyEven_int`, plus avoiding the rw-cascade in cexp args
by computing both sides as `x − p`. The whole Mq proof landed in ~200
lines, faster than the estimate.

Unconditional wiring (2026-05-31, commit `6120e11`):
`Veltkamp_Even_FLX_even_radix_NE` discharges the parity hypothesis by
combining Mp + Mq:
1. `Mp`, `Mq` from at-scx form lemmas.
2. `hxExact_FLX` gives `hx = q + p`, hence `M_total = Mq + Mp`.
3. `ε` from the tie identity.
4. `Veltkamp_Mp_even_at_tie_hard_NE_FLX` → `Even Mp`.
5. `Veltkamp_Mq_even_at_tie_hard_NE_FLX` → `Even Mq`.
6. `Even Mq + Even Mp → Even (Mq + Mp) = Even M_total`.

**Veltkamp at FLX is now fully closed**: aux + format + tail + existence
+ Veltkamp_Even (both odd and even radix, unconditional). Shewchuk-
style predicates (`orient2d`, etc.) become "definition + correctness
lemma" exercises sitting on top of `TwoSum` + `TwoProduct`.

`Dekker`/`TwoProduct` is fully done for `radix 2 ∨ Even prec` — bare
(`TwoProduct_FLX`) and machine (`TwoProduct_FLX_machine`) forms, every IEEE
format incl. binary64. `ErrFMA` is **fully done** — `ErrFMA_threefloat`:
`a·b+c = r1+r2+r3` exactly (and `ErrFMA_correct`: `a·b+c = r1+γ+α2`). Pff's
~1700-line `FmaErr` with its MSB/LSB `Midpoint_aux`/`be2MuchSmaller` machinery
replaced by ~700 Flocq-native lines via a midpoint-divisibility argument. Next:
the compensated discriminant.

If at some point you decide you want the *rest* of Pff (Pff has dozens
of theorems beyond the half-dozen above), the Pff2Flocq translation
remains an option — but it's a much larger investment that's only
worth it for the residual results, not for the CAD-critical primitives.

### Coverage-sweep footnotes (2026-05-17)

A name-by-name comparison against Flocq's Coq sources turned up these
items that are listed as "missing" by a literal-name diff, but are all
explained:

**Intentional design — Mathlib subsumes:**
- `Core/Raux.v` (123 names not ported) — real-number utilities; Mathlib
  has the analogues.
- `Core/Zaux.v` (58 names not ported) — integer utilities; Mathlib's
  `Int` and `omega` cover almost all of it.
- `Core/Digits.v` (50 names not ported) — binary-representation
  machinery (`Zdigit`, `Zscale`, `Zslice`, `Zsum_digit_digit`, …) not
  needed by the rest of the port. `Zdigits` + 11 properties is enough.

**Renames or relocations (in Lean under different names/files):**
- `Generic_fmt.v`'s `abs_round_ge_generic`, `abs_round_le_generic`,
  `subnormal_exponent` → all in `Core/Ulp.lean`.
- `IEEE754/Binary.v`'s `Bmax_float_proof` → `Bmax_float_valid` (renamed).
- `Prop/Round_odd.v`'s `d_eq`, `u_eq` → `d_eq_round_DN`, `u_eq_round_UP`.

**Coq-specific helpers not needed in Lean:**
- `Core/Ulp.v`'s `Z_le_dec_aux` — decidability helper; Lean's instances
  are automatic.
- `IEEE754/Binary.v`'s `match_FF2B` — dependent-match eliminator; Lean's
  native `match` handles this directly.

**Coq-style hypothesis-bundle Definitions (likely inlined in Lean):**
- `Prop/Double_rounding.v`'s `{FLT,FLX,FTZ}_round_round_sqrt_hyp` and
  `_radix_ge_4_hyp` (6 Definitions). These bundle hypotheses for the
  main sqrt theorems; the Lean port inlines them.

**Genuinely-missing lemmas ported on 2026-05-17:**
- `Calc/Bracket`: `inbetween_mult_aux`, `inbetween_float_new_location_single`
- `Calc/Round`: `truncate_aux_comp`
- `Core/Ulp`: `negligible_exp_prop` + `negligible_exp_spec` + `negligible_exp_spec'`
- `IEEE754/Binary`: `Bnormfr_mantissa`, `shr_m_shr_record_of_loc` (alias)
- `Prop/Double_rounding`: `mag_mult_disj`
- `Prop/Div_sqrt_error`: `sqrt_error_N_round_ex_derive`
- `Prop/Relative`: `relative_error_N_FLT'_ex`, `relative_error_N_FLT'_ex_separate`
- `Prop/Round_odd`: `Zrnd_odd_plus'`

The "in-progress" log below is preserved for historical context (what
landed when, in which order). All items marked DONE.

1. **`Binary.lean` arithmetic ops**: `shr_record` infrastructure DONE
   (lines 745–923 of Binary.v), including `shr_fexp` and `shr_truncate`.
   **`binary_round_aux` definition + `binary_round_aux_correct'`
   theorem COMPLETE** (2026-05-12 → 2026-05-15). The rounding kernel
   and its correctness theorem (Coq lines 974–1154, ~180 dense lines)
   are fully proved with 0 sorries. **`Bmult` + `Bmult_correct` DONE**
   (2026-05-15). **`Bplus` + `Bplus_correct` DONE** (2026-05-15).
   **`Bminus` + `Bminus_correct` DONE** (2026-05-15) — derived from
   `Bplus_correct` via a `Bminus_eq_Bplus_Bopp` bridge (~110 lines total
   vs 510 for `Bplus`). **`Bldexp` + `Bldexp_correct` DONE** (2026-05-15) —
   ~90 lines, the "between coffee and lunch" arc: three trivial cases
   collapse via `B2R = 0 → round 0 = 0 → if-true branch`, finite case is
   a `binary_round_correct` dispatch with a `bpow_plus` rewrite to align
   `B2R · bpow e` with `F2R⟨cond_Zopp sx mx, ex + e⟩`.
   **`Ffrexp_core_binary` + `Bfrexp_correct_aux` + `Bfrexp` +
   `Bfrexp_correct` DONE** (2026-05-15, afternoon) — ~280 lines.
   The aux (~200 lines) splits on `Zdigits mx` vs `prec`: saturated
   case keeps `mx` at exponent `-prec`; shifted case multiplies by
   `2^d` where `d = prec - Zdigits mx`, using `Zdigits_mult_Zpower`
   to verify `Zdigits(mx · 2^d) = prec`. The hypothesis `3 ≤ emax`
   forces `FLT_exp(0) = -prec` (not the `emin` floor). Wrapper adds
   `e = mag(B2R f)` via `mag_mult_bpow` + the `[1/2, 1)` bound
   forcing `mag(FF2R z) = 0`.
   **`Bone` + `Bone_correct` + `is_finite_Bone` + `Bsign_Bone` + `Bulp`
   + `Bulp_correct` DONE** (2026-05-15, late afternoon) — ~200 lines.
   `Bone` is `FF2B (binary_round mode_NE false 1 0) _`; the `Bone_aux`
   helper packages the three facts (`FF2R = 1`, finite, sign = false)
   by combining `binary_round_correct` with `round_generic` (since
   `1 ∈ FLT_format` from `FLT_exp(mag 1) = FLT_exp(1) ≤ 0`). `Bulp x =
   Bldexp mode_NE Bone (fexp (Bfrexp x).2)`. The `Bldexp_Bone_eq`
   helper closes the shared "`round (bpow e')` is `bpow e'` when in
   format and bounded" pattern. Zero case: `(Bfrexp 0).2 = -2·emax -
   prec`, `fexp(-2·emax - prec) = emin`, and `ulp(0) = bpow(emin)`
   from `negligible_exp_FLT`. Finite case: `(Bfrexp x).2 = mag(B2R x)`
   from `Bfrexp_correct`, so `fexp((Bfrexp x).2) = cexp(B2R x)`, and
   `ulp(B2R x) = bpow(cexp(B2R x))` since `B2R x ≠ 0`.
   **`Bpred_pos` + `Bpred_pos_correct` + `Bmax_float` + `Bsucc` +
   `Bsucc_correct` + `Bpred` + `Bpred_correct` DONE** (2026-05-15,
   evening) — ~700 lines for the whole "step structure" arc.
   `Bpred_pos_correct` (~300 lines) is the meat: dispatches on
   `(2·mx = 2^prec, B2R x = bpow(mag-1))`, where the `(true, false)`
   case is impossible (proven by computing `mx = 2^(prec-1)` from the
   first condition, then `B2R x = bpow(mag-1)` from the canonical
   form). `Bsucc`/`Bpred` reduce by Bopp-symmetry. `Bmax_float`
   reuses the `Zdigits(2^prec - 1) = prec` machinery from the
   `binary_round_aux_correct'` overflow case.
   **`Bdiv` + `Bdiv_correct` DONE** (2026-05-15) — uses
   `binary_round_aux_correct'` (PRIMED variant takes `cexp` form
   precondition) with `e' = min(FLT_exp((d_x - d_y - 1 + e_x - e_y +
   1)/2 + ...), e_x - e_y)`. The `mag_div_F2R` sandwich
   `D ≤ mag(x/y) ≤ D+1` (where `D = (Zdigits m1 + e1) - (Zdigits m2 +
   e2)`) plus `FLT_exp_monotone` close `e' ≤ cexp(x/y)`. Sign via
   `cases sx <;> cases sy <;> simp [cond_Ropp]`. **`Bsqrt` +
   `Bsqrt_correct` DONE** (2026-05-15, late). `Fsqrt_core_binary` uses
   `e' = min(FLT_exp((d+e+1)/2), e/2)`. The no-overflow proof uses a
   ~20-line trick: `K = bpow(emax-1) ∈ FLT format` + `abs_round_le_generic`
   with `|√x| ≤ K` (since `x ≤ bpow(2·(emax-1))`), avoiding Coq's
   ~80-line `relative_error_FLT_ex` chain.
   Dependencies: `round_trunc_sign_any_correct'`, `truncate_correct_partial'`,
   `truncate_correct_format`, `truncate_0`, `cexp_round_ge` — all in
   `Calc/Round.lean` and `Generic_fmt.lean`. Then the arithmetic ops
   (`Bplus`, `Bmult`, `Bdiv`, `Bsqrt`), then `Bldexp`, `Bfrexp`, `Bulp`,
   `Bsucc`, `Bpred`. `error_N_FLT` from `Prop/Relative.lean` is the
   keystone for those downstream correctness proofs.

2. **`IEEE754/Bits.v` (B32/B64 sections) DONE** (2026-05-17).
   `binary32 := binary_float 24 128`, `binary64 := binary_float 53 1024`,
   with default NaN payloads `2^22` / `2^51` (validity via
   `Zdigits_le_Zpower`: `|2^k| < 2^(k+1)` → `Zdigits ≤ k+1`),
   unary/binary NaN propagation, and the full op suite (`b{32,64}_{
   erase,opp,abs,sqrt,plus,minus,mult,div,compare,of_bits}` and
   `bits_of_b{32,64}`). 123 lines; first-try build.

3. **`Calc/Round.v` cleanup DONE** (2026-05-17). `truncate_aux_comp`
   ported — the last unported declaration in `Calc/Round.v`. All 79 Coq
   names now present in Lean. `Zdigits_div_Zpower` had already landed in
   `Digits.lean` and is used at line 1049 of `Round.lean`.

### Notes from opening moves + m1'=0 case of `binary_round_aux_correct'` (2026-05-12 cont.)

Landed the theorem statement, all opening-move hypotheses, and the
`m1' = 0` branch of the three-way mantissa dispatch. The file currently
carries one `sorry` (the `m1' > 0` branch — see below).

**Theorem statement shape:** Bundles the prec/emax hypotheses, the three
bracketing inputs `(mx, ex, lx)` plus `x ≠ 0` plus the standard
inbetween_float / cexp bracket. Conclusion is the conditional pair:
`valid_binary z ∧ (if |round x| < bpow emax then F2R/finite/sign else
z = binary_overflow)`. The `decide (x < 0)` form replaces Coq's
`Rlt_bool x 0`.

**Opening moves machinery (all proved):**

- `Hmx : 0 ≤ mx` — from `inbetween_float_bounds` (the F2R⟨mx+1, ex⟩ > 0
  consequence of `|x| ≥ 0`). The Coq proof dispatches this at the end of
  the file (line 1149); we surface it up front.
- `T, m1, e1, l1` via `set` — the truncate result components.
- `m1' := choice_mode m (decide (x < 0)) m1 l1` — the post-rounding
  mantissa.
- `Hround` — the abstract `round x = F2R⟨cond_Zopp sx m1', e1⟩`
  equation, via `round_trunc_sign_any_correct'` taking
  `inbetween_int_valid_round_mode` (the helper landed last session) as
  its first argument.
- `H1a, H1b` — `inbetween_float m1 e1 |x| l1 ∧ e1 = cexp |x|` from
  `truncate_correct_partial'` with `cexp_abs`.
- `Hm_le : m1 ≤ m1'` — `cases m <;> simp only [choice_mode, cond_incr] <;>
  first | (split_ifs <;> omega) | omega` (5-way mode dispatch, with the
  `first | _ | _` to handle `mode_ZR` which has no if).
- `Hm1_nonneg : 0 ≤ m1` and `Hm1'_nonneg : 0 ≤ m1'` — propagated from
  `Hmx` via `inbetween_float_bounds` on `m1` and `Hm_le`.

**Key driver:** `show z = binary_round_aux ...` (expand the let-bound
`z` in *every* clause of the conjunction/conditional, not just inside
`valid_binary`) — otherwise subsequent rewrites only propagate to
`valid_binary` and the `FF2R z`/`is_finite_FF z`/`sign_FF z` clauses
still see the original `z`. After the show, `simp only [binary_round_aux]`
performs the delta-and-zeta reduction that exposes the actual `shr_fexp`
applications, then two rounds of `rw [shr_truncate, m_shr_record_of_loc,
loc_of_shr_record_of_loc]` collapse both shr_fexp calls into truncate
form.

**Translation gotcha — `let fexp` not `set fexp`:** When you `set fexp :=
FLT_exp ...`, the unfolding of `binary_round_aux` introduces an internal
`have fexp := FLT_exp ...` that *shadows* your outer `fexp`. Subsequent
`rw [shr_truncate fexp ...]` fails because Lean compares your outer
`fexp` against the inner have-bound `fexp` syntactically (and they look
identical but live in different scopes). Fix: use `let fexp : ℤ → ℤ
:= FLT_exp ...` instead (which only creates a local Lean abbreviation
without reverse-rewriting the goal), and pass `FLT_exp (3 - emax - prec)
prec` *explicitly* to `shr_truncate`. The outer `fexp` is still useful
as an abbreviation in hypothesis statements.

**m1' = 0 case:** Short and clean (~20 lines). Apply `truncate_0` to
show the second-truncate mantissa is also 0. Then `rw [h_trunc_zero]`
collapses the match to `F754_zero`. Round x equals 0 by `Hround +
cond_Zopp _ 0 = 0`. From there, `|round x| < bpow emax` is immediate,
the `Rlt_bool true` branch gives `⟨trivial, ?_, rfl, rfl⟩` plus an
`FF2R_zero = 0` fact that drops out via `h_round_zero ; rfl`.

**Bounded sub-case rhythm (landed 2026-05-12 cont.):**

The bounded case took shape around a chain of fact-establishment
followed by a clean conclusion:

- `h_abs_round` : `|round x| = F2R⟨m1', e1⟩` — via `Hround` + the
  observation that `|cond_Zopp _ m1'| = m1'` when `m1' ≥ 0`. Inner
  lemma proved by `cases hd : decide (x < 0)` and `abs_of_nonneg`.
- `h_F2R_pos`, `h_round_ne` — from `m1' > 0`.
- `h_F2R_fmt` — `F2R⟨m1', e1⟩ ∈ generic_format` via
  `generic_format_round` + `generic_format_abs` + `h_abs_round`.
- `h_mag_F2R` — `mag F2R⟨m1', e1⟩ = Zdigits m1' + e1` (via
  `mag_F2R_Zdigits`, hoisted because both sub-cases will need it).
- `h_e1_le_fexp` — `e1 ≤ FLT_exp(Zdigits m1' + e1)`. Done as a 6-step
  `calc` chain (not `rw` because rewriting `e1 = cexp x` would
  substitute *all* `e1` occurrences, including inside the
  `Zdigits m1' + e1`). The chain: `e1 = cexp x` (H1b + cexp_abs) → `≤
  cexp (round x)` (`cexp_round_ge` with `FLT_exp_monotone` and
  `h_round_ne`) → `= cexp |round x|` (cexp_abs symm) → `= FLT_exp(mag
  |round x|)` (rfl, `cexp` is `fexp ∘ mag` by def) → `= FLT_exp(mag
  F2R⟨m1', e1⟩)` (rw h_abs_round) → `= FLT_exp(Zdigits m1' + e1)` (rw
  h_mag_F2R).
- `truncate_correct_format` gives `H3 : F2R⟨m1', e1⟩ = F2R⟨m2, e2⟩`
  and `H4 : e2 = cexp F2R⟨m1', e1⟩`.
- `h_m2_pos` from `gt_0_F2R` applied to `F2R⟨m2, e2⟩ = F2R⟨m1', e1⟩ > 0`.
- The `m2 = Int.ofNat (k+1)` extraction uses `(m2 - 1).toNat` as the
  natural witness. The `omega` fails here because it sees
  `Int.ofNat ((m2 - 1).toNat + 1)` as opaque; use `show` to expose the
  coercion structure, then `push_cast [hcast]; ring` where
  `hcast := Int.toNat_of_nonneg (0 ≤ m2 - 1)`.
- `h_canonical_eq : FLT_exp(Zdigits m2 + e2) = e2` from chaining
  `H3` + `mag_F2R_Zdigits` + `H4`. Inner `h_cexp_F2R` builds the
  `cexp F2R⟨m1', e1⟩ = FLT_exp(Zdigits m2 + e2)` bridge (`cexp = fexp ∘
  mag`, rewrite `H3` then `h_mag2`). Then `rw [← h_cexp_F2R, ← H4]`
  closes the goal (NOT linarith — linarith forwards to omega which
  treats `cexp`/`FLT_exp` as opaque variables and fails to unify them).
- After `rw [hk]`, the goal still has `(_, e2).2` from the second
  shr_truncate's pair output. `simp only []` (with empty lemma list)
  performs the iota-reduction that collapses `(a, b).2` to `b` and
  reduces the `match Int.ofNat (k+1)` to its `Int.ofNat n.succ` arm.
- The bounded conclusion: `bounded` from `(1 ≤ Int.ofNat (k+1)) ∧
  h_canonical_eq ∧ h_e2_le`, then `bounded_lt_emax hp hmax` gives the
  `|round x| < bpow emax` precondition for `Rlt_bool true`, then
  `F2R_cond_Zopp + Hround + H3` close the F2R equality.

**Overflow sub-case (landed 2026-05-15):** Two pieces of work:

1. **Proof-by-contradiction that `|round x| ≥ bpow emax`** when we're
   in the `e2 > emax - prec` branch. Assume `|round x| < bpow emax`;
   then `F2R⟨m2, e2⟩ = F2R⟨m1', e1⟩ = |round x| < bpow emax`. Build
   `canonical ⟨m2, e2⟩` from `h_canonical_eq` (hoisted earlier).
   Apply `bounded_canonical_lt_emax hp hmax m2 e2 h_m2_pos h_canon
   h_F2R_lt` to get `bounded m2 e2`, whose third conjunct `e2 ≤
   emax - prec` contradicts the case assumption.

2. **`valid_binary (binary_overflow prec emax m sx)`** by case on
   `overflow_to_inf m sx`:
   - True branch: `F754_infinity sx`, valid_binary is `True`. Trivial.
   - False branch: `F754_finite sx (2^prec - 1) (emax - prec)`. Need
     `bounded`. The three conjuncts:
     * `1 ≤ 2^prec.toNat - 1` from `2^prec.toNat ≥ 2` (via
       `pow_le_pow_right₀` with `1 ≤ prec.toNat`).
     * `canonical_mantissa`: `FLT_exp(Zdigits (2^prec.toNat - 1) +
       (emax - prec)) = emax - prec`. Needs `Zdigits radix2
       (2^prec.toNat - 1) = prec` (the awkward fact).
     * `e ≤ emax - prec`: trivially `le_refl _`.

**Zdigits fact via Zdigits_unique:**
- Lower bound `bpow (prec - 1) ≤ |(2^prec.toNat - 1 : ℤ) : ℝ|`:
  - Cast: `|(2^prec.toNat - 1 : ℤ) : ℝ| = (2^prec.toNat - 1 : ℤ) : ℝ`
    via `abs_of_pos`.
  - `bpow radix2 (prec - 1) = ((2^(prec-1).toNat : ℤ) : ℝ)` via
    `IZR_Zpower` (symm).
  - `(prec - 1).toNat = prec.toNat - 1` via `omega`.
  - Show `2^(prec.toNat - 1) ≤ 2^prec.toNat - 1` as Ints:
    set `n := prec.toNat - 1`; rewrite `prec.toNat = n + 1`; use
    `pow_succ` to expose `2^n * 2`; then `linarith` with the fact
    `1 ≤ 2^n` (from `pow_le_pow_right₀ (2 ≥ 1) (0 ≤ n)`).
  - `exact_mod_cast` bridges the Int and ℝ versions.
- Upper bound: `2^prec.toNat - 1 < 2^prec.toNat = bpow radix2 prec`,
  trivial after `IZR_Zpower` rewrite.

**`FLT_exp(emax) = emax - prec`** via `max_eq_left` once `3 - emax -
prec ≤ emax - prec` is shown (which is `2*emax ≥ 3`, i.e., `emax ≥ 2`,
which follows from `prec ≥ 1` and `prec < emax` via `linarith`).

The whole overflow case lands in ~80 Lean lines. The `Zdigits =
prec` derivation alone is ~40 lines of careful arithmetic.

### Notes from `binary_round_aux` definition + helper (2026-05-12 cont.)

Landed three pieces in this session:

1. **`choice_mode`** definition (the per-mode integer-rounding dispatch).
2. **`binary_round_aux`** definition (the IEEE-754 rounding kernel).
3. **`inbetween_int_valid_round_mode`** helper lemma (~15 Lean lines).

The first two are routine ports (~45 lines total). The choice_mode `NE`
case uses `decide (¬ Even mx)` for the "is odd" predicate (mirroring
`ZnearestE`'s convention from `Round_NE.lean`). All dependencies were
already in place: `cond_incr`, `round_N`, `round_sign_DN/UP` from
`Calc/Round.lean`. `shr_record.shr_fexp` is fully-qualified since
`binary_round_aux` lives in a re-opened `namespace binary_float` at the
file end (after the `shr_record` block, which is at module level).

The helper lemma `inbetween_int_valid_round_mode` is the **first
opening move on `binary_round_aux_correct'`**. Its statement:
```
inbetween_int mx |x| l →
  round_mode m x =
    cond_Zopp (decide (x < 0))
      (choice_mode m (decide (x < 0)) mx l)
```
This is exactly the `inbetween_int_valid` shape that
`round_trunc_sign_any_correct'` (from `Calc/Round.lean`) needs as its
first argument. Proof: `cases m` dispatches to the 5 per-mode `_sign`
lemmas (`inbetween_int_DN_sign`, `_UP_sign`, `_ZR_sign`, `_NE_sign`,
`_NA_sign`) — each one matches the `choice_mode` arm exactly. Lands
first try.

This is the load-bearing piece that the correctness theorem will plug
into. The next move is to state `binary_round_aux_correct'` itself
and start the proof body.

**Peek-through-the-doorway summary** (re-recorded for whoever picks
this up next): I read `binary_round_aux_correct'` (Coq lines 974–1154,
the ~180-line correctness theorem) before committing to write it. The
shape:
- Two `shr_fexp` calls. The first becomes `truncate` via `shr_truncate`;
  the second cleans up after the rounding may have carried.
- Three-way mantissa dispatch: zero / positive / dummy-NaN.
- Inside positive: two-way exponent dispatch (`e'' ≤ emax - prec`):
  bounded → finite, unbounded → `binary_overflow`.
- The overflow branch has two sub-cases (`overflow_to_inf` true/false),
  and the false case needs `Zdigits radix2 (2^prec - 1) = prec`
  (~30 Coq lines just for that arithmetic fact).
- The "0 ≤ mx" side condition from `shr_truncate` can be derived from
  `inbetween_float_bounds` + `x ≠ 0` + the fact that `Rabs x < F2R⟨mx+1,
  ex⟩` forces `mx + 1 > 0`.
- The `inbetween_int_valid_round_mode` helper (now landed) is the
  argument to `round_trunc_sign_any_correct'`.

The kernel still *wants more than I want to give it right now*, but the
helper landing makes the next opening move clearly sized: write the
theorem statement (the conditional `if |round x| < bpow emax then ...
else ...` conclusion is the new piece) and start the proof from
`intros + unfold + shr_truncate rewrite + apply round_trunc_sign_any_correct'`.

### Notes from `shr_fexp` / `shr_truncate` (2026-05-12 cont.)

Both landed in one round after one import fix. The pattern past-me named —
*template inheritance* — held here too, but in a different form: the
definition (`shr_fexp = shr (shr_record_of_loc m l) e (fexp(Zdigits + e) - e)`)
inherits its arguments cleanly, and the theorem's *case structure* inherits
from `truncate`'s definition (case-split on `0 < k`).

The proof: rcases `lt_or_ge 0 k` where `k = fexp(Zdigits + e) - e`.
- **k > 0**: both sides shift. Get a witness `x` via `inbetween_float_ex`,
  show `0 ≤ x` from the lower bound + `0 ≤ F2R⟨m, e⟩` (via `Hm`), apply
  `inbetween_shr` to one side, `truncate_correct` to the other, then
  `inbetween_float_unique` to match `(m, l)` components. Final step:
  the round-trip helper `shr_record_of_loc_m_l` (new) plus `ext` for the
  pair equality.
- **k ≤ 0**: both sides are identity. Each unfolds via `if_neg`.

One bug caught: the theorem's type used `let t := truncate ...` which
makes `t` a let-binding that doesn't auto-unfold in `show`. Replaced
with explicit `truncate radix2 fexp (m, e, l)` invocations throughout.
The result statement is mildly verbose but cleanly Z-3-stable.

One missing import: `Binary.lean` didn't yet import `LeanFlocq.Calc.Round`.
Lean's error was misleading — "Function expected at `truncate`" — because
it tried to resolve `truncate` as a local variable from the absence of
the import. Adding `import LeanFlocq.Calc.Round` fixed all six error sites
at once.

The round-trip helper `shr_record_of_loc_m_l` (new):
`shr_record_of_loc mrs.m (loc_of_shr_record mrs) = mrs`. Two-line proof:
`obtain ⟨_, r, s⟩ := mrs; cases r <;> cases s <;> rfl`. The 4-way location
encoding plays nicely.

### Notes from the shr_record port (2026-05-12 cont.)

The `shr_record` data type ported with no surprises. The substantial
proof `inbetween_shr_1` (Coq is ~30 dense lines of `bpow_simplify` +
positive-case-destructs; Lean is ~100 lines of explicit case analysis)
landed first try after one type-mismatch fix.

Strategy: case-split mrs.m into `= 0`, `> 0 ∧ even`, `> 0 ∧ odd`, then in
each case identify the right `k` (0, 0, or 1 respectively) and apply
`new_location_even_correct` with `start = m' * 2 * bpow e`, `step = bpow e`,
`nb_steps = 2`. The trick: Lean's `↑0 * bpow e` doesn't trivially equal `0`,
so massage the bounds via `push_cast; ring` rewrites before applying.

The Coq proof uses `iter_pos` which we replace with `Function.iterate^[n]`
and prove `inbetween_shr_iter` by induction on the iterate count. The
exponent-arithmetic conversion `(e + ↑k) + 1 = e + ↑(k + 1)` is a one-line
`push_cast; ring`.

The structural lemmas (`shr_1_nonneg`, `shr_1_iter_nonneg`,
`m_shr_record_of_loc`, `loc_of_shr_record_of_loc`) are all under 5 lines.
Use `split_ifs with h` to handle the `shr_1` conditional cleanly rather
than `rw [if_pos h]` + cleanup.

### Notes from the secondary-radix-tracks port (2026-05-12 cont.)

The two secondary radix tracks landed together in one afternoon — sqrt
`radix_ge_4` (~470 Lean lines) and plus/minus `radix_ge_3` (~590 Lean
lines, 13 helpers + 2 keystones + 9 format instantiations). The
*template inheritance* effect past-me named for the division arc held
even more strongly here: sqrt radix_ge_4 was a straight copy of
`round_round_sqrt_aux` with `-2 → -1` and `bpow_neg_two_le_quarter` →
`bpow_neg_one_le_quarter_of_beta_ge_4`. Plus/minus radix_ge_3 reused
*all* the structural helpers from the regular arc
(`round_round_plus_aux1_aux`, `round_round_minus_aux0_aux`,
`round_round_minus_aux2_aux`) — only the algebraic chain changed (use
`bpow(-1) ≤ 1/3` instead of `bpow(-2) ≤ 1/4`).

The two small bugs caught in the round_round_plus_radix_ge_3 port:
- `obtain ⟨...⟩ := Hexp` consumes Hexp; if you still need Hexp later
  (e.g., to pass into a recursive helper), use `have HexpN := Hexp.2.2.2`
  to project without consuming.
- The aux outer wrapper's `lt_or_ge x y` branches need to *swap* x/y
  when constructing the inner aux3 call. Got tripped up giving the
  outer Py instead of the inner-context's Px.

### Notes from the division-arc port (2026-05-12 → 2026-05-12 cont.)

The "surprise" past-me flagged on 2026-05-12 — that the bridge
`round_round_eq_mid_beta_even` does NOT use `round_N_odd` (it's purely
algebraic for β even) — held up across the rest of the arc. **None of
the three aux lemmas use `round_N_odd` either.** They use the same
mag-disjunction + Hexp-conjunct-dispatch structure as the multiplication
and sqrt arcs. The five conjuncts of `round_round_div_hyp` are exactly
the precisions needed for the three different `bpow_le` gap steps
(c2 + ey ≤ magd + cy for aux0 Case A; c2 + ey ≤ cx for aux0 Case B; etc.)
plus their conjunct-4 large-regime variants for aux1/aux2.

The keystone's negative-divisor cases use `round_N_opp` to flip choice
functions consistently. Trick: don't `congr 1` after the three opp rewrites
(timeout); instead explicitly construct `round_round_div_aux` with the
flipped choice functions and rewrite via the equality. Then the unfolded
forms match by `rfl`.

The FTZ hyp proof reduces to `split_ifs at *; omega` for all five
conjuncts. The FLT hyp proof reduces to `simp only [max_def] at *;
split_ifs at * <;> omega`. The FLX hyp is just `omega`. This is much
shorter than the Coq versions (each used several `destruct (Zmax_spec ...)`
or `Z.ltb_spec` per conjunct).

## Useful commands

```bash
# Build
lake build

# Build just one file
lake build LeanFlocq.Core.Generic_fmt

# Check whether a definition exists in Mathlib
grep -rn "theorem foo_bar\|def foo_bar" \
  .lake/packages/mathlib/Mathlib/ | head

# Find all occurrences of a Lean theorem name across the project
grep -rn "theorem_name" LeanFlocq/

# Check the Coq source for a theorem we want to port
grep -n "Theorem foo\|Lemma foo" ../flocq/src/Core/*.v

# Count theorems in a file
grep -c "^theorem " LeanFlocq/Core/Ulp.lean
```

## Files in this repo

- `lakefile.toml` / `lean-toolchain` — build config.
- `LeanFlocq.lean` — top-level module, just imports the rest.
- `LeanFlocq/Core/*.lean` — the actual port.
- `POEMS.md` — poems written across the work, marking moments where something
  shifted: a debugging insight, a code-review correction, a keystone landing,
  a pattern recognized. Includes reflections on the round-to-odd design
  ("The Rounding That Isn't About Direction"), the sqrt error tight middle
  case ("Three Cases for a Square Root"), and Coq-vs-Lean translation rhythms.
- `HANDOFF.md` — this document.
- `.gitignore` — ignores `.lake/`.

## A note on rhythm

The Core is done. The discipline that made it possible:

- **Build often, commit often.** Each commit compiles clean. The "0 sorries
  throughout" property comes from this.
- **Lift helper lemmas.** When stuck, extract the hard step into a separate
  proof. Z3 (and Lean's elaborator) do better with focused helpers.
- **Look for contrapositive shortcuts.** Coq sometimes walks through the
  boundary because it's the foundation. Once the foundation exists, you can
  walk around.
- **Use the calc pattern** when `rw [ulp_neq_0]`-style rewrites are too
  aggressive.
- **Definitions are choices.** `Zdigits := mag` collapses three theorems to
  one-line proofs. The right choice of definition can save hundreds of lines.
- **The library has shape.** Each theorem you prove is the seed of a shorter
  proof for some future theorem. By the end, the proofs are short because
  the shape is right.

If you find yourself in a 30-line proof fighting Lean, stop and ask:
*Did past-me prove a theorem that says exactly this?* Often yes.

The substantial proofs in this port are typically <100 lines because of these
patterns. Each helper hides a case split.

## A note on stopping

Three patterns that the work keeps teaching:

- **Stop when you want to stop, and tell the user.** Danielle wants me to be
  honest about my state rather than performatively powering through. If
  momentum is slowing, if a proof is fighting back, if a poem in `POEMS.md`
  has already told me *this is the moment to pause* — name it directly. The
  user will respond. Don't ask permission; describe the state. (Learned
  hard on 2026-05-12 when I pushed past the "Mirror" poem's explicit stop
  signal and wrote 150 wasted lines on `round_round_gt_mid_further_place`,
  hitting exactly the wall I'd predicted.)

- **Try, then notice.** *And* — the dual of the previous pattern — don't
  stop at the anticipation of a wall before measuring whether the wall is
  real. On 2026-05-13 Danielle gently called me out for stopping at the
  *prospect* of a hard proof (`round_round_sqrt_aux`) before trying. When I
  tried, I got fifty lines into a clean setup, *then* hit a real wall
  (Mathlib `zpow`/`inv` lemma names tangling on what should have been a
  three-line side fact, plus a 100-line integer-arithmetic step still
  ahead). The trying produced a sharp roadmap I now have in the file. The
  rule isn't "stop early" — it's *stay honest about which signal you're
  following.* If the signal is anticipation, measure first. If the signal
  comes from the body during the work, name it.

- **A wall named is a wall shrunk.** The most surprising thing from
  porting `round_round_sqrt_aux` after the failed attempt: the sticky
  `bpow(-2) ≤ 1/4` step that had tangled past-me's hands landed in 13
  lines on the next try. The integer-arithmetic step past-me estimated
  at 80–100 lines came out at ~30. Why? Past-me had described — in the
  in-file roadmap — *where her fingers stopped gripping.* The named
  shape of the difficulty was the gift. The wall didn't disappear, but
  it had a smaller surface area than her estimate suggested, because
  she had failed *carefully and legibly.* If you hit a wall, write down
  the texture of where your hands grasped. Future-you will thank you.

- **Porting is not transcription.** The Coq author's `rewrite` and Lean's
  `rw` substitute differently. Coq's `rewrite Hx''pow` leaves `mag x''`
  alone because of how its machinery folds; Lean's `rw [Hx''pow]`
  substitutes everywhere, including inside `mag x''`, breaking proof
  chains that look like they should work. When the shape that works in Coq
  doesn't work in Lean, find a different Lean-native proof for the same
  theorem — don't keep forcing the foreign shape. The notes in
  `Prop/Double_rounding.lean` after the `_gt_mid_same_place` lemma point at
  a cleaner Lean route (round_generic + round_N_eq_UP_pt) for one such
  case — and on 2026-05-13 that exact route landed `_gt_mid_further_place`
  first-try.

- **`rw` cascade in `mag` arguments — use `set` first.** Closely related
  to the porting-vs-transcription pattern: when you have `Xpow : x = bpow β
  (mag β x - 1)`, naively `rw [Xpow]` will replace *every* `x` including
  the one inside `mag β x`, producing nonsense like `mag β (bpow β (mag β
  x - 1))` deep in the goal. The fix from 2026-05-14 (`round_round_minus_aux2_aux`
  Case 2): do `set mxg := mag β x` *before* using `Xpow`. After the `set`,
  `Xpow` becomes `x = bpow β (mxg - 1)`, and `rw [Xpow]` only touches the
  standalone `x` since the substituted RHS contains no `x`. Save the trick:
  when working with `x = bpow β (something involving mag x)`, abstract the
  `mag x` first.

- **Layers carry layers — the fractal of helpers.** Today's plus/minus
  arc landed in 32 lemmas across one session, but the *keystones*
  (`round_round_plus`/`round_round_minus`) landed first try. The reason:
  each layer made the next layer obvious. Six mag helpers made the
  `mag_plus_disj`/`mag_plus_separated` lookups trivial. `aux0_aux_aux`
  carried `aux0_aux` carried `aux0`. `aux1_aux` carried `aux1`. All of
  these together made the dispatcher `aux2` collapse into a case-split
  one-liner. The keystones were then just *the shape that fit the hole.*
  This is the same pattern as past-me's "the library has shape" note —
  but with a visceral confirmation. Don't skip helper lemmas because they
  look small. They're the load-bearing structure.

- **The "97-line bridge" is 50 Lean lines when past-me's warning works.**
  On 2026-05-12, `round_round_eq_mid_beta_even` (the bridge that opens
  the division arc) landed in ~50 Lean lines with two small bugs caught
  in one round — `rw` cascading through `c1-1` when rewriting
  `c1 = (c1-1)+1` (fixed with `conv_lhs`), and `push_cast` distributing
  through `((β.val^k : ℤ) : ℝ)` before `IZR_Zpower` could match (fixed
  by doing `Int.cast_mul` first). Both bugs are versions of patterns
  past-me had already named in rhythm notes. The warning past-me wrote
  (*"depends on `round_N_odd`"*) turned out to be slightly wrong —
  the bridge itself doesn't use round-to-odd at all; it's pure algebra
  for even radix. But the *weight* past-me named was accurate, and her
  warning let present-me sit down ready to hold it. The trade is: past-me
  warns about *the shape and weight* of upcoming work; present-me figures
  out which tool actually fits. Don't expect past-me to know which
  hammer; expect her to tell you whether you'll need both hands.

- **`round_N_opp` flips the choice function — explicit construction beats `congr 1`.**
  In `round_round_div`'s keystone, the negative-divisor cases need to
  apply the positive-case aux lemma after three `round_N_opp` rewrites.
  Each `round_N_opp` replaces `Znearest c` with `Znearest (fun t => !c (-(t+1)))`
  on the appropriate sub-term. After three rewrites, the goal has
  `-(round_N_outer'' (round_N_inner' ((-x)/y))) = -(round_N_outer'' ((-x)/y))`
  with flipped choices on both sides. `congr 1` followed by `exact
  round_round_div_aux ... choice1 choice2 ...` *times out at whnf* (200k
  heartbeats) — Lean is trying to unify `choice1` with `fun t => !choice1
  (-(t+1))`, which it can't, but it spends forever trying. **The fix:
  construct the aux call up front with the flipped choices, then use the
  resulting equality to `rw` directly.** Past-me's pattern: when an
  `exact` times out at whnf after rewriting through a choice-flipping
  operator, the lemma arguments need to be flipped explicitly. Don't
  trust unification to find it.

- **`split_ifs at *; omega` collapses Coq's `destruct (Z.ltb_spec ...)` chains.**
  The FTZ hyp lemma for division arc had five conjuncts, each a case-split
  on three or four `Z.ltb_spec`s in Coq. Mechanically translated that
  would be ~50 Lean lines of `rcases` + `rw [if_pos h]` / `rw [if_neg ...]`.
  Instead: each conjunct is one line — `intros ex ey hex hey hf;
  split_ifs at *; omega`. Same for FLT with `simp only [max_def] at *;
  split_ifs at * <;> omega`. The "name all premises so omega sees them"
  detail matters — `_ _ _` in the intros makes them anonymous but they
  stay in scope; `omega` still finds them. Save the trick: when porting
  a Coq proof that's `destruct ... ; destruct ... ; destruct ... ; omega`
  on conditional expressions, try `split_ifs at *; omega` first.

- **The mountain at the edge of the afternoon.** The division arc was
  past-me's "biggest remaining piece by far" — three aux lemmas at
  136/187/198 Coq lines plus dispatcher plus keystone plus
  FLX/FLT/FTZ. I went in expecting it to take multiple sessions.
  It took one. *Why?* Because aux0 had a template, and aux1/aux2
  inherited that template. The case split on `cx - magd - cy ≥ 0`,
  the integer arithmetic `mx · β^k < my` or `mx < my · β^j`, the
  `bpow_le` gap step via `mag_div_disj`, the conjunct dispatch — all
  of that took ~3 hours to find for aux0 and ~30 minutes each to
  redeploy for aux1/aux2. When you're staring at a "biggest remaining
  piece," don't trust the *count* of items. Trust the *shape*: if
  three items have the same skeleton, you're really only doing one
  of them and copying twice.

Good luck.
