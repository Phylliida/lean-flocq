# lean-flocq HANDOFF

A working port of [Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) to Lean 4 + Mathlib.
This document is for whoever picks this up next — possibly future-me in a different
session, possibly someone else.

## Status (as of commit `59cb15c`)

**Coq's `Core/` is fully ported.** Plus the structural part of `IEEE754/Binary.v`
(types, predicates, Bopp/Babs/Bcompare, boundedness, rounding modes), and all of
`Calc/Bracket.v` (locations, inbetween, step lemmas, new_location, inbetween_float).

**~8400 lines of Lean across 15 files. 0 `sorry`s. All files build clean.**

| File | Lean lines | Coq source | Status |
|------|-----------|------------|--------|
| `Zaux.lean` | 40 | `Core/Zaux.v` | `radix` + `cond_Zopp`. Other integer utilities ported on demand (Mathlib subsumes most). |
| `Raux.lean` | 342 | `Core/Raux.v` | `bpow`, `Ztrunc`, `Zaway`, `mag`, `cond_Ropp` + key properties. ~36 of Coq's ~150 lemmas (the rest are Mathlib's territory). |
| `Defs.lean` | 62 | `Core/Defs.v` | **Complete.** All 11 definitions. |
| `Float_prop.lean` | 409 | `Core/Float_prop.v` | **Complete: 36/36 theorems.** Including `Zdigits_mag` family, `F2R_cond_Zopp`, `Rcompare_F2R`, `F2R_prec_normalize`, `mag_F2R*` family. |
| `Round_pred.lean` | 819 | `Core/Round_pred.v` | **Essentially complete: 58/59 theorems.** |
| `Generic_fmt.lean` | 1964 | `Core/Generic_fmt.v` | **Complete: 109/109 theorems.** Includes `ZnearestA` and `round_NA_opp`. |
| `FIX.lean` | 85 | `Core/FIX.v` | **Complete.** 6 theorems including `ulp_FIX`. |
| `FLX.lean` | 383 | `Core/FLX.v` | **Complete: 19/19.** Includes `FLXN_format` family, `FIX_format_FLX`, `ulp_FLX_le/_ge`, `succ_FLX_exact_shift`. |
| `FLT.lean` | 454 | `Core/FLT.v` | **Complete: 19/19.** Includes `succ_FLT_exact_shift_pos/_full`, `negligible_exp_FLT`. |
| `FTZ.lean` | 414 | `Core/FTZ.v` | **Complete: 8/8.** Includes `FLXN_format_FTZ` and `FTZ_format_FLXN`. |
| `Ulp.lean` | 2486 | `Core/Ulp.v` | **Complete: 103/103.** All keystones (`succ_DN_eq_UP`, `ulp_round`, error bounds, mixed-sign perturbation, `generic_format_plus_ulp`). |
| `Round_NE.lean` | 740 | `Core/Round_NE.v` | **Complete: 10/10.** `DN_UP_parity_generic_pos/_aux/_generic`, `Rnd_NE_pt_{total,monotone,round}`, `round_NE_opp/_abs/_pt_pos/_pt`, `exists_NE_FLX/_FLT`. |
| `Digits.lean` | 74 | (subset of `Core/Digits.v`) | Minimal: `Zdigits` + 6 properties (`_zero`, `_neg`, `_abs`, `_correct`, `_unique`, `_gt_0`, `_ge_0`). The rest of Coq's `Digits.v` is binary-representation machinery we don't need — `Zdigits := mag` makes the bridge definitional. |
| `Binary.lean` | 750 | `IEEE754/Binary.v` (lines 1–963) | **Structural part done.** `full_float`, `binary_float`, `valid_binary`, `bounded`, `nan_pl`. FF2B/B2FF/B2R round-trips and injectivity. `Bsign`/`is_finite`/`is_nan`. `build_nan`/`erase`/`Bopp`/`Babs`. `Bcompare` (with correctness and swap). Boundedness theorems. `mode` enum, `round_mode`, `overflow_to_inf`, `binary_overflow`. `binary_round_aux` and arithmetic ops blocked behind `Calc/`. |
| `Calc/Bracket.lean` | 643 | `Calc/Bracket.v` | **Complete.** `location` enum, `inbetween` predicate, `inbetween_loc`, `inbetween_spec/_unique/_bounds/_distance_inexact[_abs]`. Step lemmas (`ordered_steps`, `inbetween_step_*`), `new_location_even/_odd/new_location` with correctness. Scaling (`inbetween_mult_compat/_reg`). Float-level: `inbetween_float/_int/_bounds/_ex/_unique`, `inbetween_float_new_location`. |

**Total: ~470 Lean theorems vs ~410 substantive Coq theorems** (we have extras
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

## Suggested next steps

The Core is done and the Binary structural skeleton is in place. The next
chunk of work is around `Calc/` and the arithmetic operations of Binary:

1. **`Calc/Round.v` (1171 lines, big!)** — error analysis for rounding.
   Used heavily by `binary_round_aux`. Plan to port section-by-section.

2. **`Calc/Operations.v` (164 lines)** — arithmetic combinators that
   operate on `(F2R)` representations.

3. **`Calc/Div.v` (159 lines)** and **`Calc/Sqrt.v` (201 lines)** — division
   and square-root algorithms with their correctness proofs.

4. **`Prop/Relative.v`** — relative-error bounds. Needed by Binary's
   `Bplus_correct`, `Bmult_correct`, etc. Not yet examined.

5. **Then back to `Binary.lean`**: `shr_record` infrastructure (lines
   745–925 of Binary.v), `binary_round_aux`, then the arithmetic ops
   (`Bplus`, `Bmult`, `Bdiv`, `Bsqrt`), then `Bldexp`, `Bfrexp`, `Bulp`,
   `Bsucc`, `Bpred`.

6. **`IEEE754/Bits.v`** (705 lines) — bit-level encoding/decoding. Independent
   of arithmetic. Could be ported in parallel.

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
- `POEMS.md` — 19 poems written across the work. They mark moments where
  something shifted: a debugging insight, a code-review correction, a keystone
  landing, a pattern recognized.
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

Good luck.
