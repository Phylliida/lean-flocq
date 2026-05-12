# lean-flocq HANDOFF

A working port of [Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) to Lean 4 + Mathlib.
This document is for whoever picks this up next — possibly future-me in a different
session, possibly someone else.

## Status (as of commit `bb062ae`)

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
**the core mid-rounding theorems + multiplication arc + bridge + entire
sqrt arc + entire plus/minus arc with FLX/FLT/FTZ instantiations of
`Prop/Double_rounding.v`** (`_lt_mid` and `_gt_mid` families with
dispatchers, `round_round_mult` with FLX/FLT/FTZ corollaries,
`round_round_mid_cases` bridge, `round_round_sqrt_aux` keystone,
`round_round_sqrt` and FLX/FLT/FTZ corollaries, six mag helpers,
the full plus/minus aux family, **`round_round_plus`** and
**`round_round_minus`** keystones, plus their FLX/FLT/FTZ
instantiations), and **the encoding/decoding core of `IEEE754/Bits.v`**
including both round-trip theorems. The IEEE 754 binary encoding is now
a proven bijection between `binary_float` and integers in
`[0, 2^(mw+ew+1))`.

**~20700 lines of Lean across 27 files. 0 `sorry`s. All files build clean.**

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
| `Ulp.lean` | 2486 | `Core/Ulp.v` | **Complete: 103/103.** All keystones (`succ_DN_eq_UP`, `ulp_round`, error bounds, mixed-sign perturbation, `generic_format_plus_ulp`). |
| `Round_NE.lean` | 740 | `Core/Round_NE.v` | **Complete: 10/10.** `DN_UP_parity_generic_pos/_aux/_generic`, `Rnd_NE_pt_{total,monotone,round}`, `round_NE_opp/_abs/_pt_pos/_pt`, `exists_NE_FLX/_FLT`. |
| `Digits.lean` | 192 | (subset of `Core/Digits.v`) | Minimal: `Zdigits` + 9 properties (`_zero`, `_neg`, `_abs`, `_correct`, `_unique`, `_gt_0`, `_ge_0`, `_le_Zpower`, `_div_Zpower`). The rest of Coq's `Digits.v` is binary-representation machinery we don't need — `Zdigits := mag` makes the bridge definitional. |
| `Binary.lean` | 813 | `IEEE754/Binary.v` (lines 1–963) | **Structural part done.** `full_float`, `binary_float`, `valid_binary`, `bounded`, `nan_pl`. FF2B/B2FF/B2R round-trips and injectivity. `Bsign`/`is_finite`/`is_nan`. `build_nan`/`erase`/`Bopp`/`Babs`. `Bcompare` (with correctness and swap). Boundedness theorems. `mode` enum, `round_mode`, `overflow_to_inf`, `binary_overflow`. `binary_round_aux` and arithmetic ops blocked behind `Calc/`. |
| `Calc/Bracket.lean` | 643 | `Calc/Bracket.v` | **Complete.** `location` enum, `inbetween` predicate, `inbetween_loc`, `inbetween_spec/_unique/_bounds/_distance_inexact[_abs]`. Step lemmas (`ordered_steps`, `inbetween_step_*`), `new_location_even/_odd/new_location` with correctness. Scaling (`inbetween_mult_compat/_reg`). Float-level: `inbetween_float/_int/_bounds/_ex/_unique`, `inbetween_float_new_location`. |
| `Calc/Round.lean` | 1524 | `Calc/Round.v` | **Complete.** `cexp_inbetween_float[_loc_Exact]`, `cond_incr`, `inbetween_float_round[_sign]`. All 6 mode families: DN/UP/ZR/N/NE/NA, both unsigned and signed, `inbetween_int_*` and `inbetween_float_*`. `truncate_aux`, `truncate`, `truncate_0`, `truncate_correct_partial[_partial']`/`_correct[_correct']`. `generic_format_truncate`, `truncate_correct_format`. Generic correctness: `round_any_correct`, `round_trunc_any_correct[_']`, `round_sign_any_correct`, `round_trunc_sign_any_correct[_']`. **All 30 per-mode aliases** for DN/UP/ZR/NE/NA. `truncate_FIX`, `truncate_FIX_correct`. |
| `Calc/Operations.lean` | 137 | `Calc/Operations.v` | **Complete: 13/13.** `Falign[_spec[_exp]]`, `Fopp` + `F2R_opp`, `Fabs` + `F2R_abs`, `Fplus` + `F2R_plus`, `Fplus_same_exp`, `Fexp_Fplus`, `Fminus` + `F2R_minus`, `Fminus_same_exp`, `Fmult` + `F2R_mult`. |
| `Calc/Div.lean` | 213 | `Calc/Div.v` | **Complete.** `mag_div_F2R`, `Fdiv_core` + `Fdiv_core_correct`, `Fdiv` + `Fdiv_correct`. Helpers: `quot_eq_mul_bpow`, `fdiv_pair`, `fdiv_pair_quot`. |
| `Calc/Sqrt.lean` | 256 | `Calc/Sqrt.v` | **Complete.** `mag_sqrt_F2R`, `int_sqrtrem` (Int.sqrt remainder semantics), `Fsqrt_core` + `Fsqrt_core_correct`, `Fsqrt` + `Fsqrt_correct`. |
| `Prop/Relative.lean` | 760 | `Prop/Relative.v` | **Complete.** Conversion lemmas (lt/le, both directions). Generic family: `relative_error[_ex/_F2R_emin/_F2R_emin_ex/_round/_round_F2R_emin]`, `relative_error_N[_ex/_F2R_emin/_F2R_emin_ex/_round/_round_F2R_emin]`. FLX family: `_FLX_aux/_FLX/_FLX_ex/_FLX_round/_N_FLX/_N_FLX_ex/_N_FLX_round`. FLT family: `_FLT_aux/_FLT/_FLT_F2R_emin[_ex]/_FLT_ex/_N_FLT[_ex]/_N_FLT_round/_N_FLT_F2R_emin[_ex]/_N_FLT_round_F2R_emin`. Combined: `error_N_FLT_aux`, `error_N_FLT`. **Unit-roundoff family complete:** `u_ro/u_ro_pos/u_ro_lt_1/u_rod1pu_ro_pos/u_rod1pu_ro_le_u_ro`, `relative_error_N_FLX'` (the tighter `u_ro/(1+u_ro)` bound via ufpx), `relative_error_N_FLX'_ex`, `relative_error_N_round_ex_derive`, `relative_error_N_FLX_round_ex`. |
| `Prop/Sterbenz.lean` | 119 | `Prop/Sterbenz.v` | **Complete: 4/4.** `generic_format_plus` (sum stays in F when bounded by `β^(min(mag x, mag y))`), `generic_format_plus_weak` (weak version with `min(\|x\|, \|y\|)`), `sterbenz_aux` (helper `y ≤ x ≤ 2y → x - y ∈ F`), `sterbenz` (the keystone: `y/2 ≤ x ≤ 2y → x - y ∈ F`). |
| `Prop/Mult_error.lean` | 351 | `Prop/Mult_error.v` | **Complete: 7/7.** FLX: `mult_error_FLX_aux` (the keystone — produces an explicit float for the error at exponent `cx + cy`), `mult_error_FLX`, `mult_bpow_exact_FLX`. FLT: `mult_error_FLT`, `F2R_ge`, `mult_error_FLT_ge_bpow`, `mult_bpow_exact_FLT`. |
| `Prop/Plus_error.lean` | 670 | `Prop/Plus_error.v` | **Complete: 20.** Keystones: `round_repr_same_exp`, `plus_error_aux`, `plus_error`. Zero family: `FLT_format_plus_small`, `round_plus_neq_0_aux`, `round_plus_neq_0`, `round_plus_eq_0`. Trivial bounds: `plus_error_le_l/r`. Helpers: `ex_shift`, `mag_minus1`, `lt_mag`, `mag_minus_lb`. mult_ulp section: `round_plus_F2R`, `round_plus_ge_ulp`. plus_ge family: `round_FLT_plus_ge`, `round_FLT_plus_ge'`, `round_FLX_plus_ge`. **Unit-roundoff variants:** `FLT_plus_error_N_ex` and `FLT_plus_error_N_round_ex`. |
| `Prop/Div_sqrt_error.lean` | 1328 | `Prop/Div_sqrt_error.v` | **Complete (file fully ported).** Keystones: `generic_format_plus_prec`, `div_error_FLX`, `sqrt_error_FLX_N`. Sqrt unit-roundoff helpers: `om1ds1p2u_ro_pos`, `s1p2u_rom1_pos`, `om1ds1p2u_ro_le_u_rod1pu_ro`. Main sqrt error theorem and variants: `sqrt_bpow_even`, `sqrt_error_N_FLX_aux1/_aux2/_aux3`, `sqrt_error_N_FLX`, `sqrt_error_N_FLX_ex`, `sqrt_error_N_FLX_round_ex`, `sqrt_bpow_ge`, `sqrt_error_N_FLT_ex`, `sqrt_error_N_FLT_round_ex`. format_REM family: `format_REM_aux`, `format_REM_pos` (private), `format_REM`, `format_REM_ZR`, `format_REM_N`. Note: `sqrt_error_N_FLX_aux2` strengthened to `prec > 1` to avoid edge case at prec=1, β=2 where `1 + 2u_ro = β`. |
| `Prop/Round_odd.lean` | 1427 | `Prop/Round_odd.v` | **Complete.** Z-level: `Zrnd_odd` (the rounding function — rounds non-integers to the odd integer between floor and ceiling), `valid_rnd_odd`, `Zrnd_odd_Zodd`, `Zfloor_plus`, `Zceil_plus`, `Zeven_abs`, `Zrnd_odd_plus`. R-level: `Rnd_odd_pt` predicate, `Rnd_odd`, `Rnd_odd_pt_opp_inv`, `round_odd_opp`. Core: `round_odd_pt` (the keystone), `Rnd_odd_pt_unique`, `Rnd_odd_pt_monotone`. **Odd_prop_aux geometry (Stage 5):** `generic_format_fexpe_fexp`, `exists_even_fexp_lt`, `d_eq_round_DN`, `u_eq_round_UP`, `d_ge_0`, `mag_d`, `Fexp_d`, `format_bpow_x`, `format_bpow_d`, `d_le_m`, `m_le_u`, `mag_m`, `mag_m_0`, `u'_eq`, `m_eq`, `m_eq_0`, `fexp_m_eq_0`, `Fm`, `Zm`, `DN_odd_d_aux`, `UP_odd_d_aux`. **Keystones:** `round_N_odd_pos` (the no-double-rounding theorem for positive x — rounding-to-nearest of round-to-odd at coarser precision equals rounding-to-nearest directly, when fexpe ≤ fexp - 2 and β even) and `round_N_odd` (general form via opp symmetry). **Stage 6 (cexp preservation):** `mag_round_odd` and `fexp_round_odd` (FLT, β even, prec > 1: round-to-odd preserves both `mag` and `cexp`). |
| `Prop/Double_rounding.lean` | 2983 | `Prop/Double_rounding.v` (~62% by lines) | **Core mid-rounding + multiplication + bridge + full sqrt arc + full plus/minus arc + division-arc preludes.** Definitions: `round_round_eq`, `midp`, `midp'`. **`_lt_mid` family:** `_further_place'`, `_further_place`, `_same_place`, `_lt_mid` dispatcher. **`_gt_mid` family:** `_further_place'`, `_further_place` (with the `x'' = bpow(mag x)` edge case via `round_generic` + `Znearest_imp`), `_same_place`, `_gt_mid` dispatcher. **Multiplication arc:** `round_round_mult_hyp`, `round_round_mult_aux`, `round_round_mult`, `round_round_mult_FLX/_FLT/_FTZ`. **Bridge:** `round_round_mid_cases`. **Sqrt arc:** `round_round_sqrt_hyp`, `mag_sqrt_disj`, `bpow_neg_two_le_quarter`, `round_round_sqrt_aux` (300-line keystone), `round_round_sqrt` + FLX/FLT/FTZ. **Plus/minus arc:** `round_round_plus_hyp` (4-conjunct precision condition), six mag helpers (`mag_plus`/`mag_minus` in Raux, `mag_plus_disj`/`mag_plus_separated`/`mag_minus_disj`/`mag_minus_separated`), `bpow_neg_one_le_half` helper, **plus aux family** (`aux0_aux_aux` → `aux0_aux` → `aux0`, `aux1_aux` → `aux1`, `aux2`, `aux`), **minus aux family** (`aux0_aux` → `aux0`, `aux1`, **`aux2_aux`** the big case-split on whether `x` strictly exceeds `bpow(mag x - 1)`, `aux2`, `aux3`, `aux`), **`round_round_plus`** and **`round_round_minus`** keystones (dispatching on signs via `round_N_opp` and `generic_format_opp`), plus FLX/FLT/FTZ instantiations for both `plus` and `minus` (3 hyp lemmas + 6 user-facing theorems). **Division-arc preludes:** `round_round_really_zero` (deep small case), `round_round_zero` (boundary case), `round_round_all_mid_cases` (full dispatcher with 4 user callbacks), `round_round_eq_mid_beta_even` (the bridge — at midpoint with β even, x ∈ F2 directly), `mag_div_disj` helper, `round_round_div_hyp` (5-conjunct precision condition). |
| `IEEE754/Bits.lean` | 900 | `IEEE754/Bits.v` (subset) | **Bit encoding fully proven: 14 + 5 helpers.** Core int encoding: `join_bits`, `split_bits`, `join_bits_range`, `split_join_bits`, `join_split_bits`, `split_bits_inj`. binary_float pack: `bits_of_binary_float`, `bits_of_binary_float_range`, `split_bits_of_binary_float`, `split_bits_of_binary_float_correct`. Decoding: `binary_float_of_bits_aux`, `binary_float_of_bits_aux_correct`, `binary_float_of_bits`. **Round trips:** `binary_float_of_bits_of_binary_float`, `bits_of_binary_float_of_bits`. Helpers: `bpow_radix2_eq`, `Zdigits_radix2_one`, `pow_ew_minus_one_ne_zero`, `subnormal_exp_eq_emin`, `normal_exp_field_bounds`, `bits_of_full_float`, `bits_of_FF2B`. **Deferred:** B32/B64 instantiations (need arithmetic ops). |

**Total: ~678 Lean theorems vs ~480 substantive Coq theorems** (we have extras
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

Core, Calc, all of Prop/{Relative, Sterbenz, Mult_error, Plus_error,
Div_sqrt_error, Round_odd}, the core mid-rounding + multiplication +
mid_cases bridge + entire sqrt arc + entire plus/minus arc (with
FLX/FLT/FTZ instantiations) of Prop/Double_rounding are done. The
remaining work is the division arc + secondary radix tracks of
Double_rounding, the substantial part of `Binary.lean`, and the rest of
`IEEE754/Bits.v`:

1. **Division arc of `Prop/Double_rounding.v`** (~900 Coq lines remaining) —
   the four preludes (`round_round_really_zero`, `round_round_zero`,
   `round_round_all_mid_cases`, `round_round_eq_mid_beta_even`) are done.
   What remains: three aux lemmas (`round_round_div_aux0` ~136 Coq lines,
   `round_round_div_aux1` ~187, `round_round_div_aux2` ~198), the
   dispatcher `round_round_div_aux`, the keystone `round_round_div`, and
   FLX/FLT/FTZ instantiations. **Surprise found 2026-05-12**: the bridge
   itself does NOT use `round_N_odd` — it's purely algebraic
   (`x = rd + (1/2)·β^c1 = rd + n·β^(c1-1)` when `β = 2n`, putting `x` in
   `F2` directly). The round-to-odd dependency kicks in for the aux
   lemmas, presumably to chain through the `round_round_all_mid_cases`
   user callbacks. This is still the biggest remaining Double_rounding
   piece by far.

2. **Plus/minus `radix_ge_3` track** — parallel variant of the plus
   arc with a different hypothesis (`round_round_plus_radix_ge_3_hyp`)
   that uses `≤` instead of `≤ - 1` in three of the four conjuncts.
   Should largely mirror what's done — the aux lemmas follow the same
   skeleton but with different bounds.

3. **Sqrt `radix_ge_4` track** — parallel to plus's `radix_ge_3`, the
   tail of the sqrt section in Coq. Smaller than the plus/minus arc.

4. **Back to `Binary.lean`**: `shr_record` infrastructure (lines 745–925 of
   Binary.v), `binary_round_aux`, then the arithmetic ops (`Bplus`, `Bmult`,
   `Bdiv`, `Bsqrt`), then `Bldexp`, `Bfrexp`, `Bulp`, `Bsucc`, `Bpred`.
   `error_N_FLT` from `Prop/Relative.lean` is the keystone for the
   correctness proofs.

5. **`IEEE754/Bits.v` (remainder)** — beyond the encoding/decoding round-trips
   already proven, there are B32/B64-specific instantiations and helper lemmas.
   Mostly blocked on arithmetic ops in `Binary.lean`.

6. **`Calc/Round.v` cleanup**: add `Zdigits_div_Zpower` to `Digits.lean` to
   unblock the few remaining `generic_format_truncate`/`truncate_correct_format`
   polish points. Mostly nice-to-have.

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

Good luck.
