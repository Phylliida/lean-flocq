# lean-flocq HANDOFF

A working port of [Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) to Lean 4 + Mathlib.
This document is for whoever picks this up next — possibly future-me in a different
session, possibly someone else.

## Status (as of commit `6cd642b`+)

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

**~25308 lines of Lean across 27 files. 0 `sorry`s. All files build clean.**

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
| `Digits.lean` | 206 | (subset of `Core/Digits.v`) | Minimal: `Zdigits` + 10 properties (`_zero`, `_neg`, `_abs`, `_correct`, `_unique`, `_gt_0`, `_ge_0`, `_le_Zpower`, `_div_Zpower`, `_mult_Zpower`). The rest of Coq's `Digits.v` is binary-representation machinery we don't need — `Zdigits := mag` makes the bridge definitional. |
| `Binary.lean` | 3469 | `IEEE754/Binary.v` (lines 1–2440) | **Structural part + shr_record block + IEEE rounding-kernel definitions + `binary_round_aux_correct'` + `binary_round_aux_correct` + `Bmult_correct_aux` + `Bmult` + `Bmult_correct` + `shl_align` + `shl_align_correct` + `snd_shl_align` + `shl_align_fexp` + `shl_align_fexp_correct` + `binary_round` + `binary_round_correct` + `binary_normalize` + `binary_normalize_correct` + `Bplus` + `Bplus_correct` + `Bminus` + `Bminus_correct` + `Bldexp` + `Bldexp_correct` + `Ffrexp_core_binary` + `Bfrexp_correct_aux` + `Bfrexp` + `Bfrexp_correct` + `Bone` + `Bone_correct` + `is_finite_Bone` + `Bsign_Bone` + `Bulp` + `Bulp_correct`.** Still to do: `Bdiv`, `Bsqrt`, `Bsucc`, `Bpred`. `full_float`, `binary_float`, `valid_binary`, `bounded`, `nan_pl`. FF2B/B2FF/B2R round-trips and injectivity. `Bsign`/`is_finite`/`is_nan`. `build_nan`/`erase`/`Bopp`/`Babs`. `Bcompare` (with correctness and swap). Boundedness theorems. `mode` enum, `round_mode`, **`choice_mode`**, **`inbetween_int_valid_round_mode`** (the per-mode dispatch that connects `round_mode m` to `choice_mode m` via the 5 `inbetween_int_*_sign` lemmas from `Calc/Round.lean` — needed by the correctness theorem), `overflow_to_inf`, `binary_overflow`. **`shr_record`** struct + `shr_1` / `loc_of_shr_record` / `shr_record_of_loc` with three round-trip lemmas (`m_shr_record_of_loc`, `loc_of_shr_record_of_loc`, `shr_record_of_loc_m_l`), `shr` iteration function, `shr_1_nonneg` / `shr_1_iter_nonneg` invariants, and **`inbetween_shr_1`**, `inbetween_shr_iter`, **`inbetween_shr`** correctness theorems. **`shr_fexp`** definition + **`shr_truncate`** theorem (connecting `shr_fexp` to `truncate` from `Calc/Round.lean`). **`binary_round_aux`** definition (IEEE-754 rounding kernel: two `shr_fexp` calls bracketing a `choice_mode` rounding, then zero/finite/overflow classification). Still to do: `binary_round_aux_correct'` correctness theorem (Coq lines 974–1154, ~180 lines) and downstream arithmetic ops (`Bplus`, `Bmult`, `Bdiv`, `Bsqrt`, auxiliary ops). |
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
| `Prop/Double_rounding.lean` | 4885 | `Prop/Double_rounding.v` (~95% by lines) | **Core mid-rounding + multiplication + bridge + full sqrt arc + sqrt radix_ge_4 + full plus/minus arc + plus/minus radix_ge_3 + full division arc.** Definitions: `round_round_eq`, `midp`, `midp'`. **`_lt_mid` family:** `_further_place'`, `_further_place`, `_same_place`, `_lt_mid` dispatcher. **`_gt_mid` family:** `_further_place'`, `_further_place` (with the `x'' = bpow(mag x)` edge case via `round_generic` + `Znearest_imp`), `_same_place`, `_gt_mid` dispatcher. **Multiplication arc:** `round_round_mult_hyp`, `round_round_mult_aux`, `round_round_mult`, `round_round_mult_FLX/_FLT/_FTZ`. **Bridge:** `round_round_mid_cases`. **Sqrt arc:** `round_round_sqrt_hyp`, `mag_sqrt_disj`, `bpow_neg_two_le_quarter`, `round_round_sqrt_aux` (300-line keystone), `round_round_sqrt` + FLX/FLT/FTZ. **Plus/minus arc:** `round_round_plus_hyp` (4-conjunct precision condition), six mag helpers, plus/minus aux families, **`round_round_plus`** and **`round_round_minus`** keystones, plus FLX/FLT/FTZ instantiations. **Division arc complete:** `round_round_really_zero`, `round_round_zero`, `round_round_all_mid_cases` (4-callback dispatcher), `round_round_eq_mid_beta_even` (bridge for β even), `mag_div_disj`, `round_round_div_hyp` (5-conjunct precision), **`round_round_div_aux0/1/2`** (the three case-split preludes — boundary/below-midpoint/above-midpoint), **`round_round_div_aux`** dispatcher, **`round_round_div`** keystone (with sign dispatch via `round_N_opp` for negative x or y), FLX/FLT/FTZ instantiations (3 hyp lemmas + 3 user theorems). **Sqrt radix_ge_4 arc:** `bpow_neg_one_le_quarter_of_beta_ge_4` helper, `round_round_sqrt_radix_ge_4_hyp`, `_aux`, `_radix_ge_4` keystone, FLX/FLT/FTZ — the regular sqrt aux with `-2 → -1` throughout, needing `4 ≤ beta`. **Plus/minus radix_ge_3 arc:** `bpow_neg_one_le_third_of_beta_ge_3` helper, `round_round_plus_radix_ge_3_hyp`, plus chain (aux0/aux1/aux2/aux), minus chain (aux0/aux1/aux2/aux3/aux), plus/minus keystones with sign dispatch, FLX/FLT/FTZ for both — needs `3 ≤ beta`, uses `bpow(-1) ≤ 1/3`. |
| `IEEE754/Bits.lean` | 900 | `IEEE754/Bits.v` (subset) | **Bit encoding fully proven: 14 + 5 helpers.** Core int encoding: `join_bits`, `split_bits`, `join_bits_range`, `split_join_bits`, `join_split_bits`, `split_bits_inj`. binary_float pack: `bits_of_binary_float`, `bits_of_binary_float_range`, `split_bits_of_binary_float`, `split_bits_of_binary_float_correct`. Decoding: `binary_float_of_bits_aux`, `binary_float_of_bits_aux_correct`, `binary_float_of_bits`. **Round trips:** `binary_float_of_bits_of_binary_float`, `bits_of_binary_float_of_bits`. Helpers: `bpow_radix2_eq`, `Zdigits_radix2_one`, `pow_ew_minus_one_ne_zero`, `subnormal_exp_eq_emin`, `normal_exp_field_bounds`, `bits_of_full_float`, `bits_of_FF2B`. **Deferred:** B32/B64 instantiations (need arithmetic ops). |

**Total: ~720 Lean theorems vs ~480 substantive Coq theorems** (we have extras
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
Div_sqrt_error, Round_odd}, and Prop/Double_rounding (core mid-rounding +
multiplication + mid_cases bridge + sqrt arc + sqrt radix_ge_4 + plus/minus
arc + plus/minus radix_ge_3 + division arc, all with FLX/FLT/FTZ
instantiations) are done. The remaining work is the substantial part of
`Binary.lean` and the rest of `IEEE754/Bits.v`:

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
   `ulp(B2R x) = bpow(cexp(B2R x))` since `B2R x ≠ 0`. Next:
   `Bsucc`, `Bpred`. Also `Bdiv`, `Bsqrt` as the larger remaining
   arithmetic ops.
   Dependencies: `round_trunc_sign_any_correct'`, `truncate_correct_partial'`,
   `truncate_correct_format`, `truncate_0`, `cexp_round_ge` — all in
   `Calc/Round.lean` and `Generic_fmt.lean`. Then the arithmetic ops
   (`Bplus`, `Bmult`, `Bdiv`, `Bsqrt`), then `Bldexp`, `Bfrexp`, `Bulp`,
   `Bsucc`, `Bpred`. `error_N_FLT` from `Prop/Relative.lean` is the
   keystone for those downstream correctness proofs.

2. **`IEEE754/Bits.v` (remainder)** — beyond the encoding/decoding round-trips
   already proven, there are B32/B64-specific instantiations and helper lemmas.
   Mostly blocked on arithmetic ops in `Binary.lean`.

3. **`Calc/Round.v` cleanup**: add `Zdigits_div_Zpower` to `Digits.lean` to
   unblock the few remaining `generic_format_truncate`/`truncate_correct_format`
   polish points. Mostly nice-to-have.

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
