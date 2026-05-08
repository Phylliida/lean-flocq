# lean-flocq HANDOFF

A working port of [Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) to Lean 4 + Mathlib.
This document is for whoever picks this up next — possibly future-me in a different
session, possibly someone else.

## Status (as of commit `f957264`)

~5950 lines of Lean across 12 files. **0 `sorry`s.** All files build clean.
Foundational + all four classical concrete formats + substantial Ulp + Round_NE skeleton:

| File | Lean lines | Coq source | Status |
|------|-----------|------------|--------|
| `Zaux.lean` | 34 | `Core/Zaux.v` | Minimal: just `radix`. More integer lemmas on demand. |
| `Raux.lean` | 313 | `Core/Raux.v` | `bpow`, `Ztrunc`, `Zaway`, `mag` + their key properties. |
| `Defs.lean` | 62 | `Core/Defs.v` | **Complete.** All 11 definitions. |
| `Float_prop.lean` | 247 | `Core/Float_prop.v` | Algebraic lemmas + bpow-bound family. Skipped: `Rcompare_F2R`, `F2R_cond_Zopp`, `F2R_prec_normalize`, `mag_*` family. |
| `Round_pred.lean` | 819 | `Core/Round_pred.v` | **Essentially complete** (every theorem ported except `Rnd_N_pt_DN_UP_eq` variants — see file header). |
| `Generic_fmt.lean` | 1921 | `Core/Generic_fmt.v` | ~91 theorems. **All deferred items closed**: `Znearest_opp`, `round_N_opp`, `generic_round_generic` are now done. |
| `FIX.lean` | 85 | `Core/FIX.v` | **Complete**: 7 thms incl. `ulp_FIX`. |
| `FLX.lean` | 174 | `Core/FLX.v` | Core + `negligible_exp_FLX`, `ulp_FLX_0`, `generic_format_FLX_1`, `eq_0_round_0_FLX`, `gt_0_round_gt_0_FLX`. Skipped: `FLXN_format`, `succ_FLX_*`, `Round_NE.v`-dependent. |
| `FLT.lean` | 330 | `Core/FLT.v` | Core + `ulp_FLT_small/_le/_gt`, `generic_format_FLT_1`. Skipped: `succ_FLT_exact_shift_*` (need `mag_mult_bpow`), `Round_NE.v`-dependent. |
| `FTZ.lean` | 393 | `Core/FTZ.v` | 10 thms incl. `ulp_FTZ_0`. Skipped: `FTZ_format_FLXN`. |
| `Ulp.lean` | 1456 | `Core/Ulp.v` (slice) | Substantial: 69 thms (~67% of Coq's 103). All foundational pieces plus: ulp_DN, succ_DN_eq_UP_pos, ulp_succ_pos, generic_format_ulp + not_FTZ_generic_format_ulp + generic_format_bpow_ge_ulp_0 + not_FTZ_ulp_ge_ulp_0 (the triple equivalence with Exp_not_FTZ). Pending: x = 0 case of round_UP_plus_eps_pos, mixed-sign round_DN_plus_eps / round_UP_plus_eps families, ulp_round / ulp_round_pos, ulp_pred_pos, ulp_ulp_0, full succ_DN_eq_UP. |
| `Round_NE.lean` | 42 | `Core/Round_NE.v` | Foundations: `ZnearestE`, `round_NE`, `NE_prop`, `Rnd_NE_pt`, `round_NE_pt_N`. Skipped (the parity argument): `DN_UP_parity_generic_pos`, `Rnd_NE_pt_total/_monotone`, `round_NE_pt`. |

## Build setup

- **Toolchain**: `leanprover/lean4:v4.25.0` (pinned in `lean-toolchain`).
- **Mathlib**: `git#v4.25.0` via `lakefile.toml`.
- **First-time build**: `lake exe cache get` to fetch the Mathlib build cache,
  then `lake build`. Without the cache, first build is slow (Mathlib compilation
  takes >30 min). With cache, it's ~2 min.
- **Incremental rebuilds**: `lake build` typically rebuilds just the changed
  Lean files in seconds.

```bash
cd lean-flocq
lake exe cache get      # only needed once or after `lake update`
lake build              # rebuilds; show errors if any
```

## File-by-file status

### `Zaux.lean`
Just `radix` (`structure radix where val : ℤ; prop : 2 ≤ val`), `radix_gt_0`,
`radix_gt_1`, `radix2`. The bulk of Coq's Zaux.v (auxiliary integer lemmas)
hasn't been needed yet; port on demand.

### `Raux.lean`
- `bpow beta e = (beta.val : ℝ) ^ e` — `noncomputable` because of zpow.
- `bpow_gt_0/ge_0/ne_0`, `bpow_zero`, `bpow_one`, `bpow_plus` (additivity),
  `bpow_le/lt/le_bpow/lt_bpow` (monotonicity), `IZR_Zpower` (cast bridge).
- **`Ztrunc`** = `if x < 0 then ⌈x⌉ else ⌊x⌋`. Theorems: `_intCast`, `_floor`
  (for `0 ≤ x`), `_ceil`, `_opp`, `_abs`, `_le`.
- **`Zaway`** = `if x < 0 then ⌊x⌋ else ⌈x⌉`. Same shape: `_intCast`, `_le`, `_opp`.
- **`mag`** = `if x = 0 then 0 else Int.log beta.val.toNat |x| + 1`.
  Theorems: `_zero`, `_opp`, `_abs`, `_unique`, `_unique_pos`, `_bpow`,
  `bpow_mag_gt`, `bpow_mag_le`, `_le_bpow`, `_gt_bpow`, `_ge_bpow`, `_le_abs`.

### `Defs.lean`
All 11 Coq definitions ported faithfully. `float`, `F2R`, `round_pred_*`,
`Rnd_DN_pt`, `Rnd_UP_pt`, `Rnd_ZR_pt`, `Rnd_N_pt`, `Rnd_NG_pt`, `Rnd_NA_pt`.

### `Float_prop.lean`
- Comparison: `F2R_le/lt/eq`, `le_F2R/lt_F2R/eq_F2R`.
- Negation/abs: `F2R_Zopp`, `F2R_Zabs`.
- Sign: `F2R_0`, `eq_0_F2R`, `ge_0_F2R/le_0_F2R/gt_0_F2R/lt_0_F2R`,
  `F2R_ge_0/le_0/gt_0/lt_0`, `F2R_neq_0`, `Fnum_ge_0/le_0`.
- bpow bounds: `F2R_bpow`, `bpow_le_F2R`, `F2R_change_exp`, `F2R_p1_le_bpow`,
  `bpow_le_F2R_m1`, `F2R_lt_bpow`.

**One documented deviation**: `F2R_lt_bpow` is *strictly stronger* than Coq's
because Lean's `(beta.val : ℤ) ^ (e' - f.Fexp).toNat` evaluates to 1 (not 0)
when `e' < f.Fexp`. The docstring on the theorem flags this. See the
`Stronger Is Not Faithful` poem in `POEMS.md` for the story.

### `Round_pred.lean`
Essentially complete. Notable contents:
- Function-level rounding: `Rnd_DN/UP/ZR/N/NG/NA`.
- Existence/uniqueness: `round_val_of_pred`, `round_fun_of_pred` (via
  `Classical.choose` — Coq uses real-number completeness, choice is enough).
- DN/UP family: monotone, unique, refl, idempotent, opp.
- N family: `_DN_or_UP`, `_DN_or_UP_eq`, `_opp_inv`, `_refl`, `_idempotent`, `_0`,
  **`_monotone`**, **`_unique`** (the hard ones), `_ge_0/le_0/abs`.
- ZR: `_abs`, `_pt_monotone`.
- NG: `_pt_unique_prop`, `_pt_unique`, `_pt_monotone`, `_pt_refl`, `_pt_opp_inv`.
- NA: `Rnd_NA_NG_pt` (the iff bridge), `_pt_unique_prop`, `_pt_unique`,
  `_pt_monotone`, `_pt_refl`, `_pt_idempotent`, `_pt_N`, `_unique`.
- Equiv format / round_pred_*_0.
- **`satisfies_any`** family: structure + `_eq` + `_imp_DN/UP/ZR/NG/NA`. The
  `_imp_NG` proof is ~50 lines (Coq's was 140; ours is shorter because we'd
  proved `Rnd_N_pt_DN_UP` and `Rnd_N_pt_DN_or_UP_eq` earlier).

### `Generic_fmt.lean`
~88 theorems. Major sections:
- **Foundations**: `Valid_exp`, `cexp`, `canonical`, `scaled_mantissa`,
  `generic_format`. `valid_exp_large/_large'`. Format basics: `_0`, `_bpow/_bpow'`,
  `_F2R/_F2R'`, `_opp/_abs/_abs_inv`, `_canonical`, `_discrete`, `_ge_bpow`,
  `_bpow_inv/_inv'`. Canonical: `_opp/_abs/_0/_unique/_generic_format`.
  Scaled mantissa: `_generic/_mult_bpow/_0/_opp/_abs/_lt_1`.
  cexp: `_opp/_abs/_fexp/_fexp_pos`. Subnormal: `mantissa_small_pos`,
  `mantissa_DN_small_pos`, `mantissa_UP_small_pos`, `mag_generic_gt`,
  `abs_lt_bpow_prec`.
- **Round machinery**: `Valid_rnd` class, `round` def, `round_0`,
  `Zrnd_DN_or_UP`, `Zrnd_ZR_or_AW`, `round_generic`, `round_ext`,
  `round_bounded_large_pos/_small_pos`, `exp_small_round_0_pos`,
  `generic_format_round_pos`, `round_le_pos`, `Zrnd_opp` + `valid_rnd_opp`,
  `round_opp`, **`valid_rnd_DN/UP/ZR/AW`** instances, `round_DN_or_UP`,
  `round_ZR_or_AW`, `round_le`, `round_ge_generic/_le_generic`,
  `round_DN_opp/UP_opp`, `generic_format_round`, `round_DN_pt/UP_pt/ZR_pt`,
  **`generic_format_satisfies_any`** (bridge to Round_pred).
- **Extended round**: `round_abs_abs`, `round_bounded_large`,
  `exp_small_round_0`, `round_ZR/AW_opp/_DN/_UP/_abs`,
  `round_DN/UP_small_pos`, `round_DN_UP_lt`, `generic_format_EM`,
  `generic_N_pt_DN_or_UP`.
- **Magnitude**: `round_large_pos_ge_bpow`, `mag_round_ZR`, `mag_DN`,
  `cexp_DN`, `scaled_mantissa_DN`, `mag_round`.
- **Znearest**: def, `_DN_or_UP`, `_ge_floor/_le_ceil`, `valid_rnd_N` instance,
  `_N_strict`, `_half`, `_imp`, **`round_N_pt`** (Znearest as abstract Rnd_N_pt),
  `round_N_middle`, **`round_NA_pt`**, `round_N_small_pos`, `round_N_small`.
- **Monotone_exp**: def, `cexp_le_bpow/_ge_bpow`, `mag_round_ge`, `cexp_round_ge`.
- **Inclusion**: `generic_inclusion_mag/_lt_ge/_/_ge/_le/_le_ge`.

## The two architectural bridges

These are the keystones that connect the concrete (Generic_fmt) to the
abstract (Round_pred). Once they exist, much of Round_pred becomes usable
for any valid generic format:

1. **`generic_format_satisfies_any`** (Round_pred → Generic_fmt direction):
   any valid generic format is a `satisfies_any` instance — it has 0,
   is closed under negation, and admits a total round-down. This unlocks
   all `satisfies_any_imp_*` results for any concrete format.

2. **`round_N_pt`** (Generic_fmt → Round_pred direction): the value
   `round β fexp (Znearest choice) x` is a `Rnd_N_pt` of the format.
   Combined with `valid_rnd_N`, every `Rnd_N_pt` theorem in Round_pred
   automatically applies to Znearest-rounded values.

## Translation patterns and gotchas

### Imports
- `Mathlib.Algebra.Order.Floor` is deprecated; use `.Ring` and `.Semiring` subdirs.
- `Mathlib.Data.Int.Defs` doesn't exist; use `Mathlib.Data.Int.Init`.
- `Mathlib.Tactic.NormCast` doesn't exist as a module; `push_cast`/`norm_cast`
  come from core Lean's `Init.Tactics`.
- `FloorRing ℝ` instance lives in `Mathlib.Data.Real.Archimedean`.

### Mathlib lemma name shifts (Lean v4.25.0)
- `mul_lt_mul_right` → `mul_lt_mul_iff_of_pos_right`
- `le_or_lt` → `le_or_gt`
- `lt_or_le` → `lt_or_ge`
- `abs_add` → `abs_add_le`

### `bpow` and `Zpower` differ at negative exponents
Coq's `Zpower beta n` returns 0 for `n < 0`. Lean's `(beta.val : ℤ) ^ n.toNat`
returns 1 (since `.toNat = 0`). For theorems whose Coq hypothesis becomes
vacuous at negative exponents, the Lean versions are *stronger* — they accept
the additional `m = 0` case. This is documented on `F2R_lt_bpow`.

### `rw [hxm]` substitutes globally
If `hxm : x = ...` and you write `rw [hxm]`, Lean replaces *every* `x` in the
goal — including ones inside `scaled_mantissa beta fexp x`, `cexp beta fexp x`,
`(e - x').toNat`, etc. This often breaks proofs because the inner `x`s were
needed. Workarounds:
- Use `set sm := scaled_mantissa beta fexp x` (and similar) *before* the rewrite.
- Use a scoped `have h_split : ... = ...` instead of `rw`.
- Use `conv_lhs` / `conv_rhs` to target the rewrite.
- Or just prove the equality you want directly without going through `rw [hxm]`.

### `(↑n.toNat).toNat` and zpow ↔ npow
After `rw [show (n : ℤ) = ((n.toNat : ℕ) : ℤ) from htn.symm, zpow_natCast]`,
you get a residual `(↑n.toNat).toNat`. Use `Int.toNat_natCast` or `norm_cast`
to clean up. Or use the pattern in `IZR_Zpower`:
```lean
unfold bpow
push_cast
rw [show n = ((n.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hn).symm,
    zpow_natCast, Int.toNat_natCast]
```

### Bool-valued ifs and `decide`
`Znearest` has `if (choice ⌊x⌋ : Bool) then ... else ...` where `choice : ℤ → Bool`.
When the choice is `fun n => decide (0 ≤ n)`, `simp [decide_eq_true_eq.mpr h]` is
fragile (if-cascade may not collapse). `split_ifs with h` is more robust — gives
you both branches, and you can use `decide_eq_true_eq` on `h` to convert to the
Prop level.

### Equality of structures and `congr 1`
`F2R ⟨m1, e⟩ = F2R ⟨m2, e⟩` reduces (via `F2R_eq` / `congr 1`) to `m1 = m2`.
For Lean's `congr 1` to step into the structure, the exponents must already
match syntactically. Use `F2R_change_exp` or explicit unfolding when they don't.

### `rfl` sometimes closes goals after `rw`
When `rw` produces a goal that's definitionally true (e.g., `e + -k = e - k` for
integers, since `Int.sub a b = a + -b`), `rw` closes it automatically. If you
follow `rw` with `congr 1; ring`, you get "No goals to be solved" because the
goal is already closed. Either drop the trailing tactic or use `try`.

### Useful Mathlib API for this corpus
- `Int.floor`, `Int.ceil`, `Int.floor_le`, `Int.le_ceil`, `Int.floor_le_floor`,
  `Int.ceil_le_ceil`, `Int.floor_intCast`, `Int.ceil_intCast`, `Int.floor_neg`,
  `Int.ceil_neg`, `Int.ceil_le_floor_add_one`, `Int.floor_eq_iff`, `Int.ceil_eq_iff`,
  `Int.floor_lt`, `Int.le_floor`, `Int.floor_nonneg`, `Int.ceil_nonneg`.
- `Int.log` (in `Mathlib.Data.Int.Log`), `Int.zpow_log_le_self`,
  `Int.lt_zpow_succ_log_self`, `Int.zpow_le_iff_le_log`, `Int.lt_zpow_iff_log_lt`.
- `zpow_pos`, `zpow_le_zpow_right₀`, `zpow_lt_zpow_right₀`, `zpow_add₀`,
  `zpow_natCast`, `zpow_neg`, `zpow_one`.
- `abs_of_nonneg`, `abs_of_nonpos`, `abs_of_neg`, `abs_of_pos`, `abs_neg`,
  `abs_zero`, `abs_pos`, `abs_nonneg`, `abs_eq_abs`, `abs_nonpos_iff`,
  `abs_sub_comm`, `abs_lt`, `abs_add_le`, `abs_mul`.
- `mul_le_mul_of_nonneg_right`, `mul_lt_mul_of_pos_right`,
  `mul_lt_mul_iff_of_pos_right`, `mul_nonneg`, `mul_nonpos_of_nonpos_of_nonneg`,
  `mul_pos`, `mul_neg_of_neg_of_pos`, `mul_right_cancel₀`.
- `Classical.choose` / `Classical.choose_spec` for going from `∃` to a witness.

### `linarith` and `omega`
- `omega` handles linear integer arithmetic (and `Nat.cast`/`Int.toNat`).
  Use it for any goal involving only `≤`/`<`/`=` on `ℤ`/`ℕ`.
- `linarith` handles linear real arithmetic. It treats multiplications by
  variables as opaque, so `(a - b) * c` won't be seen as `a*c - b*c` unless
  you pre-distribute via `ring_nf` or equivalent.
- `nlinarith` allows some non-linear reasoning. Try it when `linarith` fails.

### Gotcha: Lean's `noncomputable`
`bpow`, `mag`, `Ztrunc`, `Zaway`, `Znearest`, `cexp`, `scaled_mantissa`,
`generic_format`, `round`, `Zrnd_opp` are all `noncomputable def`. Anything
involving real-number ⌊·⌋/⌈·⌉ requires it. The whole library is fine without
runtime computation.

## Suggested next steps

In rough order of usefulness:

1. **DN_UP parity in `Round_NE.lean`** — show `round_DN x` and `round_UP x`
   have opposite-parity canonical mantissas. This is the *keystone* needed
   for `Rnd_NE_pt_total/monotone` and `round_NE_pt`. Substantial proof
   (Coq's is ~150 lines, with separate small/large-x cases).

2. **More of `Core/Ulp.v`** — `ulp_le_pos`, `ulp_le`, `eq_0_round_0_negligible_exp`,
   the `succ_lt_le_aux` lemmas, `succ_FLT_*`, `ulp_FLT_*`, etc.
   ~2000 lines remaining; mostly format-specific instantiations.

4. **`Core/IEEE754/Binary.v`** — the actual IEEE 754 binary formats.
   The destination of this whole port. Will need full Ulp and Round_NE.

5. **`FLXN_format`** in `FLX.lean` — the normalized FLX variant. Small
   but useful for some FTZ↔FLX bridges (`FTZ_format_FLXN`). Skipped to
   keep FLX.lean trim.

6. **Skipped `Float_prop.v` lemmas**: `Rcompare_F2R` (needs `Rcompare`),
   `F2R_cond_Zopp` (needs `cond_Zopp`), `F2R_prec_normalize`, the `mag_*`
   family (`mag_F2R`, `mag_le_Zpower`, etc., would unblock cleaner FLT/FLX
   proofs and `FIX_format_FLX` which we skipped).

## Useful commands

```bash
# Build
lake build

# Build just one file
lake build LeanFlocq.Core.Generic_fmt

# Check whether a definition exists in Mathlib (can save lookup time)
grep -rn "theorem foo_bar\|def foo_bar" \
  .lake/packages/mathlib/Mathlib/ | head

# After modifying a theorem, see if the build broke
lake build 2>&1 | grep -E "error|✖|warning|Built LeanFlocq" | head

# Find all occurrences of a Lean theorem name across the project
grep -rn "theorem_name" LeanFlocq/

# Check the Coq source for a theorem we want to port
grep -n "Theorem foo\|Lemma foo" ../flocq/src/Core/*.v
```

## Files in this repo

- `lakefile.toml` / `lean-toolchain` — build config.
- `LeanFlocq.lean` — top-level module, just imports the rest.
- `LeanFlocq/Core/*.lean` — the actual port.
- `POEMS.md` — six poems written during the port. They mark moments
  where something shifted: a debugging insight, a code-review correction,
  the bridge moment, the satisfaction of round preserving order, the
  shape of the day. They're not ornamental — they're how the work got paced.
- `HANDOFF.md` — this document.
- `.gitignore` — ignores `.lake/`.

## A note on rhythm

If you're picking this up: the work goes faster when you alternate. Build a
bit, commit, build a bit more. Don't try to land four theorems at once —
each commit should compile clean. The `0 sorries throughout` in the commit
log is from this discipline, and it's worth keeping.

When you hit something genuinely hard (`valid_rnd_N`, `round_N_pt`,
`Rnd_NA_NG_pt`), the right move is usually: lift helper lemmas out, prove
each as its own `private theorem`, then the main theorem becomes a clean
composition. The substantial proofs in this port are typically <100 lines
because of this — each helper hides a case split.

Good luck.
