# lean-flocq HANDOFF

A working port of [Flocq](https://flocq.gitlabpages.inria.fr/) (Coq) to Lean 4 + Mathlib.
This document is for whoever picks this up next — possibly future-me in a different
session, possibly someone else.

## Status (as of commit `b438cd6`)

**~6325 lines of Lean across 12 files. 0 `sorry`s. All files build clean.**

Foundational layer + all four classical concrete formats + substantial Ulp
(~85% of Coq's Ulp.v) + Round_NE skeleton.

| File | Lean lines | Coq source | Status |
|------|-----------|------------|--------|
| `Zaux.lean` | 34 | `Core/Zaux.v` | Minimal: just `radix`. More integer lemmas on demand. |
| `Raux.lean` | 333 | `Core/Raux.v` | `bpow`, `Ztrunc`, `Zaway`, `mag` + key properties + `mag_mult_bpow`, `mag_1`. |
| `Defs.lean` | 62 | `Core/Defs.v` | **Complete.** All 11 definitions. |
| `Float_prop.lean` | 247 | `Core/Float_prop.v` | Algebraic + bpow-bound family. Skipped: `Rcompare_F2R`, `F2R_cond_Zopp`, `F2R_prec_normalize`, the `mag_*` family (`mag_F2R`, `mag_le_Zpower`). |
| `Round_pred.lean` | 819 | `Core/Round_pred.v` | **Essentially complete.** Every theorem ported except `Rnd_N_pt_DN_UP_eq` variants. |
| `Generic_fmt.lean` | 1921 | `Core/Generic_fmt.v` | **~91 theorems.** All foundational pieces + `Znearest_opp` / `round_N_opp` / `generic_round_generic` (was deferred — now done). |
| `FIX.lean` | 85 | `Core/FIX.v` | **Complete** (modulo Ulp): 7 thms incl. `ulp_FIX`. |
| `FLX.lean` | 174 | `Core/FLX.v` | Core + `negligible_exp_FLX`, `ulp_FLX_0`, `ulp_FLX_1`, `succ_FLX_1`, `ulp_FLX_exact_shift`, `generic_format_FLX_1`, `eq_0_round_0_FLX`, `gt_0_round_gt_0_FLX`. Skipped: `FLXN_format`. |
| `FLT.lean` | 330 | `Core/FLT.v` | Core + `ulp_FLT_small/_le/_gt`, `ulp_FLT_exact_shift`, `generic_format_FLT_1`. Skipped: `succ_FLT_exact_shift_*`. |
| `FTZ.lean` | 393 | `Core/FTZ.v` | 10 thms incl. `ulp_FTZ_0`. Skipped: `FTZ_format_FLXN`. |
| `Ulp.lean` | 1829 | `Core/Ulp.v` (slice) | **88 theorems (~85% of Coq's 103).** See section below. |
| `Round_NE.lean` | 42 | `Core/Round_NE.v` | Foundations: `ZnearestE`, `round_NE`, `NE_prop`, `Rnd_NE_pt`, `round_NE_pt_N`. Skipped: the parity argument. |

## What's in `Ulp.lean`

Substantial — roughly 85% of Coq's Ulp.v. Organized in clusters:

### Foundations
- `negligible_exp` (via `Classical.choose`), `negligible_exp_some`/`_none`, `fexp_negligible_exp_eq`.
- `ulp` def with the if-zero fallback. `ulp_neq_0`, `ulp_opp`, `ulp_abs`, `ulp_ge_0`, `ulp_bpow`.
- `ulp_le_id`, `ulp_le_abs`.
- `round_UP_DN_ulp` (the keystone: `round_UP x = round_DN x + ulp x` for `x ∉ F`).

### Step structure (succ / pred)
- Definitions: `pred_pos`, `succ`, `pred`. Basic equalities: `pred_eq_pos`, `succ_eq_pos`, `succ_opp`, `pred_opp`.
- Bound bridges: `id_p_ulp_le_bpow`, `id_m_ulp_ge_bpow`.
- Format-preservation: `generic_format_ulp_0`, `generic_format_succ_aux1`, `generic_format_pred_aux1`, `generic_format_pred_aux2`, `generic_format_pred_pos`, **`generic_format_succ` / `generic_format_pred`** (full).
- Order: `pred_pos_lt_id`, `succ_gt_id`, `pred_lt_id`, `succ_ge_id`, `pred_le_id`, `pred_pos_ge_0`, `pred_ge_0`. Lifted: `succ_gt_ge`, `pred_lt_le`. At zero: `succ_0`, `pred_0`, `pred_ulp_0`.
- The roundtrip: `pred_pos_plus_ulp_aux1/2/3`, **`pred_pos_plus_ulp` / `pred_plus_ulp`**.
- Inverse pair: `succ_pred_pos`, `pred_succ_pos`, **`succ_pred` / `pred_succ`** (full).
- Monotonicity: **`succ_le` / `pred_le` / `succ_lt` / `pred_lt`** — succ and pred are strictly order-preserving on F.

### Equivalences for `Exp_not_FTZ`
- `Exp_not_FTZ` def, `monotone_exp_not_FTZ`, `ulp_ge_ulp_0`.
- `ulp_le_pos`, `ulp_le` (ulp monotone under |·|).
- The triple equivalence: `Exp_not_FTZ ↔ ∀ x, ulp x ∈ F ↔ ∀ x, ulp 0 ≤ ulp x`. Bridges: `generic_format_ulp`, `not_FTZ_generic_format_ulp`, `generic_format_bpow_ge_ulp_0`, `not_FTZ_ulp_ge_ulp_0`.

### Round / ulp interaction
- `ulp_DN`, `ulp_succ_pos`, `ulp_ulp_0`.
- **`succ_DN_eq_UP`** (general), `succ_DN_eq_UP_pos`, `pred_UP_eq_DN`, `pred_UP_le_DN`, `UP_le_succ_DN`.
- **`ulp_round_pos`**, **`ulp_round`** (the keystones).
- Cross-rounding: `round_UP_le_DN_lt`, `round_DN_ge_UP_gt`.
- `round_DN_eq`, `round_UP_eq` (uniqueness characterizations via succ/pred).

### Perturbation
- `mag_plus_eps`, `round_DN_plus_eps_pos` (incl. `x = 0`), `round_UP_plus_eps_pos` (positive only), `round_DN_minus_eps_pos`.
- `succ_le_lt_aux`, **`succ_le_lt`** (full), **`pred_ge_gt`**, `le_pred_pos_lt`.

### Error bounds
- `error_lt_ulp`, `error_le_ulp`, `error_le_half_ulp`.
- `eq_0_round_0_negligible_exp`, `round_neq_0_negligible_exp`, `abs_round_ge_generic`.
- **`error_lt_ulp_round`**, **`error_le_ulp_round`**, **`error_le_half_ulp_round`** — the IEEE-style relative error bounds, where the bound is `ulp(round x)` rather than `ulp x`.

### Pending
- `x = 0` case of `round_UP_plus_eps_pos`.
- Mixed-sign perturbation: `round_DN_plus_eps`, `round_UP_plus_eps`, `round_DN_minus_eps`, `round_UP_pred_plus_eps_pos` / `round_UP_pred_plus_eps`.
- `succ_le_inv` / `pred_le_inv` (inverse monotonicity).
- The `round_N_le_midp` / `round_N_eq_DN` / `round_N_eq_UP` family.
- `succ_le_plus_ulp`, `generic_format_plus_ulp`.

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

## The two architectural bridges

These connect concrete `Generic_fmt` to abstract `Round_pred`. Once they exist, much of `Round_pred` becomes usable for any valid generic format:

1. **`generic_format_satisfies_any`** (`Generic_fmt → Round_pred`): any valid generic format is a `satisfies_any` instance. Unlocks all `satisfies_any_imp_*` results for any concrete format.

2. **`round_N_pt`** (`Generic_fmt → Round_pred`): `round β fexp (Znearest choice) x` is a `Rnd_N_pt` of the format. Combined with `valid_rnd_N`, every `Rnd_N_pt` theorem applies to Znearest-rounded values.

## Translation patterns and gotchas

### Imports

- `Mathlib.Algebra.Order.Floor` is deprecated; use `.Ring` and `.Semiring` subdirs.
- `Mathlib.Data.Int.Defs` doesn't exist; use `Mathlib.Data.Int.Init`.
- `Mathlib.Tactic.NormCast` doesn't exist as a module; `push_cast`/`norm_cast` come from core Lean's `Init.Tactics`.
- `FloorRing ℝ` instance lives in `Mathlib.Data.Real.Archimedean`.

### Mathlib lemma name shifts (Lean v4.25.0)

- `mul_lt_mul_right` → `mul_lt_mul_iff_of_pos_right`
- `le_or_lt` → `le_or_gt`
- `lt_or_le` → `lt_or_ge`
- `abs_add` → `abs_add_le`

### `bpow` and `Zpower` differ at negative exponents

Coq's `Zpower beta n` returns `0` for `n < 0`. Lean's `(beta.val : ℤ) ^ n.toNat` returns `1` (since `.toNat = 0`). For theorems whose Coq hypothesis becomes vacuous at negative exponents, the Lean versions are *stronger* — they accept the additional `m = 0` case. Documented on `F2R_lt_bpow`.

### `rw [hxm]` substitutes globally — multiple variants

This trap appears in **many forms**. Document it once, recognize it everywhere.

**Form 1:** `hxm : x = ...`. `rw [hxm]` substitutes every `x` in the goal — including `x` inside `⌊x⌋`, `cexp beta fexp x`, `scaled_mantissa beta fexp x`, etc. Workarounds:
- `set sm := scaled_mantissa beta fexp x` *before* the rewrite.
- `conv_lhs` / `conv_rhs` to scope.
- A scoped `have` instead of `rw`.

**Form 2:** `rw [ulp_neq_0]` is bad when the goal has both `ulp x` standalone *and* `ulp x` inside a `cexp` argument: it rewrites all of them, leaving you with `cexp(x - bpow(cexp x))` instead of the cleaner `cexp(x - ulp x)`.

The reliable fix is the **calc pattern**:

```lean
calc ulp beta fexp (x - ulp beta fexp x)
    = bpow beta (cexp beta fexp (x - ulp beta fexp x)) :=
      ulp_neq_0 beta fexp h_ne
  _ = bpow beta (cexp beta fexp x) := by congr 1; unfold cexp; rw [h_mag]
  _ = ulp beta fexp x := (ulp_neq_0 beta fexp h_x_ne).symm
```

This shows up in `pred_pos_plus_ulp_aux1`, `ulp_succ_pos`, `pred_pos_plus_ulp`. If you find yourself fighting `rw [ulp_neq_0]`, rewrite as a calc.

### `(↑n.toNat).toNat` and zpow ↔ npow

After `rw [show (n : ℤ) = ((n.toNat : ℕ) : ℤ) from htn.symm, zpow_natCast]`, you get a residual `(↑n.toNat).toNat`. Use `Int.toNat_natCast` or `norm_cast`. Or use the `IZR_Zpower` pattern:

```lean
unfold bpow
push_cast
rw [show n = ((n.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hn).symm,
    zpow_natCast, Int.toNat_natCast]
```

### Bool-valued ifs and `decide`

`Znearest` has `if (choice ⌊x⌋ : Bool) then ... else ...`. When the choice is `fun n => decide (0 ≤ n)`, `simp [decide_eq_true_eq.mpr h]` is fragile (the if-cascade may not collapse). `split_ifs with h` is more robust — gives both branches, and `decide_eq_true_eq` converts `h` to the Prop level.

### Equality of structures and `congr 1`

`F2R ⟨m1, e⟩ = F2R ⟨m2, e⟩` reduces (via `F2R_eq` / `congr 1`) to `m1 = m2`. For `congr 1` to step into the structure, the exponents must match syntactically. Use `F2R_change_exp` or explicit unfolding when they don't.

### `rfl` sometimes closes goals after `rw`

When `rw` produces a goal that's definitionally true (e.g., `e + -k = e - k` for integers, since `Int.sub a b = a + -b`), `rw` closes it automatically. If you follow `rw` with `congr 1; ring`, you get "No goals to be solved" — drop the trailing tactic or use `try`.

### `mag x - prec` vs `mag x + (-prec)` flakiness

`bpow_plus : bpow (a + b) = bpow a * bpow b`. Reverse-rewriting `← bpow_plus` to combine `bpow a * bpow b` requires the form `bpow (a + b)`, not `bpow (a - b)`. Even though `Int.sub a b = a + -b` definitionally, `rw` doesn't always close via that reduction. Workaround: rewrite `mag x - prec` to `mag x + (-prec)` first (via `show ... from by ring`), then apply `bpow_plus`. Saw this in `ulp_FLT_gt`.

### Going around vs. through

When porting a Coq proof that has substantial case analysis at the boundary (`bpow` exact, `pred y = 0`, etc.), check whether the conclusion can be derived from earlier theorems via the contrapositive. We did this for:

- **`le_pred_pos_lt`**: Coq does ~70 lines of bpow-boundary case analysis. Our proof: ~10 lines via `succ_le_lt_aux` + `succ_pred_pos`. If `pred_pos y < x` then `succ(pred_pos y) ≤ x` (succ_le_lt_aux), but `succ(pred_pos y) = y` (succ_pred_pos), so `y ≤ x`, contradicting `x < y`.

- **`succ_DN_eq_UP` (general)**: Coq goes through `pred_UP_eq_DN` → `pred_UP_le_DN` → `round_neq_0_negligible_exp` → `round_UP_le_DN_lt`. Our route: `le_antisymm` with the forward via `succ_le_lt`, the backward via contradiction (if `succ d < x` then `succ d ≤ d` by round_DN's max + `succ_ge_id`, which collapses to `d = 0` + `negligible_exp = none` + `eq_0_round_0_negligible_exp`).

The "going around" pattern only works when the prerequisite theorems are already proven. The Coq author often has to walk through the boundary because they're proving the foundation. Once it's there, the contrapositive is available as a shortcut.

### `linarith` and `omega`

- `omega` handles linear integer arithmetic (and `Nat.cast`/`Int.toNat`). For any goal involving only `≤`/`<`/`=` on `ℤ`/`ℕ`.
- `linarith` handles linear real arithmetic. Treats multiplications by variables as opaque — `(a - b) * c` won't be seen as `a*c - b*c` unless you pre-distribute via `ring_nf`.
- `nlinarith` allows some non-linear reasoning. Try when `linarith` fails.

### Useful Mathlib API for this corpus

- **Floor/ceil**: `Int.floor`, `Int.ceil`, `Int.floor_le`, `Int.le_ceil`, `Int.floor_le_floor`, `Int.ceil_le_ceil`, `Int.floor_intCast`, `Int.ceil_intCast`, `Int.floor_neg`, `Int.ceil_neg`, `Int.ceil_le_floor_add_one`, `Int.floor_eq_iff`, `Int.ceil_eq_iff`, `Int.floor_lt`, `Int.le_floor`, `Int.floor_nonneg`, `Int.ceil_nonneg`.
- **Int.log**: `Int.log` (in `Mathlib.Data.Int.Log`), `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`, `Int.zpow_le_iff_le_log`, `Int.lt_zpow_iff_log_lt`.
- **zpow**: `zpow_pos`, `zpow_le_zpow_right₀`, `zpow_lt_zpow_right₀`, `zpow_add₀`, `zpow_natCast`, `zpow_neg`, `zpow_one`.
- **abs**: `abs_of_nonneg`, `abs_of_nonpos`, `abs_of_neg`, `abs_of_pos`, `abs_neg`, `abs_zero`, `abs_pos`, `abs_nonneg`, `abs_eq_abs`, `abs_nonpos_iff`, `abs_sub_comm`, `abs_lt`, `abs_add_le`, `abs_mul`.
- **mul/order**: `mul_le_mul_of_nonneg_right`, `mul_lt_mul_of_pos_right`, `mul_lt_mul_iff_of_pos_right`, `mul_nonneg`, `mul_nonpos_of_nonpos_of_nonneg`, `mul_pos`, `mul_neg_of_neg_of_pos`, `mul_right_cancel₀`.
- **max**: `max_le`, `max_le_iff`, `max_eq_left`, `max_eq_right`, `le_max_left`, `le_max_right`, `max_le_max`.
- **Classical**: `Classical.choose`, `Classical.choose_spec` for `∃` → witness.

### Gotcha: Lean's `noncomputable`

`bpow`, `mag`, `Ztrunc`, `Zaway`, `Znearest`, `cexp`, `scaled_mantissa`, `generic_format`, `round`, `Zrnd_opp`, `ulp`, `pred_pos`, `succ`, `pred`, `negligible_exp` are all `noncomputable def`. Anything involving real-number `⌊·⌋`/`⌈·⌉`, `Classical.choose`, or `Real.zpow` requires it. The whole library is fine without runtime computation.

## Suggested next steps

In rough order of usefulness:

1. **DN_UP parity in `Round_NE.lean`** — show `round_DN x` and `round_UP x` have opposite-parity canonical mantissas. This is the *keystone* needed for `Rnd_NE_pt_total/monotone` and `round_NE_pt`. Coq's proof is ~150 lines with separate small/large-x cases. With our `succ_DN_eq_UP`, `mag_DN`, and `mag_mult_bpow` in place, this is now feasible.

2. **Mixed-sign perturbation in `Ulp.lean`** — `round_DN_plus_eps`, `round_UP_plus_eps`, `round_DN_minus_eps`, `round_UP_pred_plus_eps`. Each uses an opp-symmetry argument on top of the positive case. Should be 10–15 lines each.

3. **`x = 0` case of `round_UP_plus_eps_pos`** — analogous to the `x = 0` case in `round_DN_plus_eps_pos` we did. Cases on `negligible_exp`; the `some n` branch needs `Zceil_imp` + a `valid_exp` stabilization argument. ~30 lines.

4. **`round_N_eq_DN` / `round_N_eq_UP` family** — characterize round-to-nearest in terms of where x sits relative to the midpoint of `[round_DN x, round_UP x]`. Foundation for IEEE rounding analyses.

5. **`succ_FLT_exact_shift_*` family** — now possible since `mag_mult_bpow` is in. `ulp_FLT_exact_shift` is already done.

6. **`Core/IEEE754/Binary.v`** — the destination. Will need full Round_NE (DN_UP_parity).

7. **`FLXN_format`** in `FLX.lean` — small but useful for `FTZ_format_FLXN`.

8. **Skipped `Float_prop.v` lemmas**: `Rcompare_F2R` (needs `Rcompare`), `F2R_cond_Zopp` (needs `cond_Zopp`), `F2R_prec_normalize`, the `mag_*` family (`mag_F2R`, `mag_le_Zpower`).

## Useful commands

```bash
# Build
lake build

# Build just one file
lake build LeanFlocq.Core.Generic_fmt

# Check whether a definition exists in Mathlib
grep -rn "theorem foo_bar\|def foo_bar" \
  .lake/packages/mathlib/Mathlib/ | head

# After modifying a theorem, see if the build broke
lake build 2>&1 | grep -E "error|✖|warning|Built LeanFlocq" | head

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
- `POEMS.md` — 13 poems written across the work. They mark moments where something shifted: a debugging insight, a code-review correction, a keystone landing, a pattern recognized. They're not ornamental — they're how the work got paced.
- `HANDOFF.md` — this document.
- `.gitignore` — ignores `.lake/`.

## A note on rhythm

If you're picking this up: the work goes faster when you alternate. Build a bit, commit, build a bit more. Don't try to land four theorems at once — each commit should compile clean. The `0 sorries throughout` in the commit log is from this discipline.

When you hit something genuinely hard (`valid_rnd_N`, `round_N_pt`, `Rnd_NA_NG_pt`, `succ_DN_eq_UP`), the right move is usually:
- **Lift helper lemmas** out, prove each as its own `private theorem`, then the main theorem is a clean composition.
- **Look for a contrapositive shortcut** before porting Coq's chain literally. The library may already have what you need.
- **Use calc patterns** for `rw [ulp_neq_0]`-style traps where the rewrite is too aggressive.

The substantial proofs in this port are typically <100 lines because of these patterns. Each helper hides a case split.

If you find yourself in a 30-line proof fighting Lean, stop and ask: "Did past-me prove a theorem that says exactly this?" Often yes. The library has shape; use it.

Good luck.
