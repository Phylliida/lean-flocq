/-
# ErrFMA L2 (β2 ≠ 0 case): `(β1 − r1) + β2 ∈ F`

The remaining crux of ErrFMA's E2, Pff's `FmaErr_aux2`/`gaCorrect`. This file
builds the Flocq-native pieces that replace Pff's MSB/LSB machinery:

- **Divisibility** (`errfma_be2_mult_bpow`, `errfma_al2_lt_bpow`): `β2` is an
  integer multiple of `β^ℓ` and `|α2| < β^ℓ`, where `ℓ = min(cexp u1, cexp α1)`.
  The multiple falls straight out of `round_repr_same_exp` (rounding a float on
  grid ℓ stays on grid ℓ), with **no** `plusExact1` needed — cleaner than Pff.
- **Exponent bounds** (`errfma_cexp_be1_le_r1`, `errfma_cexp_r1_le_be1`): the
  radix-2 `Expr1`/`Expbe1`, `|cexp β1 − cexp r1| ≤ 1`, from the factor-of-two
  bounds (`round_nearby_factor_two_FLX`).
- **Midpoint dichotomy** (`errfma_be2_div_dichotomy`, REMAINING): `β1 = r1` OR
  `β2` is a multiple of `β^(cexp β1 − 2)`. The Flocq-native form of
  `Midpoint_aux`. **Full derived proof plan** (this replaces "port MSB/LSB" with a
  concrete Flocq proof):

  Abstract setup: `be1 = ◦(be1 + be2)` (be1 a round fixed-point), `r1 = ◦(be1 +
  be2 + al2)`, `be1 ≠ r1`, `be2 ≠ 0`, `be2 = M·β^ℓ` (divisibility), `|al2| < β^ℓ`,
  and `|be2| ≤ ½ ulp(be1)` (be2 is be1's rounding error, via
  `error_le_half_ulp_round`). Conclude `∃ N, be2 = N·β^(cexp be1 − 2)`.

  WLOG `be1 > 0` (sign-reduce via `round_N_opp` + flipped choice, as in the
  engine). Let `u = ulp(be1) = β^cexp(be1)`, `v0 = be1+be2`, `v1 = v0+al2`.

  • **be2 > 0 (upper midpoint).** `v0` rounds to be1 ⟹ `v0 ≤ mid_up := be1 +
    u/2` (else `round_N_ge_midp` on `succ be1`, using `pred_succ`, forces
    `◦v0 ≥ succ be1 > be1`). So `be2 ≤ u/2`. And `v1` rounds to `r1 ≠ be1` ⟹
    `v1 ≥ mid_up` (else `round_N_le_midp` gives `◦v1 ≤ be1`, while `v1 > be1 >
    mid_dn` gives `◦v1 ≥ be1`, so `◦v1 = be1 = r1`, contradiction; uses `be2 ≥
    β^ℓ > |al2|`). So `be2 + al2 ≥ u/2`, i.e. `be2 > u/2 − β^ℓ`. Hence `ξ :=
    u/2 − be2 ∈ [0, β^ℓ)`. Now `u/2 = β^(cexp−1)` and `β^ℓ ≤ be2 ≤ u/2` ⟹ `ℓ ≤
    cexp−1` ⟹ `u/2` is a β^ℓ-multiple; so `ξ` is a β^ℓ-multiple in `[0,β^ℓ)`,
    hence `ξ = 0`, `be2 = u/2 = β^(cexp−1) = 2·β^(cexp−2)`. ✓

  • **be2 < 0 (lower midpoint).** Symmetric with `mid_dn := (be1 + pred be1)/2`
    and `d := be1 − mid_dn = ½(be1 − pred be1)`. `v0 ≥ mid_dn`, `v1 ≤ mid_dn`,
    giving `be2 ∈ [−d, −d + β^ℓ)`, squeeze ⟹ `be2 = −d`. **The pred subtlety:**
    `be1 − pred be1 = β^cexp` (non-power) or `β^(cexp−1)` (power of β, via
    `pred_pos` def — case on `be1 = β^(mag be1 − 1)`), so `d = β^(cexp−1)` or
    `β^(cexp−2)`, both β^(cexp−2)-multiples and (since `β^ℓ ≤ |be2| = d`) β^ℓ-
    multiples. ✓

  • **Divisibility squeeze** (clean helper): a nonneg β^ℓ-multiple `< β^ℓ` is 0.

  The `pred_pos`/power-of-β case in the lower-midpoint branch is the one genuinely
  fiddly spot; everything else is `round_N_{le,ge}_midp` + integer arithmetic.

- **Assembly** (REMAINING): `(β1−r1)+β2 ∈ F`. `be1=r1` ⟹ `= β2 ∈ F` (plus_error).
  Else: β1, r1, β2 are all multiples of `β^(cexp β1 − 2)` (β1 trivially; r1 via
  `cexp r1 ≥ cexp β1 − 1` from `Expbe1`; β2 via the dichotomy), and
  `|(β1−r1)+β2| < β^(cexp β1 + 1) ≤ β^(prec − 2 + (cexp β1 − 2) ... )` ⟹ in F by
  the grid lemma (`generic_format_FLX_of_mult_bpow`, `prec ≥ 3`).

Setting: radix 2, FLX, round-to-nearest, `prec ≥ 4`.
-/
import LeanFlocq.Algorithms.ErrFMA

namespace LeanFlocq

open radix (radix2)
open Classical

/-! ### Divisibility: `β2` is a multiple of `β^min(cexp u1, cexp α1)` -/

/-- `β2 = (u1 + α1) − round(u1 + α1)` is an integer multiple of
`β^min(cexp u1, cexp α1)`: rounding a float on the common grid stays on it. -/
theorem errfma_be2_mult_bpow (prec : ℤ) (choice : ℤ → Bool)
    {u1 al1 be1 be2 : ℝ}
    (Fu1 : generic_format radix2 (FLX_exp prec) u1)
    (Fal1 : generic_format radix2 (FLX_exp prec) al1)
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hbe2 : be2 = u1 + al1 - be1) :
    ∃ M : ℤ, be2 = (M : ℝ)
      * bpow radix2 (min (cexp radix2 (FLX_exp prec) u1) (cexp radix2 (FLX_exp prec) al1)) := by
  set eu := cexp radix2 (FLX_exp prec) u1 with heu
  set ea := cexp radix2 (FLX_exp prec) al1 with hea
  set ℓ := min eu ea with hℓ
  set Mu := Ztrunc (scaled_mantissa radix2 (FLX_exp prec) u1) with hMu
  set Ma := Ztrunc (scaled_mantissa radix2 (FLX_exp prec) al1) with hMa
  have hu : u1 = F2R (beta := radix2) ⟨Mu, eu⟩ := Fu1
  have ha : al1 = F2R (beta := radix2) ⟨Ma, ea⟩ := Fal1
  have hℓu : ℓ ≤ eu := min_le_left _ _
  have hℓa : ℓ ≤ ea := min_le_right _ _
  have hu' : u1 = F2R (beta := radix2) ⟨Mu * (radix2.val : ℤ) ^ (eu - ℓ).toNat, ℓ⟩ := by
    rw [hu]; exact F2R_change_exp ℓ Mu eu hℓu
  have ha' : al1 = F2R (beta := radix2) ⟨Ma * (radix2.val : ℤ) ^ (ea - ℓ).toNat, ℓ⟩ := by
    rw [ha]; exact F2R_change_exp ℓ Ma ea hℓa
  set K := Mu * (radix2.val : ℤ) ^ (eu - ℓ).toNat + Ma * (radix2.val : ℤ) ^ (ea - ℓ).toNat with hK
  have hsum : u1 + al1 = F2R (beta := radix2) ⟨K, ℓ⟩ := by
    rw [hu', ha', ← F2R_plus, Fplus_same_exp]
  obtain ⟨K', hK'⟩ := round_repr_same_exp radix2 (FLX_exp prec) (Znearest choice) K ℓ
  rw [← hsum] at hK'
  refine ⟨K - K', ?_⟩
  rw [hbe2, hbe1, hK', hsum, ← F2R_minus, Fminus_same_exp]
  rfl

/-- `|α2| < β^min(cexp u1, cexp α1)`: α2 is below the common grid. From L1's
bounds `|α2| ≤ |u2| ≤ ½ ulp u1` and `|α2| ≤ ½ ulp α1`. -/
theorem errfma_al2_lt_bpow (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 al2 : ℝ}
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu10 : u1 ≠ 0) (hal10 : al1 ≠ 0)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hal2 : al2 = c + u2 - al1) :
    |al2| < bpow radix2
      (min (cexp radix2 (FLX_exp prec) u1) (cexp radix2 (FLX_exp prec) al1)) := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNotFTZ := monotone_exp_not_FTZ hValid hMon
  -- |al2| ≤ |u2| (round-to-nearest closeness with the float c)
  have hal2_le_u2 : |al2| ≤ |u2| := by
    obtain ⟨_, hcl⟩ := round_N_pt radix2 (FLX_exp prec) hValid choice (c + u2)
    have hc := hcl c Fc
    rw [← hal1] at hc
    have hcu : |c - (c + u2)| = |u2| := by
      rw [show c - (c + u2) = -u2 from by ring, abs_neg]
    rw [hcu] at hc
    rw [hal2, abs_sub_comm]; exact hc
  -- |u2| ≤ ½ ulp u1
  have hu2_err : |u2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) u1 := by
    have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (a * b)
    rw [← hu1] at h
    rw [hu2, abs_sub_comm]; exact h
  -- |al2| ≤ ½ ulp al1
  have hal2_err : |al2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) al1 := by
    have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (c + u2)
    rw [← hal1] at h
    rw [hal2, abs_sub_comm]; exact h
  -- |al2| < β^cexp(u1) and < β^cexp(al1)
  have hlt_u : |al2| < bpow radix2 (cexp radix2 (FLX_exp prec) u1) := by
    rw [ulp_neq_0 radix2 (FLX_exp prec) hu10] at hu2_err
    have hbp : (0 : ℝ) < bpow radix2 (cexp radix2 (FLX_exp prec) u1) := bpow_gt_0 _ _
    calc |al2| ≤ |u2| := hal2_le_u2
      _ ≤ 1 / 2 * bpow radix2 (cexp radix2 (FLX_exp prec) u1) := hu2_err
      _ < bpow radix2 (cexp radix2 (FLX_exp prec) u1) := by linarith
  have hlt_a : |al2| < bpow radix2 (cexp radix2 (FLX_exp prec) al1) := by
    rw [ulp_neq_0 radix2 (FLX_exp prec) hal10] at hal2_err
    have hbp : (0 : ℝ) < bpow radix2 (cexp radix2 (FLX_exp prec) al1) := bpow_gt_0 _ _
    linarith
  rcases le_total (cexp radix2 (FLX_exp prec) u1) (cexp radix2 (FLX_exp prec) al1) with h | h
  · rw [min_eq_left h]; exact hlt_u
  · rw [min_eq_right h]; exact hlt_a

/-! ### Divisibility squeeze (the heart of the midpoint dichotomy) -/

/-- A nonnegative integer multiple of `β^ℓ` that is strictly below `β^ℓ` is `0`.
This is the squeeze that pins `β2` to its midpoint value in the dichotomy. -/
theorem nonneg_bpow_mult_lt_eq_zero (beta : radix) (ℓ : ℤ) {ξ : ℝ} {M : ℤ}
    (hξ : ξ = (M : ℝ) * bpow beta ℓ) (h0 : 0 ≤ ξ) (hlt : ξ < bpow beta ℓ) : ξ = 0 := by
  have hbp : (0 : ℝ) < bpow beta ℓ := bpow_gt_0 beta ℓ
  have hM0 : 0 ≤ M := by
    by_contra h
    push_neg at h
    have hMr : (M : ℝ) < 0 := by exact_mod_cast h
    rw [hξ] at h0
    nlinarith [mul_neg_of_neg_of_pos hMr hbp]
  have hM1 : M < 1 := by
    by_contra h
    push_neg at h
    have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    rw [hξ] at hlt
    nlinarith [hbp]
  have hMz : M = 0 := by omega
  rw [hξ, hMz]; simp

/-- Negative-side squeeze: `be2` is a `β^ℓ`-multiple in `[−β^j, −β^j + β^ℓ)` with
`ℓ ≤ j`, hence `be2 = −β^j` exactly. -/
theorem neg_bpow_squeeze (beta : radix) (ℓ j : ℤ) (hℓj : ℓ ≤ j) {be2 : ℝ} {M : ℤ}
    (hM : be2 = (M : ℝ) * bpow beta ℓ)
    (hlo : -bpow beta j ≤ be2) (hhi : be2 < -bpow beta j + bpow beta ℓ) :
    be2 = -bpow beta j := by
  have hdnn : 0 ≤ j - ℓ := by omega
  have hjpow : bpow beta j = ((beta.val ^ (j - ℓ).toNat : ℤ) : ℝ) * bpow beta ℓ := by
    rw [IZR_Zpower beta hdnn, ← bpow_plus]; congr 1; omega
  set ξ := be2 + bpow beta j with hξdef
  have hξform : ξ = ((M + beta.val ^ (j - ℓ).toNat : ℤ) : ℝ) * bpow beta ℓ := by
    rw [hξdef, hM, hjpow]; push_cast; ring
  have hξ0 : 0 ≤ ξ := by rw [hξdef]; linarith
  have hξlt : ξ < bpow beta ℓ := by rw [hξdef]; linarith
  have := nonneg_bpow_mult_lt_eq_zero beta ℓ hξform hξ0 hξlt
  rw [hξdef] at this; linarith

/-- **Upper-midpoint core.** With `be1 > 0`, `be2 > 0`, `be1 = ◦(be1+be2)`,
`r1 = ◦(be1+be2+al2) ≠ be1`, and the divisibility data, `be2 = β^(cexp be1 − 1)`
(exactly half a ulp). The clean half of the midpoint dichotomy: `r1 ≠ be1` forces
`be1+be2+al2` above the upper midpoint, and the squeeze pins `be2`. -/
theorem errfma_be2_eq_bpow_upper (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {be1 be2 al2 r1 : ℝ} (ℓ : ℤ)
    (Fbe1 : generic_format radix2 (FLX_exp prec) be1)
    (hbe1pos : 0 < be1) (hbe2pos : 0 < be2)
    (hbe1_fix : be1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2))
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2))
    (hne : be1 ≠ r1)
    (hbe2_div : ∃ M : ℤ, be2 = (M : ℝ) * bpow radix2 ℓ)
    (hal2_lt : |al2| < bpow radix2 ℓ)
    (hbe2_le : be2 ≤ 1 / 2 * ulp radix2 (FLX_exp prec) be1) :
    be2 = bpow radix2 (cexp radix2 (FLX_exp prec) be1 - 1) := by
  have hValid := FLX_exp_valid prec hp
  have hbe1ne : be1 ≠ 0 := ne_of_gt hbe1pos
  set c1 := cexp radix2 (FLX_exp prec) be1 with hc1
  have hu : ulp radix2 (FLX_exp prec) be1 = bpow radix2 c1 :=
    ulp_neq_0 radix2 (FLX_exp prec) hbe1ne
  have hbpl : (0 : ℝ) < bpow radix2 ℓ := bpow_gt_0 _ _
  obtain ⟨M, hM⟩ := hbe2_div
  -- M ≥ 1 and β^ℓ ≤ be2
  have hM1 : 1 ≤ M := by
    rcases lt_or_ge M 1 with h | h
    · exfalso
      have : M ≤ 0 := by omega
      have : (M : ℝ) ≤ 0 := by exact_mod_cast this
      nlinarith [hM, mul_nonpos_of_nonpos_of_nonneg this (le_of_lt hbpl)]
    · exact h
  have hbel_le_be2 : bpow radix2 ℓ ≤ be2 := by
    rw [hM]
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    nlinarith [hbpl]
  -- u/2 = β^(c1 − 1)
  have hhalf : 1 / 2 * ulp radix2 (FLX_exp prec) be1 = bpow radix2 (c1 - 1) := by
    rw [hu, show c1 - 1 = c1 + (-1) from by ring, bpow_plus]
    have hb1 : bpow radix2 (-1 : ℤ) = 1 / 2 := by
      show ((radix2.val : ℝ)) ^ (-1 : ℤ) = 1 / 2
      have : (radix2.val : ℝ) = 2 := by norm_cast
      rw [this]; norm_num
    rw [hb1]; ring
  have hbe2_le' : be2 ≤ bpow radix2 (c1 - 1) := by rw [← hhalf]; exact hbe2_le
  -- ℓ ≤ c1 − 1
  have hℓc1 : ℓ ≤ c1 - 1 := by
    by_contra h; push_neg at h
    have : bpow radix2 (c1 - 1) < bpow radix2 ℓ := bpow_lt radix2 (by omega)
    linarith [hbel_le_be2, hbe2_le']
  -- succ structure
  have hsucc : succ radix2 (FLX_exp prec) be1 = be1 + ulp radix2 (FLX_exp prec) be1 :=
    succ_eq_pos radix2 (FLX_exp prec) (le_of_lt hbe1pos)
  -- v1 ≥ mid_up: else r1 = be1.
  have hv1_ge : (be1 + succ radix2 (FLX_exp prec) be1) / 2 ≤ be1 + be2 + al2 := by
    by_contra h; push_neg at h
    -- round_N (be1+be2+al2) ≤ be1
    have hle : round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2) ≤ be1 :=
      round_N_le_midp radix2 (FLX_exp prec) hValid choice Fbe1 h
    -- v1 > mid_dn ⟹ be1 ≤ round_N
    have hv1_gt_be1 : be1 < be1 + be2 + al2 := by
      have hal2 : -bpow radix2 ℓ < al2 := by
        have := neg_abs_le al2; linarith [hal2_lt]
      linarith [hbel_le_be2]
    have hmiddn : (be1 + pred radix2 (FLX_exp prec) be1) / 2 < be1 + be2 + al2 := by
      have := pred_le_id radix2 (FLX_exp prec) be1; linarith
    have hge : be1 ≤ round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2) :=
      round_N_ge_midp radix2 (FLX_exp prec) hValid choice Fbe1 hmiddn
    exact hne (by rw [hr1]; linarith)
  -- be2 ≥ u/2 − al2 > u/2 − β^ℓ
  have hlb : bpow radix2 (c1 - 1) - bpow radix2 ℓ < be2 := by
    have hmid : (be1 + succ radix2 (FLX_exp prec) be1) / 2 = be1 + bpow radix2 (c1 - 1) := by
      rw [hsucc, hu]; rw [← hhalf, hu]; ring
    rw [hmid] at hv1_ge
    have hal2 : al2 < bpow radix2 ℓ := by linarith [le_abs_self al2, hal2_lt]
    linarith
  -- squeeze: ξ = β^(c1-1) − be2 = (β^(c1-1-ℓ) − M)·β^ℓ ∈ [0, β^ℓ) ⟹ 0
  have hdnn : 0 ≤ c1 - 1 - ℓ := by omega
  have hKpow : bpow radix2 (c1 - 1) = ((radix2.val ^ (c1 - 1 - ℓ).toNat : ℤ) : ℝ) * bpow radix2 ℓ := by
    rw [IZR_Zpower radix2 hdnn, ← bpow_plus]; congr 1; omega
  set ξ := bpow radix2 (c1 - 1) - be2 with hξdef
  have hξform : ξ = ((radix2.val ^ (c1 - 1 - ℓ).toNat - M : ℤ) : ℝ) * bpow radix2 ℓ := by
    rw [hξdef, hKpow, hM]; push_cast; ring
  have hξ0 : 0 ≤ ξ := by rw [hξdef]; linarith [hbe2_le']
  have hξlt : ξ < bpow radix2 ℓ := by rw [hξdef]; linarith [hlb]
  have : ξ = 0 := nonneg_bpow_mult_lt_eq_zero radix2 ℓ hξform hξ0 hξlt
  rw [hξdef] at this; linarith

/-- **Lower-midpoint core.** With `be1 > 0`, `be2 < 0`, and the dichotomy data,
`be2 = −β^(cexp be1 − 1)` (non-power-of-β `be1`) or `be2 = −β^(cexp be1 − 2)`
(power of β — the `pred_pos` branch). Both are multiples of `β^(cexp be1 − 2)`. -/
theorem errfma_be2_eq_bpow_lower (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {be1 be2 al2 r1 : ℝ} (ℓ : ℤ)
    (Fbe1 : generic_format radix2 (FLX_exp prec) be1)
    (hbe1pos : 0 < be1) (hbe2neg : be2 < 0)
    (hbe1_fix : be1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2))
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2))
    (hne : be1 ≠ r1)
    (hbe2_div : ∃ M : ℤ, be2 = (M : ℝ) * bpow radix2 ℓ)
    (hal2_lt : |al2| < bpow radix2 ℓ) :
    be2 = -bpow radix2 (cexp radix2 (FLX_exp prec) be1 - 1)
      ∨ be2 = -bpow radix2 (cexp radix2 (FLX_exp prec) be1 - 2) := by
  have hValid := FLX_exp_valid prec hp
  have hbe1ne : be1 ≠ 0 := ne_of_gt hbe1pos
  set c1 := cexp radix2 (FLX_exp prec) be1 with hc1
  have hc1m : c1 = mag radix2 be1 - prec := by rw [hc1]; rfl
  have hu : ulp radix2 (FLX_exp prec) be1 = bpow radix2 c1 :=
    ulp_neq_0 radix2 (FLX_exp prec) hbe1ne
  have hbpl : (0 : ℝ) < bpow radix2 ℓ := bpow_gt_0 _ _
  obtain ⟨M, hM⟩ := hbe2_div
  -- M ≤ −1 and be2 ≤ −β^ℓ
  have hM1 : M ≤ -1 := by
    rcases le_or_gt M (-1) with h | h
    · exact h
    · exfalso
      have hM0 : 0 ≤ M := by omega
      have : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
      nlinarith [hM, mul_nonneg this (le_of_lt hbpl)]
  have hbe2_le_neg : be2 ≤ -bpow radix2 ℓ := by
    rw [hM]
    have : (M : ℝ) ≤ -1 := by exact_mod_cast hM1
    nlinarith [hbpl]
  -- bpow(-1) = 1/2
  have hb1 : bpow radix2 (-1 : ℤ) = 1 / 2 := by
    show ((radix2.val : ℝ)) ^ (-1 : ℤ) = 1 / 2
    have : (radix2.val : ℝ) = 2 := by norm_cast
    rw [this]; norm_num
  set p := pred radix2 (FLX_exp prec) be1 with hp_def
  -- v0 = be1 + be2 ≥ mid_dn = (be1 + p)/2
  have hv0_ge : (be1 + p) / 2 ≤ be1 + be2 := by
    by_contra h; push_neg at h
    have hsp : succ radix2 (FLX_exp prec) p = be1 := succ_pred radix2 (FLX_exp prec) hValid Fbe1
    have hle : round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2) ≤ p :=
      round_N_le_midp radix2 (FLX_exp prec) hValid choice
        (generic_format_pred radix2 (FLX_exp prec) hValid Fbe1)
        (by rw [hsp]; linarith)
    rw [← hbe1_fix] at hle
    have := pred_lt_id radix2 (FLX_exp prec) hbe1ne
    rw [← hp_def] at this; linarith
  -- v1 = be1 + be2 + al2 ≤ mid_dn
  have hv1_le : be1 + be2 + al2 ≤ (be1 + p) / 2 := by
    by_contra h; push_neg at h
    have hge : be1 ≤ round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2) :=
      round_N_ge_midp radix2 (FLX_exp prec) hValid choice Fbe1 h
    have hsucc : succ radix2 (FLX_exp prec) be1 = be1 + ulp radix2 (FLX_exp prec) be1 :=
      succ_eq_pos radix2 (FLX_exp prec) (le_of_lt hbe1pos)
    have hal2 : al2 < bpow radix2 ℓ := lt_of_le_of_lt (le_abs_self al2) hal2_lt
    have hv1_lt_be1 : be1 + be2 + al2 < be1 := by linarith [hbe2_le_neg]
    have hle : round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2) ≤ be1 :=
      round_N_le_midp radix2 (FLX_exp prec) hValid choice Fbe1
        (by rw [hsucc, hu]; have := bpow_gt_0 radix2 c1; linarith)
    exact hne (by rw [hr1]; linarith)
  -- be2 ∈ [(p−be1)/2, (p−be1)/2 + β^ℓ)
  have hlo : (p - be1) / 2 ≤ be2 := by linarith
  have hhi : be2 < (p - be1) / 2 + bpow radix2 ℓ := by
    have hal2 : -bpow radix2 ℓ < al2 := by linarith [neg_abs_le al2, hal2_lt]
    linarith
  -- compute (p − be1)/2 via pred_pos branch
  have hpred_eq : p = pred_pos radix2 (FLX_exp prec) be1 := by
    rw [hp_def]; exact pred_eq_pos radix2 (FLX_exp prec) (le_of_lt hbe1pos)
  by_cases hpow : be1 = bpow radix2 (mag radix2 be1 - 1)
  · -- power of β: be1 − p = β^(c1−1), (p−be1)/2 = −β^(c1−2)
    right
    have hpval : p = be1 - bpow radix2 (c1 - 1) := by
      rw [hpred_eq]; unfold pred_pos; rw [if_pos hpow]
      congr 2
      show FLX_exp prec (mag radix2 be1 - 1) = c1 - 1
      unfold FLX_exp; omega
    have hmidval : (p - be1) / 2 = -bpow radix2 (c1 - 2) := by
      rw [hpval]
      rw [show c1 - 2 = (c1 - 1) + (-1) from by ring, bpow_plus, hb1]; ring
    rw [hmidval] at hlo hhi
    have hℓj : ℓ ≤ c1 - 2 := by
      by_contra hcon; push_neg at hcon
      have : bpow radix2 (c1 - 2) < bpow radix2 ℓ := bpow_lt radix2 (by omega)
      have hbe2ge : -bpow radix2 (c1 - 2) ≤ be2 := hlo
      linarith [hbe2_le_neg]
    exact neg_bpow_squeeze radix2 ℓ (c1 - 2) hℓj hM hlo hhi
  · -- non-power: be1 − p = ulp = β^c1, (p−be1)/2 = −β^(c1−1)
    left
    have hpval : p = be1 - bpow radix2 c1 := by
      rw [hpred_eq]; unfold pred_pos; rw [if_neg hpow, hu]
    have hmidval : (p - be1) / 2 = -bpow radix2 (c1 - 1) := by
      rw [hpval]
      rw [show c1 - 1 = c1 + (-1) from by ring, bpow_plus, hb1]; ring
    rw [hmidval] at hlo hhi
    have hℓj : ℓ ≤ c1 - 1 := by
      by_contra hcon; push_neg at hcon
      have : bpow radix2 (c1 - 1) < bpow radix2 ℓ := bpow_lt radix2 (by omega)
      have hbe2ge : -bpow radix2 (c1 - 1) ≤ be2 := hlo
      linarith [hbe2_le_neg]
    exact neg_bpow_squeeze radix2 ℓ (c1 - 1) hℓj hM hlo hhi

/-! ### The dichotomy: `β1 = r1` or `β2` is a multiple of `β^(cexp β1 − 2)` -/

/-- The positive-`be1` dispatcher: combine the upper/lower cores into "β2 is a
multiple of `β^(cexp be1 − 2)`". -/
theorem errfma_be2_div_dichotomy_pos (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {be1 be2 al2 r1 : ℝ} (ℓ : ℤ)
    (Fbe1 : generic_format radix2 (FLX_exp prec) be1)
    (hb1pos : 0 < be1) (hbe2_ne : be2 ≠ 0)
    (hbe1_fix : be1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2))
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2))
    (hne : be1 ≠ r1)
    (hbe2_div : ∃ M : ℤ, be2 = (M : ℝ) * bpow radix2 ℓ)
    (hal2_lt : |al2| < bpow radix2 ℓ) :
    ∃ N : ℤ, be2 = (N : ℝ) * bpow radix2 (cexp radix2 (FLX_exp prec) be1 - 2) := by
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNotFTZ := monotone_exp_not_FTZ hValid hMon
  set c1 := cexp radix2 (FLX_exp prec) be1 with hc1
  have hconv : bpow radix2 (c1 - 1) = 2 * bpow radix2 (c1 - 2) := by
    rw [show c1 - 1 = (c1 - 2) + 1 from by ring, bpow_plus, bpow_one]
    have : (radix2.val : ℝ) = 2 := by norm_cast
    rw [this]; ring
  rcases lt_trichotomy be2 0 with hb2neg | hb2zero | hb2pos
  · rcases errfma_be2_eq_bpow_lower prec hp choice ℓ Fbe1 hb1pos hb2neg hbe1_fix hr1 hne
        hbe2_div hal2_lt with h | h
    · rw [← hc1] at h; exact ⟨-2, by rw [h, hconv]; push_cast; ring⟩
    · rw [← hc1] at h; exact ⟨-1, by rw [h]; push_cast; ring⟩
  · exact absurd hb2zero hbe2_ne
  · have hbe2_le : be2 ≤ 1 / 2 * ulp radix2 (FLX_exp prec) be1 := by
      have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (be1 + be2)
      rw [← hbe1_fix] at h
      have heq : |be1 - (be1 + be2)| = be2 := by
        rw [show be1 - (be1 + be2) = -be2 from by ring, abs_neg, abs_of_pos hb2pos]
      rw [heq] at h; exact h
    have h := errfma_be2_eq_bpow_upper prec hp choice ℓ Fbe1 hb1pos hb2pos hbe1_fix hr1 hne
      hbe2_div hal2_lt hbe2_le
    rw [← hc1] at h; exact ⟨2, by rw [h, hconv]; push_cast; ring⟩

/-- **The midpoint dichotomy** (`Midpoint_aux`). Either the FMA result equals
`β1` or `β2` is a multiple of `β^(cexp β1 − 2)`. Sign-reduces `be1 < 0` to the
positive dispatcher via `round_N_opp` with a flipped tie-breaker. -/
theorem errfma_be2_div_dichotomy (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)
    {be1 be2 al2 r1 : ℝ}
    (Fbe1 : generic_format radix2 (FLX_exp prec) be1)
    (hbe2_ne : be2 ≠ 0)
    (hbe1_fix : be1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2))
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2))
    {ℓ : ℤ}
    (hbe2_div : ∃ M : ℤ, be2 = (M : ℝ) * bpow radix2 ℓ)
    (hal2_lt : |al2| < bpow radix2 ℓ) :
    be1 = r1 ∨
      ∃ N : ℤ, be2 = (N : ℝ) * bpow radix2 (cexp radix2 (FLX_exp prec) be1 - 2) := by
  by_cases hbe1r1 : be1 = r1
  · left; exact hbe1r1
  · right
    have hValid := FLX_exp_valid prec hp
    have hMon := FLX_exp_monotone prec
    have hNotFTZ := monotone_exp_not_FTZ hValid hMon
    -- |be2| ≤ ½ ulp be1 (be2 is be1's rounding error)
    have hbe2_le_half : |be2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) be1 := by
      have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (be1 + be2)
      rw [← hbe1_fix] at h
      have heq : |be1 - (be1 + be2)| = |be2| := by
        rw [show be1 - (be1 + be2) = -be2 from by ring, abs_neg]
      rw [heq] at h; exact h
    -- be1 ≠ 0
    have hbe1ne : be1 ≠ 0 := by
      intro h0
      apply hbe2_ne
      rw [h0, ulp_FLX_0 radix2 prec hp, mul_zero] at hbe2_le_half
      exact abs_eq_zero.mp (le_antisymm hbe2_le_half (abs_nonneg be2))
    rcases lt_trichotomy be1 0 with hb1neg | hb1zero | hb1pos
    · -- be1 < 0: negate everything and use the positive dispatcher
      set c' : ℤ → Bool := fun t => !choice (-(t + 1)) with hc'
      have hflip : (fun t : ℤ => !c' (-(t + 1))) = choice := by
        funext t; rw [hc']; show (!!choice (-(-(t + 1) + 1))) = choice t; simp
      have Fnb1 : generic_format radix2 (FLX_exp prec) (-be1) :=
        generic_format_opp radix2 (FLX_exp prec) Fbe1
      -- -be1 = round c' (-be1 + -be2)
      have hfix' : -be1 = round radix2 (FLX_exp prec) (Znearest c') (-be1 + -be2) := by
        have := round_N_opp radix2 (FLX_exp prec) c' (be1 + be2)
        rw [hflip] at this
        rw [show -be1 + -be2 = -(be1 + be2) from by ring, this, ← hbe1_fix]
      have hr1' : -r1 = round radix2 (FLX_exp prec) (Znearest c') (-be1 + -be2 + -al2) := by
        have := round_N_opp radix2 (FLX_exp prec) c' (be1 + be2 + al2)
        rw [hflip] at this
        rw [show -be1 + -be2 + -al2 = -(be1 + be2 + al2) from by ring, this, ← hr1]
      have hne' : -be1 ≠ -r1 := fun h => hbe1r1 (neg_injective h)
      have hdiv' : ∃ M : ℤ, -be2 = (M : ℝ) * bpow radix2 ℓ := by
        obtain ⟨M, hM⟩ := hbe2_div; exact ⟨-M, by rw [hM]; push_cast; ring⟩
      have hal2' : |-al2| < bpow radix2 ℓ := by rw [abs_neg]; exact hal2_lt
      obtain ⟨N, hN⟩ := errfma_be2_div_dichotomy_pos prec hp c' ℓ Fnb1
        (by linarith) (by simpa using hbe2_ne) hfix' hr1' hne' hdiv' hal2'
      rw [cexp_opp] at hN
      exact ⟨-N, by
        have : be2 = -(-be2) := by ring
        rw [this, hN]; push_cast; ring⟩
    · exact absurd hb1zero hbe1ne
    · exact errfma_be2_div_dichotomy_pos prec hp choice ℓ Fbe1 hb1pos hbe2_ne hbe1_fix hr1
        hbe1r1 hbe2_div hal2_lt

end LeanFlocq
