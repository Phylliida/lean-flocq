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

/-! ### Assembly: `(β1 − r1) + β2 ∈ F` -/

/-- A format element with `cexp ≥ E` is an integer multiple of `β^E`. -/
theorem format_mult_bpow_of_cexp_ge (beta : radix) (prec : ℤ) {x : ℝ} (E : ℤ)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hE : E ≤ cexp beta (FLX_exp prec) x) :
    ∃ m : ℤ, x = (m : ℝ) * bpow beta E := by
  set e := cexp beta (FLX_exp prec) x with he
  set Mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hMx
  have hx : x = F2R (beta := beta) ⟨Mx, e⟩ := Fx
  refine ⟨Mx * (beta.val : ℤ) ^ (e - E).toNat, ?_⟩
  rw [hx, F2R_change_exp E Mx e hE]; rfl

/-- **ErrFMA L2 (`gaCorrect`).** `(β1 − r1) + β2 ∈ F`, the keystone of the
`β2 ≠ 0` branch. `β1 = r1` ⟹ `= β2 ∈ F`; else the dichotomy makes β2 a
`β^(cexp β1 − 2)`-multiple, β1 and r1 are coarser multiples (via `Expbe1`), and a
magnitude bound `< β^(cexp β1 + 1)` closes it by the grid lemma. -/
theorem errfma_ga_exact (prec : ℤ) (hp : 3 ≤ prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 al2 be1 be2 r1 : ℝ}
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu10 : u1 ≠ 0) (hal10 : al1 ≠ 0) (hbe2_ne : be2 ≠ 0) (hr1_ne : r1 ≠ 0)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hal2 : al2 = c + u2 - al1)
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hbe2 : be2 = u1 + al1 - be1)
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b + c)) :
    generic_format radix2 (FLX_exp prec) (be1 - r1 + be2) := by
  have hp0 : 0 < prec := by omega
  have hValid := FLX_exp_valid prec hp0
  have hMon := FLX_exp_monotone prec
  have hNotFTZ := monotone_exp_not_FTZ hValid hMon
  have Fu1 : generic_format radix2 (FLX_exp prec) u1 := by
    rw [hu1]; exact generic_format_round _ _ hValid _ _
  have Fal1 : generic_format radix2 (FLX_exp prec) al1 := by
    rw [hal1]; exact generic_format_round _ _ hValid _ _
  have Fbe1 : generic_format radix2 (FLX_exp prec) be1 := by
    rw [hbe1]; exact generic_format_round _ _ hValid _ _
  have Fr1 : generic_format radix2 (FLX_exp prec) r1 := by
    rw [hr1]; exact generic_format_round _ _ hValid _ _
  -- β2 ∈ F (rounding error of u1 + al1)
  have Fbe2 : generic_format radix2 (FLX_exp prec) be2 := by
    have h := plus_error radix2 (FLX_exp prec) hValid hMon choice Fu1 Fal1
    rw [← hbe1] at h
    rw [show be2 = -(be1 - (u1 + al1)) from by rw [hbe2]; ring]
    exact generic_format_opp _ _ h
  -- be1 + be2 = u1 + al1, be1 + be2 + al2 = a*b + c
  have hsum1 : be1 + be2 = u1 + al1 := by rw [hbe2]; ring
  have hsum2 : be1 + be2 + al2 = a * b + c := by rw [hbe2, hal2, hu2]; ring
  have hfix : be1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2) := by
    rw [hsum1, hbe1]
  have hr1' : r1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2 + al2) := by
    rw [hsum2, hr1]
  -- divisibility + al2 bound at ℓ = min(cexp u1, cexp al1)
  set ℓ := min (cexp radix2 (FLX_exp prec) u1) (cexp radix2 (FLX_exp prec) al1) with hℓ
  have hdiv : ∃ M : ℤ, be2 = (M : ℝ) * bpow radix2 ℓ :=
    errfma_be2_mult_bpow prec choice Fu1 Fal1 hbe1 hbe2
  have hal2lt : |al2| < bpow radix2 ℓ :=
    errfma_al2_lt_bpow prec hp0 choice Fc hu10 hal10 hu1 hu2 hal1 hal2
  -- dichotomy
  rcases errfma_be2_div_dichotomy prec hp0 choice Fbe1 hbe2_ne hfix hr1' hdiv hal2lt with
    hbe1r1 | ⟨N, hN⟩
  · -- be1 = r1: (be1 - r1) + be2 = be2 ∈ F
    rw [show be1 - r1 + be2 = be2 from by rw [hbe1r1]; ring]; exact Fbe2
  · -- assembly on grid β^(cexp be1 − 2)
    set c1 := cexp radix2 (FLX_exp prec) be1 with hc1
    have hbe1ne : be1 ≠ 0 := by
      intro h0; apply hbe2_ne
      have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (be1 + be2)
      rw [← hfix, h0, ulp_FLX_0 radix2 prec hp0] at h
      simp only [zero_add, zero_sub, abs_neg, mul_zero] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    -- factor-of-two: |be1| ≤ 2|r1|, |r1| ≤ 2|be1|
    have hHea : |al2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) u1 := by
      have hcl := (round_N_pt radix2 (FLX_exp prec) hValid choice (c + u2)).2 c Fc
      rw [← hal1] at hcl
      have hcu : |c - (c + u2)| = |u2| := by rw [show c - (c + u2) = -u2 from by ring, abs_neg]
      rw [hcu] at hcl
      have hu2err : |u2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) u1 := by
        have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (a * b)
        rw [← hu1] at h; rw [hu2, abs_sub_comm]; exact h
      have : |al2| ≤ |u2| := by rw [hal2, abs_sub_comm]; exact hcl
      linarith
    have hHeb : |al2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) al1 := by
      have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (c + u2)
      rw [← hal1] at h; rw [hal2, abs_sub_comm]; exact h
    have hu1al1_ne : u1 + al1 ≠ 0 := by
      intro h0; apply hbe2_ne; rw [hbe2, h0, hbe1, ← h0, h0,
        round_0 radix2 (FLX_exp prec) (Znearest choice)]; ring
    obtain ⟨_, hb1le2r, hr1le2b⟩ :=
      round_nearby_factor_two_FLX prec hp choice Fu1 Fal1 hHea hHeb hu10 hal10 hu1al1_ne
    rw [← hbe1] at hb1le2r hr1le2b
    have hround_r1 : round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1 + al2) = r1 := by
      rw [show u1 + al1 + al2 = a * b + c from by rw [hal2, hu2]; ring, hr1]
    rw [hround_r1] at hb1le2r hr1le2b
    -- cexp(r1) ∈ [c1 − 1, c1 + 1]
    have h2bpow : (2 : ℝ) = bpow radix2 1 := by rw [bpow_one]; norm_cast
    have hmag_le1 : mag radix2 be1 ≤ mag radix2 r1 + 1 := by
      have h2 : |be1| ≤ |2 * r1| := by rw [abs_mul]; simp only [abs_two]; linarith [hb1le2r]
      have := mag_le_abs radix2 hbe1ne h2
      rwa [show (2 : ℝ) * r1 = r1 * bpow radix2 1 from by rw [h2bpow]; ring,
        mag_mult_bpow radix2 hr1_ne] at this
    have hmag_le2 : mag radix2 r1 ≤ mag radix2 be1 + 1 := by
      have h2 : |r1| ≤ |2 * be1| := by rw [abs_mul]; simp only [abs_two]; linarith [hr1le2b]
      have := mag_le_abs radix2 hr1_ne h2
      rwa [show (2 : ℝ) * be1 = be1 * bpow radix2 1 from by rw [h2bpow]; ring,
        mag_mult_bpow radix2 hbe1ne] at this
    have hcexp_r1_lo : c1 - 1 ≤ cexp radix2 (FLX_exp prec) r1 := by
      show c1 - 1 ≤ FLX_exp prec (mag radix2 r1)
      unfold FLX_exp; rw [hc1]; show cexp radix2 (FLX_exp prec) be1 - 1 ≤ _
      unfold cexp FLX_exp; omega
    have hcexp_r1_hi : cexp radix2 (FLX_exp prec) r1 ≤ c1 + 1 := by
      show FLX_exp prec (mag radix2 r1) ≤ c1 + 1
      unfold FLX_exp; rw [hc1]; unfold cexp FLX_exp; omega
    -- |al2| ≤ |be2|  (al2 below β2's grid)
    have hal2_le_be2 : |al2| ≤ |be2| := by
      obtain ⟨Mb, hMb⟩ := hdiv
      have hMb1 : (1 : ℤ) ≤ |Mb| := by
        rcases eq_or_ne Mb 0 with h | h
        · exfalso; apply hbe2_ne; rw [hMb, h]; simp
        · exact Int.one_le_abs h
      have : bpow radix2 ℓ ≤ |be2| := by
        rw [hMb, abs_mul, abs_of_pos (bpow_gt_0 radix2 ℓ)]
        have : (1 : ℝ) ≤ |(Mb : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hMb1
        nlinarith [bpow_gt_0 radix2 ℓ]
      linarith [hal2lt]
    -- magnitude: |(be1 − r1) + be2| < β^(c1 + 1)
    have hmagbound : |be1 - r1 + be2| < bpow radix2 (c1 + 1) := by
      have heq : be1 - r1 + be2 = (a * b + c - r1) - al2 := by
        have : be1 + be2 = a * b + c - al2 := by rw [hsum1]; linarith [hsum2]
        linarith [this]
      have hfma_err : |a * b + c - r1| ≤ 1 / 2 * bpow radix2 (cexp radix2 (FLX_exp prec) r1) := by
        have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (a * b + c)
        rw [← hr1, ulp_neq_0 radix2 (FLX_exp prec) hr1_ne] at h
        rw [abs_sub_comm]; exact h
      have hr1ulp_le : bpow radix2 (cexp radix2 (FLX_exp prec) r1) ≤ bpow radix2 (c1 + 1) :=
        bpow_le radix2 hcexp_r1_hi
      have hbe2ulp : |be2| ≤ 1 / 2 * bpow radix2 c1 := by
        have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (be1 + be2)
        rw [← hfix, ulp_neq_0 radix2 (FLX_exp prec) hbe1ne, ← hc1] at h
        have : |be1 - (be1 + be2)| = |be2| := by rw [show be1 - (be1 + be2) = -be2 from by ring, abs_neg]
        rw [this] at h; exact h
      have hc1_lt : bpow radix2 c1 < bpow radix2 (c1 + 1) := bpow_lt radix2 (by omega)
      rw [heq]
      calc |a * b + c - r1 - al2| ≤ |a * b + c - r1| + |al2| := abs_sub _ _
        _ ≤ 1 / 2 * bpow radix2 (cexp radix2 (FLX_exp prec) r1) + |be2| := by linarith [hal2_le_be2]
        _ < bpow radix2 (c1 + 1) := by linarith
    -- (be1 − r1) + be2 = K·β^(c1 − 2)
    obtain ⟨mb, hmb⟩ := format_mult_bpow_of_cexp_ge radix2 prec (c1 - 2) Fbe1 (by rw [← hc1]; omega)
    obtain ⟨mr, hmr⟩ := format_mult_bpow_of_cexp_ge radix2 prec (c1 - 2) Fr1 (by omega)
    have hmult : be1 - r1 + be2 = ((mb - mr + N : ℤ) : ℝ) * bpow radix2 (c1 - 2) := by
      rw [hmb, hmr, hN]; push_cast; ring
    -- grid lemma
    have hgrid : |be1 - r1 + be2| < bpow radix2 (prec + (c1 - 2)) :=
      lt_of_lt_of_le hmagbound (bpow_le radix2 (by omega))
    exact generic_format_FLX_of_mult_bpow radix2 prec (mb - mr + N) (c1 - 2) hmult hgrid

/-! ### The β2 ≠ 0 branch (`FmaErr_aux2`) -/

/-- **ErrFMA, `β2 ≠ 0` case.** With `γ = ◦(◦(β1−r1) + β2)`, both roundings are
exact (L1: `β1−r1 ∈ F`; L2: `(β1−r1)+β2 ∈ F`), so `γ = β1+β2−r1` and the
three-term identity `a·b + c = r1 + γ + α2` follows. -/
theorem ErrFMA_be2_nonzero (prec : ℤ) (hp : 3 ≤ prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 al2 be1 be2 r1 gat ga : ℝ}
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu10 : u1 ≠ 0) (hal10 : al1 ≠ 0) (hbe2_ne : be2 ≠ 0) (hr1_ne : r1 ≠ 0)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hal2 : al2 = c + u2 - al1)
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hbe2 : be2 = u1 + al1 - be1)
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b + c))
    (hgat : gat = round radix2 (FLX_exp prec) (Znearest choice) (be1 - r1))
    (hga : ga = round radix2 (FLX_exp prec) (Znearest choice) (gat + be2)) :
    a * b + c = r1 + ga + al2 := by
  have hp0 : 0 < prec := by omega
  -- L1: be1 − r1 ∈ F, so gat = be1 − r1
  have hL1 : generic_format radix2 (FLX_exp prec) (be1 - r1) :=
    errfma_gat_exact prec hp choice Fc hu1 hu2 hal1 hbe1 hr1
  have hgat_eq : gat = be1 - r1 := by
    rw [hgat]; exact round_generic radix2 (FLX_exp prec) (Znearest choice) hL1
  -- L2: (be1 − r1) + be2 ∈ F, so ga = (be1 − r1) + be2
  have hL2 : generic_format radix2 (FLX_exp prec) (be1 - r1 + be2) :=
    errfma_ga_exact prec hp choice Fc hu10 hal10 hbe2_ne hr1_ne hu1 hu2 hal1 hal2 hbe1 hbe2 hr1
  have hga_eq : ga = be1 - r1 + be2 := by
    rw [hga, hgat_eq]
    exact round_generic radix2 (FLX_exp prec) (Znearest choice) hL2
  -- algebra
  rw [hga_eq, hbe2, hal2, hu2]; ring

/-! ### The full ErrFMA error theorem (`FmaErr`) -/

/-- **ErrFMA (Boldo–Muller Theorem 2).** For floats `a, b, c` at FLX radix 2,
`prec ≥ 4`, with the Algorithm-4 intermediate values, `a·b + c = r1 + γ + α2`
exactly. Combines the `β2 = 0` and `β2 ≠ 0` branches; the `β2 ≠ 0` edge
conditions (`u1, α1, r1 ≠ 0`) are discharged from `β2 ≠ 0`. -/
theorem ErrFMA_correct (prec : ℤ) (hp : 3 ≤ prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 al2 be1 be2 r1 gat ga : ℝ}
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hal2 : al2 = c + u2 - al1)
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hbe2 : be2 = u1 + al1 - be1)
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b + c))
    (hgat : gat = round radix2 (FLX_exp prec) (Znearest choice) (be1 - r1))
    (hga : ga = round radix2 (FLX_exp prec) (Znearest choice) (gat + be2)) :
    a * b + c = r1 + ga + al2 := by
  have hp0 : 0 < prec := by omega
  have hValid := FLX_exp_valid prec hp0
  have hMon := FLX_exp_monotone prec
  have hNotFTZ := monotone_exp_not_FTZ hValid hMon
  have Fu1 : generic_format radix2 (FLX_exp prec) u1 := by
    rw [hu1]; exact generic_format_round _ _ hValid _ _
  have Fbe1 : generic_format radix2 (FLX_exp prec) be1 := by
    rw [hbe1]; exact generic_format_round _ _ hValid _ _
  -- ◦v = 0 ⟹ v = 0 at FLX
  have round_zero_imp : ∀ v : ℝ,
      round radix2 (FLX_exp prec) (Znearest choice) v = 0 → v = 0 := by
    intro v hv
    have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice v
    rw [hv, ulp_FLX_0 radix2 prec hp0, zero_sub, abs_neg, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  by_cases hbe2z : be2 = 0
  · exact ErrFMA_be2_zero prec hp choice Fc hu1 hu2 hal1 hal2 hbe1 hbe2 hr1 hgat hga hbe2z
  · -- β2 ≠ 0: derive u1, al1, r1 ≠ 0
    have hu10 : u1 ≠ 0 := by
      intro hu1z; apply hbe2z
      have habz : a * b = 0 := round_zero_imp (a * b) (by rw [← hu1]; exact hu1z)
      have hu2z : u2 = 0 := by rw [hu2, hu1z, habz]; ring
      have hal1c : al1 = c := by
        rw [hal1, hu2z, add_zero]; exact round_generic radix2 (FLX_exp prec) (Znearest choice) Fc
      have hbe1c : be1 = c := by
        rw [hbe1, hu1z, hal1c, zero_add]; exact round_generic radix2 (FLX_exp prec) (Znearest choice) Fc
      rw [hbe2, hu1z, hal1c, hbe1c]; ring
    have hal10 : al1 ≠ 0 := by
      intro hal1z; apply hbe2z
      have hbe1u : be1 = u1 := by
        rw [hbe1, hal1z, add_zero]; exact round_generic radix2 (FLX_exp prec) (Znearest choice) Fu1
      rw [hbe2, hal1z, hbe1u]; ring
    have hr1_ne : r1 ≠ 0 := by
      intro hr1z; apply hbe2z
      have habc0 : a * b + c = 0 := round_zero_imp (a * b + c) (by rw [← hr1]; exact hr1z)
      have hsum0 : be1 + be2 + al2 = 0 := by
        rw [show be1 + be2 + al2 = a * b + c from by rw [hbe2, hal2, hu2]; ring, habc0]
      -- |al2| ≤ |be2| via divisibility
      set ℓ := min (cexp radix2 (FLX_exp prec) u1) (cexp radix2 (FLX_exp prec) al1) with hℓ
      obtain ⟨Mb, hMb⟩ := errfma_be2_mult_bpow prec choice Fu1
        (by rw [hal1]; exact generic_format_round _ _ hValid _ _) hbe1 hbe2
      have hal2lt : |al2| < bpow radix2 ℓ :=
        errfma_al2_lt_bpow prec hp0 choice Fc hu10 hal10 hu1 hu2 hal1 hal2
      have hal2_le_be2 : |al2| ≤ |be2| := by
        rcases eq_or_ne Mb 0 with h | h
        · exfalso; apply hbe2z; rw [hMb, h]; simp
        · have hMb1 : (1 : ℤ) ≤ |Mb| := Int.one_le_abs h
          have : bpow radix2 ℓ ≤ |be2| := by
            rw [hMb, abs_mul, abs_of_pos (bpow_gt_0 radix2 ℓ)]
            have : (1 : ℝ) ≤ |(Mb : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hMb1
            nlinarith [bpow_gt_0 radix2 ℓ]
          linarith [hal2lt]
      -- |be2| ≤ ½ ulp be1
      have hbe2_le : |be2| ≤ 1 / 2 * ulp radix2 (FLX_exp prec) be1 := by
        have hfix : be1 = round radix2 (FLX_exp prec) (Znearest choice) (be1 + be2) := by
          rw [show be1 + be2 = u1 + al1 from by rw [hbe2]; ring, hbe1]
        have h := error_le_half_ulp_round radix2 (FLX_exp prec) hValid hNotFTZ hMon choice (be1 + be2)
        rw [← hfix] at h
        have : |be1 - (be1 + be2)| = |be2| := by
          rw [show be1 - (be1 + be2) = -be2 from by ring, abs_neg]
        rw [this] at h; exact h
      -- be1 = 0 (else magnitude contradiction), hence be2 = 0
      have hbe1z : be1 = 0 := by
        by_contra hbe1ne
        have hule : |be1| ≤ ulp radix2 (FLX_exp prec) be1 := by
          have : |be1| ≤ 2 * |be2| := by
            have := abs_add_le be2 al2
            have hb1eq : be1 = -(be2 + al2) := by linarith [hsum0]
            rw [hb1eq, abs_neg]; linarith [hal2_le_be2]
          linarith [hbe2_le]
        rw [ulp_neq_0 radix2 (FLX_exp prec) hbe1ne] at hule
        have hlo := bpow_mag_le radix2 hbe1ne
        have : bpow radix2 (mag radix2 be1 - 1) ≤ bpow radix2 (cexp radix2 (FLX_exp prec) be1) :=
          le_trans hlo hule
        have hexp : mag radix2 be1 - 1 ≤ cexp radix2 (FLX_exp prec) be1 := by
          by_contra hc; push_neg at hc
          exact absurd this (not_le.mpr (bpow_lt radix2 (by omega)))
        have : mag radix2 be1 - 1 ≤ mag radix2 be1 - prec := by
          rwa [show cexp radix2 (FLX_exp prec) be1 = mag radix2 be1 - prec from rfl] at hexp
        omega
      have hu1al1z : u1 + al1 = 0 :=
        round_zero_imp (u1 + al1) (by rw [← hbe1]; exact hbe1z)
      rw [hbe2, hu1al1z, hbe1z]; ring
    exact ErrFMA_be2_nonzero prec hp choice Fc hu10 hal10 hbe2z hr1_ne
      hu1 hu2 hal1 hal2 hbe1 hbe2 hr1 hgat hga

/-! ### The three-float error-free transformation (`Fma_FTS`) -/

/-- **ErrFMA as a 3-term EFT.** `a·b + c = r1 + r2 + r3` exactly, with
`r2, r3 ∈ F` and `r2 = ◦(γ + α2)`. The Algorithm-4 final step is
`Fast2Sum(γ, α2)`; we use the precondition-free `TwoSum(γ, α2)` (same exact
`r2 + r3 = γ + α2`), so no `|α2| ≤ |γ|` obligation is needed. -/
theorem ErrFMA_threefloat (prec : ℤ) (hp : 3 ≤ prec) (choice : ℤ → Bool)
    {a b c u1 u2 al1 al2 be1 be2 r1 gat ga : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Fc : generic_format radix2 (FLX_exp prec) c)
    (hu1 : u1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b))
    (hu2 : u2 = a * b - u1)
    (hal1 : al1 = round radix2 (FLX_exp prec) (Znearest choice) (c + u2))
    (hal2 : al2 = c + u2 - al1)
    (hbe1 : be1 = round radix2 (FLX_exp prec) (Znearest choice) (u1 + al1))
    (hbe2 : be2 = u1 + al1 - be1)
    (hr1 : r1 = round radix2 (FLX_exp prec) (Znearest choice) (a * b + c))
    (hgat : gat = round radix2 (FLX_exp prec) (Znearest choice) (be1 - r1))
    (hga : ga = round radix2 (FLX_exp prec) (Znearest choice) (gat + be2)) :
    ∃ r2 r3 : ℝ,
      generic_format radix2 (FLX_exp prec) r2 ∧
      generic_format radix2 (FLX_exp prec) r3 ∧
      r2 = round radix2 (FLX_exp prec) (Znearest choice) (ga + al2) ∧
      a * b + c = r1 + r2 + r3 := by
  have hp0 : 0 < prec := by omega
  have hValid := FLX_exp_valid prec hp0
  have hMon := FLX_exp_monotone prec
  -- core identity
  have hcore : a * b + c = r1 + ga + al2 :=
    ErrFMA_correct prec hp choice Fc hu1 hu2 hal1 hal2 hbe1 hbe2 hr1 hgat hga
  -- ga, al2 ∈ F
  have Fga : generic_format radix2 (FLX_exp prec) ga := by
    rw [hga]; exact generic_format_round _ _ hValid _ _
  have Fu2 : generic_format radix2 (FLX_exp prec) u2 := by
    rw [show u2 = -(round radix2 (FLX_exp prec) (Znearest choice) (a * b) - a * b) from by
      rw [hu2, hu1]; ring]
    exact generic_format_opp _ _ (mult_error_FLX radix2 prec hp0 (Znearest choice) Fa Fb)
  have Fal2 : generic_format radix2 (FLX_exp prec) al2 := by
    rw [show al2 = -(round radix2 (FLX_exp prec) (Znearest choice) (c + u2) - (c + u2)) from by
      rw [hal2, hal1]; ring]
    exact generic_format_opp _ _
      (plus_error radix2 (FLX_exp prec) hValid hMon choice Fc Fu2)
  -- TwoSum(ga, al2): ga + al2 = round(ga+al2) + e
  have htwo := TwoSum_FLX_correct prec hp0 choice Fga Fal2
  set r2 := round radix2 (FLX_exp prec) (Znearest choice) (ga + al2) with hr2
  set r3 := (if |al2| ≤ |ga|
       then round radix2 (FLX_exp prec) (Znearest choice)
              (al2 - round radix2 (FLX_exp prec) (Znearest choice) (r2 - ga))
       else round radix2 (FLX_exp prec) (Znearest choice)
              (ga - round radix2 (FLX_exp prec) (Znearest choice) (r2 - al2))) with hr3
  refine ⟨r2, r3, generic_format_round _ _ hValid _ _, ?_, rfl, ?_⟩
  · rw [hr3]; split_ifs <;> exact generic_format_round _ _ hValid _ _
  · -- ga + al2 = r2 + r3, so a*b+c = r1 + ga + al2 = r1 + r2 + r3
    have hsum : ga + al2 = r2 + r3 := htwo
    linarith [hcore, hsum]

end LeanFlocq
