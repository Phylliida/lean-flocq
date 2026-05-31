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
- **Midpoint dichotomy** (`errfma_be2_div_dichotomy`): `β1 = r1` OR `β2` is a
  multiple of `β^(cexp β1 − 2)`. The Flocq-native form of `Midpoint_aux`: if the
  tiny α2 flips the rounding (`r1 ≠ β1`), then `β1+β2` sits within `|α2|` of a
  grid midpoint, and a divisibility squeeze (`ξ = ±½ulp − β2` is a β^ℓ-multiple
  `< β^ℓ`, hence 0) pins β2 to the midpoint value.

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

end LeanFlocq
