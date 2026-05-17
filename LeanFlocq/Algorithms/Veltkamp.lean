/-
Veltkamp's splitting: an error-free decomposition `x = hx + tx` using only
three rounded operations applied to a splitting constant `C = β^s + 1`.

Following Coq Flocq's `Pff/Pff2Flocq.v` section `Veltkamp`, the algorithm is

  C  := β^s + 1
  p  := round(x · C)
  q  := round(x − p)
  hx := round(q + p)
  tx := round(x − hx)

The Pff statements are at FLT (gradual underflow). We mirror Fast2Sum's path:
build the keystone at FLX (no underflow) first, then lift to FLT in a follow-up.

Current contents:
- `Veltkamp_C_format` (FLT) — `C ∈ F`, matching the FLT statement.
- `mag_xC_bounds` (FLX/generic) — `mag(x) + s ≤ mag(x·C) ≤ mag(x) + s + 1`.

TODO (FLX first, then port to FLT):
- `Veltkamp_aux_FLX`  — keystone bound `|x − hx| ≤ β^(s+cexp x)/2` + `hx ∈ F(prec − s)`.
- `Veltkamp_FLX`      — ∃ `choice'`, `hx = round_{prec − s, choice'} x`.
- `Veltkamp_tail_FLX` — `x = hx + tx` and `tx ∈ FLX_s`.
- FLT lifts of all three.
- `Veltkamp_Even`     — with round-to-nearest-even, the equality holds.
-/
import LeanFlocq.Core.FLT
import LeanFlocq.Prop.Sterbenz
import LeanFlocq.Prop.Mult_error

namespace LeanFlocq

/-- The Veltkamp splitting constant `C = β^s + 1` is in FLT format whenever
`0 ≤ s`, `s + 1 < prec`, and `emin ≤ 0`. Mirrors Coq's `C_format` from
`Pff/Pff2Flocq.v` (lines 354–379). -/
theorem Veltkamp_C_format (beta : radix) (emin prec s : ℤ)
    (hp : 0 < prec) (hs_lo : 0 ≤ s) (hs_hi : s + 1 < prec)
    (hemin : emin ≤ 0) :
    generic_format beta (FLT_exp emin prec) (bpow beta s + 1) := by
  apply generic_format_FLT beta emin prec hp
  refine ⟨⟨(beta.val : ℤ) ^ s.toNat + 1, 0⟩, ?_, ?_, ?_⟩
  · -- β^s + 1 = F2R⟨β^s.toNat + 1, 0⟩
    show bpow beta s + 1
           = (((((beta.val : ℤ) ^ s.toNat + 1 : ℤ) : ℝ)) * bpow beta 0)
    rw [bpow_zero, mul_one, Int.cast_add, Int.cast_one, IZR_Zpower beta hs_lo]
  · -- |β^s.toNat + 1| < β^prec.toNat
    have hbeta_ge_2 : (2 : ℤ) ≤ beta.val := beta.prop
    have hbeta_pos : (0 : ℤ) < beta.val := by linarith
    -- 1 ≤ β^s
    have hpow_s_pos : (1 : ℤ) ≤ beta.val ^ s.toNat := by
      have : (1 : ℤ) = 1 ^ s.toNat := (one_pow _).symm
      rw [this]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hpow_s_nonneg : (0 : ℤ) ≤ beta.val ^ s.toNat := by linarith
    -- β^s + 1 ≥ 1 > 0, so |β^s + 1| = β^s + 1
    have hC_pos : (0 : ℤ) < beta.val ^ s.toNat + 1 := by linarith
    rw [abs_of_pos hC_pos]
    -- Aim: β^s + 1 < β^prec. Use β^s + 1 ≤ 2·β^s ≤ β·β^s = β^(s+1) < β^prec.
    have h_two_pow_s : (2 : ℤ) * beta.val ^ s.toNat ≤ beta.val ^ (s.toNat + 1) := by
      rw [pow_succ]; nlinarith
    have h_succ_le : (s.toNat + 1 : ℕ) ≤ prec.toNat - 1 + 1 := by
      have : s + 1 ≤ prec - 1 := by linarith
      have hpr_nat : (prec.toNat : ℤ) = prec := Int.toNat_of_nonneg (le_of_lt hp)
      have hsn_nat : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs_lo
      -- s.toNat + 1 ≤ prec.toNat
      have hle : s.toNat + 1 ≤ prec.toNat := by
        have h_le_int : (s.toNat : ℤ) + 1 ≤ (prec.toNat : ℤ) := by
          rw [hsn_nat, hpr_nat]; linarith
        exact_mod_cast h_le_int
      have hpge1 : 1 ≤ prec.toNat := by
        have : (1 : ℤ) ≤ (prec.toNat : ℤ) := by rw [hpr_nat]; linarith
        exact_mod_cast this
      omega
    have h_succ_lt : s.toNat + 1 < prec.toNat := by
      have : (s.toNat : ℤ) + 1 < (prec.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt hp), Int.toNat_of_nonneg hs_lo]
        linarith
      exact_mod_cast this
    have h_pow_mono : beta.val ^ (s.toNat + 1) < beta.val ^ prec.toNat := by
      apply pow_lt_pow_right₀
      · linarith
      · exact h_succ_lt
    linarith
  · -- emin ≤ 0
    exact hemin

/-! ### Magnitude of `x · C`

For `C = β^s + 1` and `x ≠ 0`, the magnitude of `x · C` is in
`{mag(x) + s, mag(x) + s + 1}`. The lower bound uses `β^s ≤ C`; the upper
bound uses `C < β^(s+1)` (which needs `s ≥ 0`, since for `s = 0`,
`C = 2 ≤ β` only when `β = 2`; we keep it generic via `1 ≤ s`). -/

/-- Magnitude bounds for `x · C` with `C = β^s + 1`, `s ≥ 1`, `x ≠ 0`:
`mag(x) + s ≤ mag(x · C) ≤ mag(x) + s + 1`. -/
private theorem mag_xC_bounds (beta : radix) {x : ℝ} {s : ℤ}
    (hx : x ≠ 0) (hs : 1 ≤ s) :
    mag beta x + s ≤ mag beta (x * (bpow beta s + 1))
      ∧ mag beta (x * (bpow beta s + 1)) ≤ mag beta x + s + 1 := by
  have hC_pos : 0 < bpow beta s + 1 := by linarith [bpow_gt_0 beta s]
  have hC_ne : bpow beta s + 1 ≠ 0 := ne_of_gt hC_pos
  -- bpow(s) ≥ β ≥ 2 > 1 for s ≥ 1.
  have h_pow_s_gt_1 : (1 : ℝ) < bpow beta s := by
    have : bpow beta 0 < bpow beta s := bpow_lt beta (by linarith : (0 : ℤ) < s)
    rwa [bpow_zero] at this
  have hβ : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  -- mag(C) bounds via |C| sandwich.
  have h_mag_C_lo : s + 1 ≤ mag beta (bpow beta s + 1) := by
    by_contra hlt
    push_neg at hlt
    have hmagle : mag beta (bpow beta s + 1) ≤ s := by linarith
    have h_high : |bpow beta s + 1| < bpow beta (mag beta (bpow beta s + 1)) :=
      bpow_mag_gt beta (bpow beta s + 1)
    have : |bpow beta s + 1| < bpow beta s :=
      lt_of_lt_of_le h_high (bpow_le beta hmagle)
    rw [abs_of_pos hC_pos] at this; linarith
  have h_mag_C_hi : mag beta (bpow beta s + 1) ≤ s + 1 := by
    apply mag_le_bpow beta hC_ne
    rw [abs_of_pos hC_pos, bpow_plus, bpow_one]
    nlinarith [bpow_ge_0 beta s, h_pow_s_gt_1]
  have h_mult := mag_mult beta hx hC_ne
  refine ⟨?_, ?_⟩
  · linarith [h_mult.1]
  · linarith [h_mult.2]

end LeanFlocq
