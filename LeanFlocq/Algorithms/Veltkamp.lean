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

/-! ### FLX algorithm constants

We name the algorithm steps for the FLX (no underflow) version. The keystone
will refer to these by name across multiple theorems. Mirrors the section
`Veltkamp` in `Pff2Flocq.v` (lines 323–350). -/

/-- Veltkamp splitting constant: `C = β^s + 1`. -/
noncomputable def Veltkamp_C (beta : radix) (s : ℤ) : ℝ := bpow beta s + 1

/-- Step 1 of the algorithm: `p = round(x · C)`. -/
noncomputable def Veltkamp_p_FLX (beta : radix) (prec : ℤ) (choice : ℤ → Bool)
    (s : ℤ) (x : ℝ) : ℝ :=
  round beta (FLX_exp prec) (Znearest choice) (x * Veltkamp_C beta s)

/-- Step 2: `q = round(x − p)`. -/
noncomputable def Veltkamp_q_FLX (beta : radix) (prec : ℤ) (choice : ℤ → Bool)
    (s : ℤ) (x : ℝ) : ℝ :=
  round beta (FLX_exp prec) (Znearest choice)
    (x - Veltkamp_p_FLX beta prec choice s x)

/-- Step 3: `hx = round(q + p)`, the "high part" of the splitting. -/
noncomputable def Veltkamp_hx_FLX (beta : radix) (prec : ℤ) (choice : ℤ → Bool)
    (s : ℤ) (x : ℝ) : ℝ :=
  round beta (FLX_exp prec) (Znearest choice)
    (Veltkamp_q_FLX beta prec choice s x + Veltkamp_p_FLX beta prec choice s x)

/-- Step 4: `tx = round(x − hx)`, the "tail" / low part. -/
noncomputable def Veltkamp_tx_FLX (beta : radix) (prec : ℤ) (choice : ℤ → Bool)
    (s : ℤ) (x : ℝ) : ℝ :=
  round beta (FLX_exp prec) (Znearest choice)
    (x - Veltkamp_hx_FLX beta prec choice s x)

/-- The FLX-form C is in F (FLX, prec) when `0 ≤ s` and `s + 1 < prec`. -/
theorem Veltkamp_C_format_FLX (beta : radix) (prec s : ℤ)
    (hs_lo : 0 ≤ s) (hs_hi : s + 1 < prec) :
    generic_format beta (FLX_exp prec) (Veltkamp_C beta s) := by
  unfold Veltkamp_C
  have hC_pos : 0 < bpow beta s + 1 := by linarith [bpow_gt_0 beta s]
  have hC_ne : bpow beta s + 1 ≠ 0 := ne_of_gt hC_pos
  have hβ : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have h_pow_s_ge_1 : (1 : ℝ) ≤ bpow beta s := by
    rw [← bpow_zero beta]; exact bpow_le beta hs_lo
  refine generic_format_F2R' beta (FLX_exp prec)
    (⟨(beta.val : ℤ) ^ s.toNat + 1, 0⟩ : float beta) ?_ ?_
  · -- F2R⟨β^s + 1, 0⟩ = β^s + 1
    show ((((beta.val : ℤ) ^ s.toNat + 1 : ℤ) : ℝ) * bpow beta 0)
           = bpow beta s + 1
    rw [bpow_zero, mul_one, Int.cast_add, Int.cast_one, IZR_Zpower beta hs_lo]
  · -- cexp(C) ≤ 0. Suffices mag(C) ≤ prec, which follows from |C| < β^prec.
    intro _
    show cexp beta (FLX_exp prec) (bpow beta s + 1) ≤ 0
    have h_C_lt : |bpow beta s + 1| < bpow beta prec := by
      rw [abs_of_pos hC_pos]
      -- β^s + 1 ≤ 2·β^s ≤ β·β^s = β^(s+1) ≤ β^(prec-1) < β^prec.
      have h1 : bpow beta s + 1 ≤ 2 * bpow beta s := by linarith
      have h2 : 2 * bpow beta s ≤ (beta.val : ℝ) * bpow beta s := by nlinarith
      have h3 : (beta.val : ℝ) * bpow beta s = bpow beta (s + 1) := by
        rw [bpow_plus, bpow_one]; ring
      have h4 : bpow beta (s + 1) ≤ bpow beta (prec - 1) :=
        bpow_le beta (by linarith)
      have h5 : bpow beta (prec - 1) < bpow beta prec :=
        bpow_lt beta (by linarith)
      linarith
    have h_mag_le : mag beta (bpow beta s + 1) ≤ prec :=
      mag_le_bpow beta hC_ne h_C_lt
    show FLX_exp prec (mag beta (bpow beta s + 1)) ≤ 0
    unfold FLX_exp; linarith

/-! ### Polarity facts for the FLX algorithm

For `x > 0`, the rounded results have predictable signs: `p ≥ 0`, `q ≤ 0`,
and `x ≤ p`. These will feed the Sterbenz argument for `hx = p + q`. -/

/-- For `x > 0` and `s ≥ 0`, the constant `C = β^s + 1 ≥ 1`. -/
private theorem Veltkamp_one_le_C (beta : radix) {s : ℤ} (hs : 0 ≤ s) :
    1 ≤ Veltkamp_C beta s := by
  unfold Veltkamp_C
  have : (1 : ℝ) ≤ bpow beta s := by
    rw [← bpow_zero beta]; exact bpow_le beta hs
  linarith

/-- For `x > 0` and `s ≥ 0`, step-1 result is nonneg: `0 ≤ p`. -/
private theorem Veltkamp_p_nonneg_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    0 ≤ Veltkamp_p_FLX beta prec choice s x := by
  unfold Veltkamp_p_FLX
  have h_prod_nn : 0 ≤ x * Veltkamp_C beta s :=
    mul_nonneg (le_of_lt hx_pos) (by linarith [Veltkamp_one_le_C beta hs])
  exact round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
    (generic_format_0 beta _) h_prod_nn

/-- For `x ∈ F` with `x > 0` and `s ≥ 0`: `x ≤ p`. (Comes from monotonicity
of `round` plus `round x = x` since `x ∈ F`.) -/
private theorem Veltkamp_x_le_p_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    x ≤ Veltkamp_p_FLX beta prec choice s x := by
  unfold Veltkamp_p_FLX
  have hC_ge_1 : 1 ≤ Veltkamp_C beta s := Veltkamp_one_le_C beta hs
  have h_x_le_xC : x ≤ x * Veltkamp_C beta s := by
    have := mul_le_mul_of_nonneg_left hC_ge_1 (le_of_lt hx_pos)
    linarith
  exact round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
    Fx h_x_le_xC

/-- For `x ∈ F` with `x > 0` and `s ≥ 0`: `q ≤ 0`. -/
private theorem Veltkamp_q_nonpos_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    Veltkamp_q_FLX beta prec choice s x ≤ 0 := by
  unfold Veltkamp_q_FLX
  have h_xmp_nonpos : x - Veltkamp_p_FLX beta prec choice s x ≤ 0 := by
    linarith [Veltkamp_x_le_p_FLX beta prec hp choice Fx hx_pos hs]
  exact round_le_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
    (generic_format_0 beta _) h_xmp_nonpos

end LeanFlocq
