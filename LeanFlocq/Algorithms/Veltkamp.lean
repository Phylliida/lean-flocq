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
import LeanFlocq.Core.Round_NE
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

/-! ### Sterbenz upper bound for `hxExact`

For `2 ≤ s ≤ prec − 2`, `β ≥ 2`, and `x > 0`: `p ≤ −2q`. Combined with
the trivial lower bound `−q ≤ p` (from polarity + monotonicity), this is
the input to Sterbenz on `(p, −q)` giving `p + q ∈ F`. -/

/-- The Sterbenz lower bound: `-q ≤ p`. For `x ∈ F`, `x > 0`. Comes from
`round(x - p) ≥ round(-p) = -p` since `-p ≤ x - p` and `-p ∈ F`. -/
private theorem Veltkamp_neg_q_le_p_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (_Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    -Veltkamp_q_FLX beta prec choice s x ≤ Veltkamp_p_FLX beta prec choice s x := by
  have hp_nn : 0 ≤ Veltkamp_p_FLX beta prec choice s x :=
    Veltkamp_p_nonneg_FLX beta prec hp choice hx_pos hs
  have Fp : generic_format beta (FLX_exp prec) (Veltkamp_p_FLX beta prec choice s x) :=
    generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice)
      (x * Veltkamp_C beta s)
  have F_neg_p :
      generic_format beta (FLX_exp prec) (-Veltkamp_p_FLX beta prec choice s x) :=
    generic_format_opp beta _ Fp
  unfold Veltkamp_q_FLX
  have h_neg_p_le : -Veltkamp_p_FLX beta prec choice s x
                  ≤ x - Veltkamp_p_FLX beta prec choice s x := by linarith
  have h_q_ge_neg_p :
      -Veltkamp_p_FLX beta prec choice s x
        ≤ round beta (FLX_exp prec) (Znearest choice)
            (x - Veltkamp_p_FLX beta prec choice s x) :=
    round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _ F_neg_p h_neg_p_le
  linarith

/-- Mag bound: `mag(x·C) ≤ mag(x) + s + 1`, the upper bound from `mag_xC_bounds`. -/
private theorem Veltkamp_mag_xC_le (beta : radix) {x : ℝ} {s : ℤ}
    (hx_ne : x ≠ 0) (hs : 1 ≤ s) :
    mag beta (x * Veltkamp_C beta s) ≤ mag beta x + s + 1 := by
  unfold Veltkamp_C
  exact (mag_xC_bounds beta hx_ne hs).2

/-- Key auxiliary: the algebraic identity `x − p = −x·β^s − err_p` and a bound
on `|x − p|`, leading to `|x − p| < β^(mag x + s + 1)`. -/
private theorem Veltkamp_abs_x_minus_p_lt_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (hx_pos : 0 < x) (hs_lo : 1 ≤ s) (hs_hi : s + 2 ≤ prec) :
    |x - Veltkamp_p_FLX beta prec choice s x|
      < bpow beta (mag beta x + s + 1) := by
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set m := mag beta x with hm_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hC : Veltkamp_C beta s = bpow beta s + 1 := rfl
  have hxC_ne : x * Veltkamp_C beta s ≠ 0 := by
    have : 0 < Veltkamp_C beta s := by
      unfold Veltkamp_C; linarith [bpow_gt_0 beta s]
    have : 0 < x * Veltkamp_C beta s := mul_pos hx_pos this
    linarith
  -- |err_p| = |p - x·C| ≤ bpow(cexp(x·C))/2 ≤ bpow(m + s + 1 - prec)/2.
  have h_p_eq : p = round beta (FLX_exp prec) (Znearest choice)
                      (x * Veltkamp_C beta s) := rfl
  have h_err_p : |p - x * Veltkamp_C beta s|
                  ≤ bpow beta (mag beta (x * Veltkamp_C beta s) - prec) / 2 := by
    rw [h_p_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                (x * Veltkamp_C beta s)
    rw [ulp_neq_0 beta _ hxC_ne] at h
    have h_cexp : cexp beta (FLX_exp prec) (x * Veltkamp_C beta s)
                = mag beta (x * Veltkamp_C beta s) - prec := rfl
    rw [h_cexp] at h
    linarith
  -- bpow(mag(x·C) - prec) ≤ bpow(m + s + 1 - prec)
  have h_mag_xC : mag beta (x * Veltkamp_C beta s) ≤ m + s + 1 :=
    Veltkamp_mag_xC_le beta hx_ne hs_lo
  have h_err_p_bound : |p - x * Veltkamp_C beta s|
                        ≤ bpow beta (m + s + 1 - prec) / 2 := by
    have hbpow_le : bpow beta (mag beta (x * Veltkamp_C beta s) - prec)
                    ≤ bpow beta (m + s + 1 - prec) :=
      bpow_le beta (by linarith)
    have hge0 : 0 ≤ bpow beta (mag beta (x * Veltkamp_C beta s) - prec) :=
      bpow_ge_0 _ _
    linarith
  -- x - p = -x·β^s - err_p, so |x - p| ≤ x·β^s + |err_p|.
  have h_xmp_eq : x - p = -(x * bpow beta s) - (p - x * Veltkamp_C beta s) := by
    rw [hC]; ring
  have h_xmp_abs : |x - p| ≤ x * bpow beta s + bpow beta (m + s + 1 - prec) / 2 := by
    rw [h_xmp_eq]
    have h_tri : |-(x * bpow beta s) - (p - x * Veltkamp_C beta s)|
                  ≤ |x * bpow beta s| + |p - x * Veltkamp_C beta s| := by
      rw [show -(x * bpow beta s) - (p - x * Veltkamp_C beta s)
            = -(x * bpow beta s + (p - x * Veltkamp_C beta s)) from by ring]
      rw [abs_neg]
      exact abs_add_le _ _
    have h_xbs_abs : |x * bpow beta s| = x * bpow beta s := by
      apply abs_of_pos
      exact mul_pos hx_pos (bpow_gt_0 beta s)
    linarith
  -- x·β^s < bpow(m + s).
  have h_x_lt : x < bpow beta m := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos hx_pos] at this
  have h_xbs_lt : x * bpow beta s < bpow beta (m + s) := by
    rw [show (m + s : ℤ) = s + m from by ring, bpow_plus]
    have hbs_pos : 0 < bpow beta s := bpow_gt_0 beta s
    calc x * bpow beta s = bpow beta s * x := by ring
      _ < bpow beta s * bpow beta m := by
          exact (mul_lt_mul_iff_of_pos_left hbs_pos).mpr h_x_lt
  -- bpow(m + s + 1 - prec)/2 ≤ bpow(m + s)/(2β^(prec - s - 1)) ≤ bpow(m + s)
  --   (since prec - s - 1 ≥ 1, so β^(prec - s - 1) ≥ 2).
  -- Actually simpler: bpow(m + s + 1 - prec)/2 ≤ bpow(m + s)/2 (since 1 - prec ≤ -1 ≤ 0).
  have h_err_bound2 : bpow beta (m + s + 1 - prec) / 2 ≤ bpow beta (m + s) / 2 := by
    have : bpow beta (m + s + 1 - prec) ≤ bpow beta (m + s) :=
      bpow_le beta (by linarith)
    linarith
  -- |x - p| ≤ x·β^s + bpow(m+s)/2 < bpow(m+s) + bpow(m+s)/2 = (3/2) bpow(m+s).
  have h_xmp_lt_15 : |x - p| < bpow beta (m + s) * (3 / 2) := by
    have hge0 : 0 ≤ bpow beta (m + s) := bpow_ge_0 _ _
    linarith
  -- (3/2) bpow(m+s) ≤ bpow(m+s+1) (since β ≥ 2 and (3/2)·1 ≤ β).
  have h_bpow_succ : bpow beta (m + s + 1) = (beta.val : ℝ) * bpow beta (m + s) := by
    rw [show (m + s + 1 : ℤ) = (m + s) + 1 from by ring, bpow_plus, bpow_one]; ring
  have h_15_le_succ : bpow beta (m + s) * (3 / 2) ≤ bpow beta (m + s + 1) := by
    rw [h_bpow_succ]
    have hge0 : 0 ≤ bpow beta (m + s) := bpow_ge_0 _ _
    have : 3 / 2 ≤ (beta.val : ℝ) := by linarith
    nlinarith
  linarith

/-- The Sterbenz upper bound: `p ≤ −2q`. For `2 ≤ s ≤ prec − 2`, `x > 0`, `x ∈ F`.
The bound `p ≥ 2x + ulp(x − p)` (derived from `p ≥ x·C − ulp(x·C)/2` and
`x·(β^s − 1) ≥ (3/2) bpow(m + s + 1 − prec)`) closes via the half-ulp bound on
`q = round(x − p)`. -/
private theorem Veltkamp_p_le_neg_2q_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (_Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    Veltkamp_p_FLX beta prec choice s x
      ≤ -2 * Veltkamp_q_FLX beta prec choice s x := by
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set m := mag beta x with hm_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  -- Step 1: |x - p| < bpow(m + s + 1).
  have h_abs_xmp : |x - p|
                  < bpow beta (m + s + 1) :=
    Veltkamp_abs_x_minus_p_lt_FLX beta prec hp choice hx_pos (by linarith) hs_hi
  -- Step 2: |err_q| = |q - (x - p)| ≤ ulp(x - p)/2 ≤ bpow(m + s + 1 - prec)/2.
  -- We use error_le_half_ulp on (x - p) for q = round(x - p).
  have h_err_q : |Veltkamp_q_FLX beta prec choice s x - (x - p)|
                  ≤ bpow beta (m + s + 1 - prec) / 2 := by
    have h_q_eq : Veltkamp_q_FLX beta prec choice s x
                = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
    rw [h_q_eq]
    by_cases h_xmp_zero : x - p = 0
    · rw [h_xmp_zero, round_0, sub_zero, abs_zero]
      have := bpow_ge_0 beta (m + s + 1 - prec)
      linarith
    · have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice (x - p)
      rw [ulp_neq_0 beta _ h_xmp_zero] at h
      have h_cexp : cexp beta (FLX_exp prec) (x - p)
                  = mag beta (x - p) - prec := rfl
      rw [h_cexp] at h
      have h_mag_xmp : mag beta (x - p) ≤ m + s + 1 :=
        mag_le_bpow beta h_xmp_zero h_abs_xmp
      have h_bpow_mag_le : bpow beta (mag beta (x - p) - prec)
                          ≤ bpow beta (m + s + 1 - prec) :=
        bpow_le beta (by linarith)
      have hge0 : 0 ≤ bpow beta (mag beta (x - p) - prec) := bpow_ge_0 _ _
      linarith
  -- Step 3: |err_p| ≤ bpow(m + s + 1 - prec)/2 (same bound as in abs_x_minus_p_lt).
  -- Combine for p ≥ x·C - bpow(m+s+1-prec)/2.
  have hxC_ne : x * Veltkamp_C beta s ≠ 0 := by
    have : 0 < Veltkamp_C beta s := by
      unfold Veltkamp_C; linarith [bpow_gt_0 beta s]
    have : 0 < x * Veltkamp_C beta s := mul_pos hx_pos this
    linarith
  have h_err_p : |p - x * Veltkamp_C beta s|
                  ≤ bpow beta (m + s + 1 - prec) / 2 := by
    have h_p_eq : p = round beta (FLX_exp prec) (Znearest choice)
                       (x * Veltkamp_C beta s) := rfl
    rw [h_p_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                (x * Veltkamp_C beta s)
    rw [ulp_neq_0 beta _ hxC_ne] at h
    have h_cexp : cexp beta (FLX_exp prec) (x * Veltkamp_C beta s)
                = mag beta (x * Veltkamp_C beta s) - prec := rfl
    rw [h_cexp] at h
    have h_mag_xC_le : mag beta (x * Veltkamp_C beta s) ≤ m + s + 1 :=
      Veltkamp_mag_xC_le beta hx_ne (by linarith)
    have h_bpow_le : bpow beta (mag beta (x * Veltkamp_C beta s) - prec)
                    ≤ bpow beta (m + s + 1 - prec) :=
      bpow_le beta (by linarith)
    have hge0 : 0 ≤ bpow beta (mag beta (x * Veltkamp_C beta s) - prec) :=
      bpow_ge_0 _ _
    linarith
  -- Step 4: p ≥ x·(β^s + 1) - bpow(m+s+1-prec)/2 from h_err_p.
  -- Algebra: |p - x*C| ≤ E means p ≥ x*C - E.
  have h_p_lower : p ≥ x * (bpow beta s + 1) - bpow beta (m + s + 1 - prec) / 2 := by
    have h_abs := abs_le.mp h_err_p
    -- h_abs.1 : -(bpow .../2) ≤ p - x * Veltkamp_C beta s
    have : p - x * Veltkamp_C beta s ≥ -(bpow beta (m + s + 1 - prec) / 2) := h_abs.1
    rw [hC_eq] at this
    linarith
  -- Step 5: -q ≥ (p - x) - bpow(m + s + 1 - prec)/2 from h_err_q.
  have h_neg_q_lower : -Veltkamp_q_FLX beta prec choice s x
                          ≥ (p - x) - bpow beta (m + s + 1 - prec) / 2 := by
    have h_abs := abs_le.mp h_err_q
    -- h_abs.2 : Veltkamp_q - (x - p) ≤ bpow(...)/2
    have : Veltkamp_q_FLX beta prec choice s x - (x - p)
            ≤ bpow beta (m + s + 1 - prec) / 2 := h_abs.2
    linarith
  -- Step 6: Combine. Want p ≤ -2q.
  -- From h_p_lower: p ≥ x·(β^s + 1) - E/2 where E := bpow(m+s+1-prec).
  -- From h_neg_q_lower: -2q ≥ 2(p - x) - E.
  -- Want p ≤ -2q ⟺ p ≤ 2p - 2x - E ⟺ 2x + E ≤ p.
  -- Sufficient: 2x + E ≤ x·(β^s + 1) - E/2 ⟺ x·(β^s - 1) ≥ (3/2) E.
  -- Suffices: x · (β^s - 1) ≥ (3/2) · bpow(m+s+1-prec).
  have hE_def : True := trivial  -- E := bpow(m+s+1-prec)
  -- x ≥ bpow(m-1) since x > 0 in F has mag = m.
  have h_x_ge : bpow beta (m - 1) ≤ x := by
    have := bpow_mag_le beta hx_ne
    rwa [abs_of_pos hx_pos] at this
  -- bpow(m+s+1-prec) ≤ bpow(m - 1) (since s + 1 - prec ≤ -1 ⟺ s ≤ prec - 2).
  have h_bpow_E_le_x : bpow beta (m + s + 1 - prec) ≤ bpow beta (m - 1) :=
    bpow_le beta (by linarith)
  have h_bpow_E_le_x2 : bpow beta (m + s + 1 - prec) ≤ x :=
    le_trans h_bpow_E_le_x h_x_ge
  -- (3/2) · bpow(m+s+1-prec) ≤ (3/2) · x.
  have h_32E_le_32x : (3 / 2) * bpow beta (m + s + 1 - prec) ≤ (3 / 2) * x := by
    have : 0 ≤ (3 / 2 : ℝ) := by norm_num
    nlinarith
  -- x · (β^s - 1) ≥ x · (5/2 - 1) = (3/2) · x when β^s ≥ 5/2.
  -- For s ≥ 2, β ≥ 2: β^s ≥ 4 ≥ 5/2.
  have h_bpow_s_ge : (4 : ℝ) ≤ bpow beta s := by
    have h_pow2_ge_4 : (4 : ℝ) ≤ bpow beta 2 := by
      have h_bpow2 : bpow beta 2 = (beta.val : ℝ) * (beta.val : ℝ) := by
        rw [show (2 : ℤ) = 1 + 1 from rfl, bpow_plus, bpow_one]
      rw [h_bpow2]
      nlinarith
    exact le_trans h_pow2_ge_4 (bpow_le beta hs_lo)
  have h_β_s_sub_1 : bpow beta s - 1 ≥ 3 := by linarith
  have h_x_times : x * (bpow beta s - 1) ≥ x * 3 := by
    have : x * (bpow beta s - 1) ≥ x * 3 := by nlinarith
    exact this
  -- 3x ≥ (3/2) · bpow(m+s+1-prec).
  have h_3x_ge_32E : x * 3 ≥ (3 / 2) * bpow beta (m + s + 1 - prec) := by
    have h_2x_ge_E : 2 * x ≥ bpow beta (m + s + 1 - prec) := by
      have : 2 * x ≥ 2 * bpow beta (m + s + 1 - prec) := by nlinarith
      have hE_le_x : bpow beta (m + s + 1 - prec) ≤ x := h_bpow_E_le_x2
      linarith
    linarith
  -- Conclude x·(β^s - 1) ≥ (3/2) · bpow(m+s+1-prec).
  have h_key : x * (bpow beta s - 1) ≥ (3 / 2) * bpow beta (m + s + 1 - prec) := by
    linarith
  -- Final assembly.
  -- p ≥ x·(β^s + 1) - E/2 = x·β^s + x - E/2.
  -- 2x + E ≤ p when x·(β^s - 1) ≥ (3/2) E.
  -- p ≥ x·β^s + x - E/2.
  -- We want p ≥ 2x + E, equivalently x·β^s + x - E/2 ≥ 2x + E,
  -- equivalently x·β^s ≥ x + (3/2) E, equivalently x·(β^s - 1) ≥ (3/2) E. ✓
  have h_p_ge_2x_E : p ≥ 2 * x + bpow beta (m + s + 1 - prec) := by
    have : x * (bpow beta s + 1) = x * (bpow beta s - 1) + 2 * x := by ring
    have h1 := h_p_lower
    rw [show x * (bpow beta s + 1) - bpow beta (m + s + 1 - prec) / 2
          = (x * (bpow beta s - 1) + 2 * x) - bpow beta (m + s + 1 - prec) / 2 from by ring]
      at h1
    linarith
  -- Now p ≤ -2q from p ≤ 2(p - x) - E (which is -2q ≥ 2(p - x) - E from h_neg_q_lower).
  have h_neg_2q_ge : -2 * Veltkamp_q_FLX beta prec choice s x
                    ≥ 2 * (p - x) - bpow beta (m + s + 1 - prec) := by
    have := h_neg_q_lower
    nlinarith
  linarith

/-! ### `x ≤ β^(mag x) − β^(cexp x)` — the F upper-bound lemma

A normal `x ∈ F(FLX, prec)` has integer mantissa at exponent `cexp(x)` bounded
by `β^prec − 1`, so `x ≤ (β^prec − 1) · β^cexp(x) = β^(mag x) − β^cexp(x)`.
This is just the `F2R_p1_le_bpow` lemma applied at the canonical exponent. -/
private theorem F_le_bpow_minus_bpow_cexp (beta : radix) (prec : ℤ)
    {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) :
    x + bpow beta (cexp beta (FLX_exp prec) x) ≤ bpow beta (mag beta x) := by
  set mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hmx_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hx_eq : x = F2R (beta := beta) ⟨mx, cx⟩ := Fx
  have hmx_pos : 0 < mx := by
    apply gt_0_F2R (beta := beta) (e := cx)
    rw [← hx_eq]; exact hx_pos
  have h_x_lt : x < bpow beta (mag beta x) := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos hx_pos] at this
  have h_F2R_lt : F2R (beta := beta) ⟨mx, cx⟩ < bpow beta (mag beta x) := by
    rw [← hx_eq]; exact h_x_lt
  have h_F2R_p1 : F2R (beta := beta) ⟨mx + 1, cx⟩ ≤ bpow beta (mag beta x) :=
    F2R_p1_le_bpow hmx_pos h_F2R_lt
  -- F2R⟨mx + 1, cx⟩ = x + β^cx.
  have h_F2R_eq : F2R (beta := beta) ⟨mx + 1, cx⟩
                = x + bpow beta cx := by
    show ((mx + 1 : ℤ) : ℝ) * bpow beta cx = x + bpow beta cx
    have hx_eq' : x = (mx : ℝ) * bpow beta cx := hx_eq
    push_cast; linarith
  linarith

/-- **hxExact at FLX**: `hx = p + q` exactly. Under FLX with `2 ≤ s ≤ prec − 2`
and `x > 0`, `q + p ∈ F` by Sterbenz on `(p, −q)`, so the third rounding step is
the identity. (Pff `hxExact`, line 13147 of `Pff.v`.) -/
theorem hxExact_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    Veltkamp_hx_FLX beta prec choice s x
      = Veltkamp_q_FLX beta prec choice s x + Veltkamp_p_FLX beta prec choice s x := by
  unfold Veltkamp_hx_FLX
  apply round_generic
  have Fp : generic_format beta (FLX_exp prec) (Veltkamp_p_FLX beta prec choice s x) :=
    generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) _ _
  have Fq : generic_format beta (FLX_exp prec) (Veltkamp_q_FLX beta prec choice s x) :=
    generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) _ _
  have Fnq : generic_format beta (FLX_exp prec) (-Veltkamp_q_FLX beta prec choice s x) :=
    generic_format_opp beta _ Fq
  have h_lower := Veltkamp_neg_q_le_p_FLX beta prec hp choice Fx hx_pos (by linarith)
  have h_upper := Veltkamp_p_le_neg_2q_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_qp_eq : Veltkamp_q_FLX beta prec choice s x
                  + Veltkamp_p_FLX beta prec choice s x
              = Veltkamp_p_FLX beta prec choice s x
                  - (-Veltkamp_q_FLX beta prec choice s x) := by ring
  rw [h_qp_eq]
  apply sterbenz_aux beta (FLX_exp prec) (FLX_exp_valid prec hp) (FLX_exp_monotone prec)
    Fp Fnq
  refine ⟨h_lower, ?_⟩
  linarith

/-! ### Case A of `Veltkamp_aux_FLX`

When `mag(x · C) = mag(x) + s`, the `|err_p|` bound is at the tighter exponent
`m + s − prec`, so `|x − p|` stays under `β^(m+s)` and `cexp(q) ≤ s + cexp(x)`,
giving `|x − hx| = |err_q| ≤ β^(s + cexp x)/2` directly.

(Case B — when `mag(x · C) = mag(x) + s + 1` — needs the structural integer-
mantissa argument from Pff and is deferred.) -/

/-- **Veltkamp_aux_FLX, Case A**: when the multiplication step doesn't push
the magnitude up by an extra `1`, the `|x − hx|` bound holds via the half-ulp
argument plus an algebraic bound on `|x − p|`. -/
theorem Veltkamp_aux_FLX_CaseA (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_caseA : mag beta (x * Veltkamp_C beta s) = mag beta x + s) :
    |x - Veltkamp_hx_FLX beta prec choice s x|
      ≤ bpow beta (s + cexp beta (FLX_exp prec) x) / 2 := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  -- Step 1: hxExact gives x - hx = -(q - (x - p)).
  have h_hxExact : Veltkamp_hx_FLX beta prec choice s x = q + p :=
    hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_x_minus_hx : x - Veltkamp_hx_FLX beta prec choice s x
                    = -(q - (x - p)) := by rw [h_hxExact]; ring
  rw [h_x_minus_hx, abs_neg]
  -- Step 2: |err_p| ≤ β^(m + s - prec)/2 (using Case A's mag equality).
  have hxC_pos : 0 < x * Veltkamp_C beta s := by
    apply mul_pos hx_pos
    unfold Veltkamp_C; linarith [bpow_gt_0 beta s]
  have hxC_ne : x * Veltkamp_C beta s ≠ 0 := ne_of_gt hxC_pos
  have h_err_p : |p - x * Veltkamp_C beta s|
                  ≤ bpow beta (m + s - prec) / 2 := by
    have h_p_eq : p = round beta (FLX_exp prec) (Znearest choice)
                       (x * Veltkamp_C beta s) := rfl
    rw [h_p_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                (x * Veltkamp_C beta s)
    rw [ulp_neq_0 beta _ hxC_ne] at h
    have h_cexp : cexp beta (FLX_exp prec) (x * Veltkamp_C beta s)
                = mag beta (x * Veltkamp_C beta s) - prec := rfl
    rw [h_cexp, h_caseA] at h
    linarith
  -- Step 3: x ≤ β^m - β^cx (F upper bound).
  have h_x_F_bound : x + bpow beta cx ≤ bpow beta m :=
    F_le_bpow_minus_bpow_cexp beta prec Fx hx_pos
  have h_x_le : x ≤ bpow beta m - bpow beta cx := by
    have := bpow_ge_0 beta cx; linarith
  -- Step 4: x·β^s ≤ β^(m+s) - β^(m+s-prec).
  have h_xbs_le : x * bpow beta s ≤ bpow beta (m + s) - bpow beta (m + s - prec) := by
    have hbs_pos : 0 < bpow beta s := bpow_gt_0 beta s
    have h_mul : x * bpow beta s ≤ (bpow beta m - bpow beta cx) * bpow beta s :=
      mul_le_mul_of_nonneg_right h_x_le (le_of_lt hbs_pos)
    have h_eq2 : bpow beta m * bpow beta s = bpow beta (m + s) := by
      rw [← bpow_plus]
    have h_eq3 : bpow beta cx * bpow beta s = bpow beta (m + s - prec) := by
      rw [← bpow_plus, hcx_eq]; congr 1; ring
    nlinarith
  -- Step 5: |x - p| ≤ β^(m+s) - β^(m+s-prec)/2.
  have h_xmp_eq : x - p = -(x * bpow beta s) - (p - x * Veltkamp_C beta s) := by
    rw [hC_eq]; ring
  have h_abs_xmp : |x - p|
                   ≤ bpow beta (m + s) - bpow beta (m + s - prec) / 2 := by
    rw [h_xmp_eq]
    have h_tri : |-(x * bpow beta s) - (p - x * Veltkamp_C beta s)|
                  ≤ |x * bpow beta s| + |p - x * Veltkamp_C beta s| := by
      rw [show -(x * bpow beta s) - (p - x * Veltkamp_C beta s)
            = -(x * bpow beta s + (p - x * Veltkamp_C beta s)) from by ring,
          abs_neg]
      exact abs_add_le _ _
    have h_xbs_abs : |x * bpow beta s| = x * bpow beta s :=
      abs_of_pos (mul_pos hx_pos (bpow_gt_0 beta s))
    linarith
  -- Step 6: |x - p| < β^(m+s) strict.
  have h_abs_xmp_lt : |x - p| < bpow beta (m + s) := by
    have hge0 : 0 < bpow beta (m + s - prec) := bpow_gt_0 _ _
    linarith
  -- Step 7: bound |err_q| via ulp(x - p)/2.
  by_cases h_xmp_zero : x - p = 0
  · -- x = p, q = 0, |err_q| = 0.
    have h_q_zero : q = 0 := by
      show round beta (FLX_exp prec) (Znearest choice) (x - p) = 0
      rw [h_xmp_zero]; exact round_0 _ _ _
    rw [h_q_zero, h_xmp_zero, sub_zero, abs_zero]
    have := bpow_ge_0 beta (s + cx); linarith
  · have h_mag_xmp : mag beta (x - p) ≤ m + s :=
      mag_le_bpow beta h_xmp_zero h_abs_xmp_lt
    have h_cexp_xmp_le : cexp beta (FLX_exp prec) (x - p) ≤ s + cx := by
      show mag beta (x - p) - prec ≤ s + cx
      rw [hcx_eq]; linarith
    have h_bpow_cexp_le : bpow beta (cexp beta (FLX_exp prec) (x - p))
                          ≤ bpow beta (s + cx) :=
      bpow_le beta h_cexp_xmp_le
    have h_err_q : |q - (x - p)| ≤ bpow beta (s + cx) / 2 := by
      have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
      rw [h_q_eq]
      have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                  (x - p)
      rw [ulp_neq_0 beta _ h_xmp_zero] at h
      linarith
    exact h_err_q

/-! ### Case B of `Veltkamp_aux_FLX`

When `mag(x · C) = mag(x) + s + 1`, the half-ulp argument on `q = round(x − p)`
gives only `|err_q| ≤ β · β^(s + cexp x)/2` — off by a factor of `β`. The Pff
fix (line 13313, `eqLe`) is a structural integer-mantissa argument: case-split
on `M_x ≤ β^prec − β − 1` (interior, most M_x values) vs
`M_x ≥ β^prec − β` (boundary, the top `β` values).

In the interior subcase, `(M_x + β) · β^(s + cexp x)` is in F at exponent
`s + cexp x`, and dominates `|q|` via `|x − p| ≤ x · β^s + ulp(p) ≤
M_x · β^(s+cexp x) + β · β^(s + cexp x)`. This forces `mag(q) ≤ m + s`,
hence `cexp(q) ≤ s + cexp(x)`, hence `|err_q| ≤ β^(s+cexp x)/2`.

The boundary subcase needs further analysis: either `q > -β^(s+m)`
(reducing to the interior argument with one more case) or `q = -β^(s+m)`
exactly (handled directly via a midpoint argument). -/

/-- **epLe** at FLX: `p ≤ x · β^(s+1)`. Pff line 13275. The key fact: `x · β^(s+1)`
is in F (it's `x` shifted by an integer power), and `x · C ≤ x · β^(s+1)` since
`C = β^s + 1 ≤ 2·β^s ≤ β·β^s`. So `p = round(x·C) ≤ round(x·β^(s+1)) = x·β^(s+1)`. -/
private theorem Veltkamp_p_le_xbeta_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    Veltkamp_p_FLX beta prec choice s x ≤ x * bpow beta (s + 1) := by
  unfold Veltkamp_p_FLX
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  -- x · C ≤ x · β^(s+1).
  have h_C_le : Veltkamp_C beta s ≤ bpow beta (s + 1) := by
    unfold Veltkamp_C
    rw [show (s + 1 : ℤ) = s + 1 from rfl, bpow_plus, bpow_one]
    have h_pow_s_ge : (1 : ℝ) ≤ bpow beta s := by
      rw [← bpow_zero beta]; exact bpow_le beta hs
    nlinarith [bpow_gt_0 beta s]
  have h_xC_le : x * Veltkamp_C beta s ≤ x * bpow beta (s + 1) :=
    mul_le_mul_of_nonneg_left h_C_le (le_of_lt hx_pos)
  -- x · β^(s+1) ∈ F.
  have h_F_xbeta : generic_format beta (FLX_exp prec) (x * bpow beta (s + 1)) := by
    -- x = M_x · β^cexp(x), so x · β^(s+1) = M_x · β^(s+1+cexp x). Both x and its shift use M_x.
    obtain ⟨f, hxf, hbf⟩ := FLX_format_generic beta prec hp Fx
    apply generic_format_FLX beta prec hp
    refine ⟨⟨f.Fnum, f.Fexp + (s + 1)⟩, ?_, ?_⟩
    · -- x · β^(s+1) = F2R⟨f.Fnum, f.Fexp + (s+1)⟩
      show x * bpow beta (s + 1)
            = (f.Fnum : ℝ) * bpow beta (f.Fexp + (s + 1))
      rw [hxf]
      show (f.Fnum : ℝ) * bpow beta f.Fexp * bpow beta (s + 1)
            = (f.Fnum : ℝ) * bpow beta (f.Fexp + (s + 1))
      have h1 : bpow beta (f.Fexp + (s + 1))
              = bpow beta f.Fexp * bpow beta (s + 1) := by
        rw [bpow_plus]
      rw [h1]; ring
    · exact hbf
  -- round(x · β^(s+1)) = x · β^(s+1) since it's in F.
  have h_round_eq : round beta (FLX_exp prec) (Znearest choice) (x * bpow beta (s + 1))
                  = x * bpow beta (s + 1) :=
    round_generic beta (FLX_exp prec) (Znearest choice) h_F_xbeta
  -- p = round(x·C) ≤ round(x·β^(s+1)) by monotonicity.
  have h_round_le := round_le beta (FLX_exp prec) (FLX_exp_valid prec hp)
                       (Znearest choice) h_xC_le
  linarith

/-- `mag(p) ≤ m + s + 1`, where `m = mag(x)`. Follows from `|p| ≤ x · β^(s+1) < β^(m+s+1)`. -/
private theorem Veltkamp_mag_p_le_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    mag beta (Veltkamp_p_FLX beta prec choice s x) ≤ mag beta x + s + 1 := by
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set m := mag beta x with hm_def
  have hp_ge : x ≤ p := Veltkamp_x_le_p_FLX beta prec hp choice Fx hx_pos hs
  have hp_pos : 0 < p := lt_of_lt_of_le hx_pos hp_ge
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  -- |p| ≤ x · β^(s+1) < β^m · β^(s+1) = β^(m+s+1).
  have h_p_bound : p ≤ x * bpow beta (s + 1) :=
    Veltkamp_p_le_xbeta_FLX beta prec hp choice Fx hx_pos hs
  have h_x_lt : x < bpow beta m := by
    have h := bpow_mag_gt beta x
    rwa [abs_of_pos hx_pos] at h
  have h_p_lt : p < bpow beta (m + s + 1) := by
    have h_bpow_s1 : 0 < bpow beta (s + 1) := bpow_gt_0 beta (s + 1)
    have h_xb_lt : x * bpow beta (s + 1) < bpow beta m * bpow beta (s + 1) :=
      (mul_lt_mul_iff_of_pos_right h_bpow_s1).mpr h_x_lt
    have h_eq : bpow beta m * bpow beta (s + 1) = bpow beta (m + s + 1) := by
      rw [← bpow_plus]; congr 1; ring
    linarith
  have hp_abs : |p| = p := abs_of_nonneg (le_of_lt hp_pos)
  apply mag_le_bpow beta hp_ne
  rw [hp_abs]; exact h_p_lt

/-- `cexp(p) ≤ s + 1 + cexp(x)`. Immediate from `mag(p) ≤ m + s + 1`. -/
private theorem Veltkamp_cexp_p_le_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 0 ≤ s) :
    cexp beta (FLX_exp prec) (Veltkamp_p_FLX beta prec choice s x)
      ≤ s + 1 + cexp beta (FLX_exp prec) x := by
  show mag beta (Veltkamp_p_FLX beta prec choice s x) - prec
       ≤ s + 1 + (mag beta x - prec)
  have := Veltkamp_mag_p_le_FLX beta prec hp choice Fx hx_pos hs
  linarith

/-- **`Veltkamp_aux_FLX_CaseB` interior subcase**: when `M_x ≤ β^prec − β − 1`,
the bound `|x − hx| ≤ β^(s + cexp x)/2` holds. The argument: `|x − p| ≤
(M_x + β/2) · β^(s+cexp x) < (M_x + β) · β^(s + cexp x) =: g`. Since `g ∈ F`
and `g < β^(s + mag x)`, we get `|q| ≤ g < β^(s+m)`, hence `mag(q) ≤ s + m`
and `cexp(q) ≤ s + cexp x`. The bound on `|err_q|` follows. -/
theorem Veltkamp_aux_FLX_CaseB_interior (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_caseB : mag beta (x * Veltkamp_C beta s) = mag beta x + s + 1)
    (h_Mx_interior :
      Ztrunc (scaled_mantissa beta (FLX_exp prec) x)
        ≤ (beta.val : ℤ) ^ prec.toNat - beta.val - 1) :
    |x - Veltkamp_hx_FLX beta prec choice s x|
      ≤ bpow beta (s + cexp beta (FLX_exp prec) x) / 2 := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  set Mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hMx_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hβ_int_ge_2 : (2 : ℤ) ≤ beta.val := beta.prop
  have hβ_int_pos : (0 : ℤ) < beta.val := by linarith
  have hcx_eq : cx = m - prec := rfl
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hxC_pos : 0 < x * Veltkamp_C beta s := by
    apply mul_pos hx_pos
    unfold Veltkamp_C; linarith [bpow_gt_0 beta s]
  have hxC_ne : x * Veltkamp_C beta s ≠ 0 := ne_of_gt hxC_pos
  -- x = M_x · β^cx.
  have hMx_eq : x = (Mx : ℝ) * bpow beta cx := Fx
  -- M_x > 0.
  have hMx_pos : 0 < Mx := by
    apply gt_0_F2R (beta := beta) (e := cx)
    show 0 < (Mx : ℝ) * bpow beta cx
    rw [← hMx_eq]; exact hx_pos
  -- M_x < β^prec.
  have hMx_lt : Mx < (beta.val : ℤ) ^ prec.toNat := by
    have ⟨f, hxf, hbf⟩ := FLX_format_generic beta prec hp Fx
    -- f.Fnum is the same as Mx by canonicity, but we don't have that directly.
    -- Use FLX bound on the explicit mantissa instead.
    -- Actually, |Mx| < β^prec from FLX_format_generic on Fx.
    have := FLX_format_generic beta prec hp Fx
    obtain ⟨⟨f1, f1exp⟩, hxf1, hbf1⟩ := this
    -- Mx is the canonical Ztrunc(scaled_mantissa x). Compute |Mx| < β^prec.
    have h_sm := scaled_mantissa_lt_bpow beta (FLX_exp prec) x
    have h_sm_eq : ((Mx : ℤ) : ℝ) = scaled_mantissa beta (FLX_exp prec) x :=
      (scaled_mantissa_generic beta (FLX_exp prec) Fx).symm
    have h_abs1 : |((Mx : ℤ) : ℝ)| < bpow beta prec := by
      rw [h_sm_eq]
      calc |scaled_mantissa beta (FLX_exp prec) x|
          < bpow beta (mag beta x - FLX_exp prec (mag beta x)) := h_sm
        _ = bpow beta prec := by
            show bpow beta (mag beta x - (mag beta x - prec)) = bpow beta prec
            congr 1; ring
    have h_abs : (|Mx| : ℝ) < bpow beta prec := by
      have h_eq : (|Mx| : ℝ) = |((Mx : ℤ) : ℝ)| := by push_cast; rfl
      rw [h_eq]; exact h_abs1
    -- Now bridge to ℤ.
    have h_abs_int : |Mx| < (beta.val : ℤ) ^ prec.toNat := by
      have h_lhs : ((|Mx| : ℤ) : ℝ) < ((((beta.val : ℤ) ^ prec.toNat) : ℤ) : ℝ) := by
        rw [IZR_Zpower beta (le_of_lt hp)]
        push_cast; exact h_abs
      exact_mod_cast h_lhs
    omega
  -- |err_p| ≤ β · β^(s + cx) / 2 = β^(s+1+cx)/2.
  have h_err_p_bound : |p - x * Veltkamp_C beta s|
                        ≤ bpow beta (s + 1 + cx) / 2 := by
    have h_p_eq : p = round beta (FLX_exp prec) (Znearest choice)
                       (x * Veltkamp_C beta s) := rfl
    rw [h_p_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                (x * Veltkamp_C beta s)
    rw [ulp_neq_0 beta _ hxC_ne] at h
    have h_cexp : cexp beta (FLX_exp prec) (x * Veltkamp_C beta s)
                = mag beta (x * Veltkamp_C beta s) - prec := rfl
    rw [h_cexp, h_caseB] at h
    -- h : |round - xC| ≤ β^(m+s+1-prec)/2 = β^(s+1+cx)/2 (since cx = m - prec).
    have heq : (m + s + 1 - prec : ℤ) = s + 1 + cx := by
      show (m + s + 1 - prec : ℤ) = s + 1 + (m - prec); ring
    rw [heq] at h
    linarith
  -- x · β^s = M_x · β^(s+cx).
  have h_xbs_eq : x * bpow beta s = (Mx : ℝ) * bpow beta (s + cx) := by
    rw [hMx_eq]
    have h1 : bpow beta (s + cx) = bpow beta s * bpow beta cx := by
      rw [bpow_plus]
    rw [h1]; ring
  -- |x - p| ≤ (M_x + β/2) · β^(s+cx).
  have h_xmp_eq : x - p = -(x * bpow beta s) - (p - x * Veltkamp_C beta s) := by
    rw [hC_eq]; ring
  have h_bpow_s1cx_eq : bpow beta (s + 1 + cx) = (beta.val : ℝ) * bpow beta (s + cx) := by
    rw [show (s + 1 + cx : ℤ) = (s + cx) + 1 from by ring, bpow_plus, bpow_one]; ring
  have h_abs_xmp : |x - p|
                    ≤ ((Mx : ℝ) + beta.val / 2) * bpow beta (s + cx) := by
    rw [h_xmp_eq]
    have h_tri : |-(x * bpow beta s) - (p - x * Veltkamp_C beta s)|
                  ≤ |x * bpow beta s| + |p - x * Veltkamp_C beta s| := by
      rw [show -(x * bpow beta s) - (p - x * Veltkamp_C beta s)
            = -(x * bpow beta s + (p - x * Veltkamp_C beta s)) from by ring,
          abs_neg]
      exact abs_add_le _ _
    have h_xbs_abs : |x * bpow beta s| = x * bpow beta s :=
      abs_of_pos (mul_pos hx_pos (bpow_gt_0 beta s))
    have hMx_real_pos : (0 : ℝ) < (Mx : ℝ) := by exact_mod_cast hMx_pos
    have hbpow_pos : 0 < bpow beta (s + cx) := bpow_gt_0 _ _
    -- |x · β^s| = M_x · β^(s+cx), |err_p| ≤ β·β^(s+cx)/2.
    have h_err_p_bound' : |p - x * Veltkamp_C beta s|
                          ≤ (beta.val : ℝ) * bpow beta (s + cx) / 2 := by
      have := h_err_p_bound
      rw [h_bpow_s1cx_eq] at this; exact this
    have : |x * bpow beta s| + |p - x * Veltkamp_C beta s|
            ≤ (Mx : ℝ) * bpow beta (s + cx)
              + (beta.val : ℝ) * bpow beta (s + cx) / 2 := by
      rw [h_xbs_abs, h_xbs_eq] at *
      linarith
    have h_rearrange :
        ((Mx : ℝ) + beta.val / 2) * bpow beta (s + cx)
          = (Mx : ℝ) * bpow beta (s + cx)
            + (beta.val : ℝ) * bpow beta (s + cx) / 2 := by ring
    linarith
  -- (M_x + β) is in [β^(prec-1), β^prec - 1].
  -- We need β^(prec-1) ≤ M_x to ensure M_x + β ≥ β^(prec-1).
  -- Actually, M_x is the canonical mantissa of x ≥ β^(m-1), so M_x ≥ β^(prec-1).
  have hMx_ge_prec1 : (beta.val : ℤ) ^ (prec.toNat - 1) ≤ Mx := by
    -- x ≥ β^(m-1) (from being a normal FLX value).
    have h_x_ge : bpow beta (m - 1) ≤ x := by
      have := bpow_mag_le beta hx_ne
      rwa [abs_of_pos hx_pos] at this
    -- M_x · β^cx = x ≥ β^(m-1), and cx = m - prec.
    -- So M_x ≥ β^(m-1)/β^(m-prec) = β^(prec-1).
    have h_Mx_real : ((beta.val : ℝ) ^ (prec.toNat - 1 : ℕ))
                       ≤ (Mx : ℝ) := by
      -- bpow(prec-1) ≤ M_x.
      have h_bpow_prec1 : bpow beta (prec - 1) ≤ (Mx : ℝ) := by
        -- From x ≥ β^(m-1) and x = M_x · β^cx with cx = m - prec.
        have h1 : (Mx : ℝ) * bpow beta cx ≥ bpow beta (m - 1) := by
          rw [← hMx_eq]; exact h_x_ge
        have h_cx_eq : bpow beta cx = bpow beta (m - prec) := by
          rw [hcx_eq]
        rw [h_cx_eq] at h1
        have h_bpow_cx_pos : 0 < bpow beta (m - prec) := bpow_gt_0 _ _
        -- M_x · β^(m-prec) ≥ β^(m-1) = β^(prec-1) · β^(m-prec), so M_x ≥ β^(prec-1).
        have h_mul : bpow beta (m - 1) = bpow beta (prec - 1) * bpow beta (m - prec) := by
          rw [← bpow_plus]; congr 1; ring
        rw [h_mul] at h1
        have h_bpow_prec1_pos : 0 < bpow beta (prec - 1) := bpow_gt_0 _ _
        nlinarith
      -- bpow(prec-1) = β^(prec.toNat - 1).
      have h_pnat : (prec - 1 : ℤ).toNat = prec.toNat - 1 := by
        have hpr : (prec.toNat : ℤ) = prec := Int.toNat_of_nonneg (le_of_lt hp)
        omega
      have h_bpow_natcast : bpow beta (prec - 1)
                            = (((beta.val : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) := by
        rw [IZR_Zpower beta (by linarith : (0 : ℤ) ≤ prec - 1)]
      rw [h_bpow_natcast, h_pnat] at h_bpow_prec1
      have : (((beta.val : ℤ) ^ (prec.toNat - 1) : ℤ) : ℝ) = (beta.val : ℝ) ^ (prec.toNat - 1) := by
        push_cast; rfl
      rw [this] at h_bpow_prec1
      exact h_bpow_prec1
    -- Bridge to ℤ.
    have h_int : ((beta.val : ℤ) ^ (prec.toNat - 1) : ℤ) ≤ Mx := by
      have h1 : (((beta.val : ℤ) ^ (prec.toNat - 1) : ℤ) : ℝ) ≤ ((Mx : ℤ) : ℝ) := by
        have : (((beta.val : ℤ) ^ (prec.toNat - 1) : ℤ) : ℝ)
                = (beta.val : ℝ) ^ (prec.toNat - 1) := by push_cast; rfl
        rw [this]
        exact h_Mx_real
      exact_mod_cast h1
    exact h_int
  -- g := (M_x + β) · β^(s+cx).  We show g ∈ F.
  have hMx_plus_β_bound : Mx + beta.val ≤ (beta.val : ℤ) ^ prec.toNat - 1 := by
    omega
  have hMx_plus_β_pos : 0 < Mx + beta.val := by
    have : 0 ≤ beta.val := by linarith
    linarith
  -- The float ⟨M_x + β, s + cx⟩.
  have h_g_in_F : generic_format beta (FLX_exp prec)
                    (((Mx + beta.val : ℤ) : ℝ) * bpow beta (s + cx)) := by
    apply generic_format_FLX beta prec hp
    refine ⟨⟨Mx + beta.val, s + cx⟩, rfl, ?_⟩
    show |Mx + beta.val| < (beta.val : ℤ) ^ prec.toNat
    rw [abs_of_pos hMx_plus_β_pos]
    omega
  -- |x - p| ≤ g.
  have h_abs_xmp_le_g : |x - p|
                        ≤ ((Mx + beta.val : ℤ) : ℝ) * bpow beta (s + cx) := by
    have hge : (0 : ℝ) ≤ bpow beta (s + cx) := bpow_ge_0 _ _
    have h_le : ((Mx : ℝ) + beta.val / 2) ≤ ((Mx + beta.val : ℤ) : ℝ) := by
      have : (((Mx + beta.val : ℤ)) : ℝ) = (Mx : ℝ) + (beta.val : ℝ) := by push_cast; ring
      rw [this]
      linarith
    calc |x - p| ≤ ((Mx : ℝ) + beta.val / 2) * bpow beta (s + cx) := h_abs_xmp
      _ ≤ ((Mx + beta.val : ℤ) : ℝ) * bpow beta (s + cx) := by
          exact mul_le_mul_of_nonneg_right h_le hge
  -- |q| ≤ g.
  have h_abs_q_le_g : |q| ≤ ((Mx + beta.val : ℤ) : ℝ) * bpow beta (s + cx) := by
    have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
    rw [h_q_eq]
    exact abs_round_le_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
            h_g_in_F h_abs_xmp_le_g
  -- g < β^(s + m).
  have h_g_lt : ((Mx + beta.val : ℤ) : ℝ) * bpow beta (s + cx) < bpow beta (s + m) := by
    have h_g_real_le : ((Mx + beta.val : ℤ) : ℝ)
                        ≤ (((beta.val : ℤ) ^ prec.toNat - 1 : ℤ) : ℝ) := by
      exact_mod_cast hMx_plus_β_bound
    have h_pow_eq : (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) = bpow beta prec := by
      have := IZR_Zpower beta (le_of_lt hp)
      push_cast at this ⊢
      linarith
    have h_g_real_lt : ((Mx + beta.val : ℤ) : ℝ) < bpow beta prec := by
      have h1 : (((beta.val : ℤ) ^ prec.toNat - 1 : ℤ) : ℝ)
                  = (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) - 1 := by push_cast; ring
      rw [h1, h_pow_eq] at h_g_real_le
      linarith
    have hbpow_pos : 0 < bpow beta (s + cx) := bpow_gt_0 _ _
    have h_mul_lt : ((Mx + beta.val : ℤ) : ℝ) * bpow beta (s + cx)
                      < bpow beta prec * bpow beta (s + cx) :=
      (mul_lt_mul_iff_of_pos_right hbpow_pos).mpr h_g_real_lt
    have h_pow_combine : bpow beta prec * bpow beta (s + cx) = bpow beta (s + m) := by
      rw [← bpow_plus]; congr 1
      show prec + (s + cx) = s + m
      rw [hcx_eq]; ring
    linarith
  -- |q| < β^(s+m), hence mag(q) ≤ s + m.
  have h_abs_q_lt : |q| < bpow beta (s + m) := by linarith
  -- Case: q = 0 vs q ≠ 0.
  -- hxExact: x - hx = -(q - (x - p)).
  have h_hxExact : Veltkamp_hx_FLX beta prec choice s x = q + p :=
    hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_x_minus_hx : x - Veltkamp_hx_FLX beta prec choice s x
                    = -(q - (x - p)) := by rw [h_hxExact]; ring
  rw [h_x_minus_hx, abs_neg]
  by_cases hq_zero : q = 0
  · -- q = 0 in FLX (no negligible exp) means x - p = 0.
    have hxmp_zero : x - p = 0 := by
      have h_neg : negligible_exp (FLX_exp prec) = none :=
        negligible_exp_FLX prec hp
      have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
      rw [h_q_eq] at hq_zero
      exact eq_0_round_0_negligible_exp beta _ (FLX_exp_valid prec hp) h_neg _ hq_zero
    rw [hq_zero, hxmp_zero, sub_zero, abs_zero]
    have := bpow_ge_0 beta (s + cx)
    linarith
  · -- q ≠ 0: mag(q) ≤ s + m, cexp(q) ≤ s + cx.
    have h_mag_q : mag beta q ≤ s + m :=
      mag_le_bpow beta hq_zero h_abs_q_lt
    have h_cexp_q : cexp beta (FLX_exp prec) q ≤ s + cx := by
      show mag beta q - prec ≤ s + cx
      rw [hcx_eq]; linarith
    have h_bpow_cexp_le : bpow beta (cexp beta (FLX_exp prec) q)
                          ≤ bpow beta (s + cx) :=
      bpow_le beta h_cexp_q
    have h_NotFTZ : Exp_not_FTZ (FLX_exp prec) :=
      monotone_exp_not_FTZ (FLX_exp_valid prec hp) (FLX_exp_monotone prec)
    have h := error_le_half_ulp_round beta (FLX_exp prec) (FLX_exp_valid prec hp)
                h_NotFTZ (FLX_exp_monotone prec) choice (x - p)
    have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
    rw [← h_q_eq] at h
    rw [ulp_neq_0 beta _ hq_zero] at h
    linarith

/-! ### Pff's J1: `p ≤ β^(s+m) + β^m`

A tight upper bound on `p = round(x · C)` from `x < β^m` and `β^(s+m) + β^m ∈ F`.
The key fact for the boundary subcase. -/

/-- **Pff `J1` at FLX**: `p ≤ β^(s+m) + β^m`, where `m = mag x`. -/
private theorem Veltkamp_p_le_J1_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 1 ≤ s) (hs_hi : s + 1 < prec) :
    Veltkamp_p_FLX beta prec choice s x
      ≤ bpow beta (s + mag beta x) + bpow beta (mag beta x) := by
  unfold Veltkamp_p_FLX
  set m := mag beta x with hm_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  -- x · C < β^m · C, where C = β^s + 1.
  have h_x_lt : x < bpow beta m := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos hx_pos] at this
  have hC_pos : 0 < Veltkamp_C beta s := by
    unfold Veltkamp_C; linarith [bpow_gt_0 beta s]
  have h_xC_lt : x * Veltkamp_C beta s ≤ bpow beta m * Veltkamp_C beta s :=
    mul_le_mul_of_nonneg_right (le_of_lt h_x_lt) (le_of_lt hC_pos)
  -- β^m · C = β^(s+m) + β^m.
  have h_pow_C_eq : bpow beta m * Veltkamp_C beta s
                  = bpow beta (s + m) + bpow beta m := by
    unfold Veltkamp_C
    have h1 : bpow beta (s + m) = bpow beta s * bpow beta m := by rw [bpow_plus]
    rw [h1]; ring
  -- β^m · C ∈ F. Mantissa β^s + 1 at exponent m, |mantissa| = β^s + 1 ≤ β^(prec-1) + 1 < β^prec.
  have h_F : generic_format beta (FLX_exp prec)
                (bpow beta (s + m) + bpow beta m) := by
    apply generic_format_FLX beta prec hp
    refine ⟨⟨(beta.val : ℤ) ^ s.toNat + 1, m⟩, ?_, ?_⟩
    · show bpow beta (s + m) + bpow beta m
            = ((((beta.val : ℤ) ^ s.toNat + 1 : ℤ) : ℝ) * bpow beta m)
      rw [show bpow beta (s + m) = bpow beta s * bpow beta m from by rw [bpow_plus]]
      rw [Int.cast_add, Int.cast_one, IZR_Zpower beta (by linarith : (0 : ℤ) ≤ s)]
      ring
    · show |(beta.val : ℤ) ^ s.toNat + 1| < (beta.val : ℤ) ^ prec.toNat
      have hβ_int_ge_2 : (2 : ℤ) ≤ beta.val := beta.prop
      have h_pow_s_pos : (1 : ℤ) ≤ beta.val ^ s.toNat := by
        have h1 : (1 : ℤ) = 1 ^ s.toNat := (one_pow _).symm
        rw [h1]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have h_sum_pos : (0 : ℤ) < beta.val ^ s.toNat + 1 := by linarith
      rw [abs_of_pos h_sum_pos]
      -- β^s + 1 ≤ 2·β^s ≤ β·β^s = β^(s+1) ≤ β^(prec-1) < β^prec.
      have h_two_pow : (2 : ℤ) * beta.val ^ s.toNat ≤ beta.val ^ (s.toNat + 1) := by
        rw [pow_succ]; nlinarith
      have h_succ_lt : s.toNat + 1 < prec.toNat := by
        have : (s.toNat : ℤ) + 1 < (prec.toNat : ℤ) := by
          rw [Int.toNat_of_nonneg (le_of_lt hp), Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ s)]
          linarith
        exact_mod_cast this
      have h_pow_mono : beta.val ^ (s.toNat + 1) < beta.val ^ prec.toNat := by
        apply pow_lt_pow_right₀
        · linarith
        · exact h_succ_lt
      linarith
  -- round(x · C) ≤ round(β^m · C) = β^m · C by monotonicity + round_generic.
  have h_round_le := round_le beta (FLX_exp prec) (FLX_exp_valid prec hp)
                       (Znearest choice) h_xC_lt
  rw [h_pow_C_eq] at h_round_le
  rw [round_generic beta (FLX_exp prec) (Znearest choice) h_F] at h_round_le
  exact h_round_le

/-- **Boundary `-q ≤ β^(s+m)`** (Pff's `V`): when `M_x ≥ β^prec − β` (so
`x ≥ β^m − β · β^cexp(x)`), the negation of `q` is bounded by `β^(s+m)`.
The argument: `p − x ≤ β^(s+m) + β · β^cexp(x)` (J1 plus the boundary lower
bound on `x`), and this is below the midpoint between `β^(s+m)` and its
successor in F, so `round_N(p − x) ≤ β^(s+m)`. -/
private theorem Veltkamp_neg_q_le_pow_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_Mx_boundary :
      (beta.val : ℤ) ^ prec.toNat - beta.val
        ≤ Ztrunc (scaled_mantissa beta (FLX_exp prec) x)) :
    -Veltkamp_q_FLX beta prec choice s x ≤ bpow beta (s + mag beta x) := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  set Mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hMx_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hβ_int_ge_2 : (2 : ℤ) ≤ beta.val := beta.prop
  have hβ_int_pos : (0 : ℤ) < beta.val := by linarith
  have hcx_eq : cx = m - prec := rfl
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hMx_eq : x = (Mx : ℝ) * bpow beta cx := Fx
  -- Boundary lower bound on x.
  have h_x_ge_boundary : (beta.val : ℝ) ^ prec.toNat * bpow beta cx
                          - (beta.val : ℝ) * bpow beta cx ≤ x := by
    have h_Mx_real : (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) - (beta.val : ℝ)
                       ≤ (Mx : ℝ) := by
      have h1 : (((beta.val : ℤ) ^ prec.toNat - beta.val : ℤ) : ℝ) ≤ ((Mx : ℤ) : ℝ) := by
        exact_mod_cast h_Mx_boundary
      have h2 : (((beta.val : ℤ) ^ prec.toNat - beta.val : ℤ) : ℝ)
                  = (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) - (beta.val : ℝ) := by
        push_cast; ring
      rw [h2] at h1; exact h1
    have h_Mx_cast : (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) = (beta.val : ℝ) ^ prec.toNat := by
      push_cast; rfl
    rw [h_Mx_cast] at h_Mx_real
    have h_bpow_cx_pos : 0 < bpow beta cx := bpow_gt_0 _ _
    calc (beta.val : ℝ) ^ prec.toNat * bpow beta cx - (beta.val : ℝ) * bpow beta cx
        = ((beta.val : ℝ) ^ prec.toNat - (beta.val : ℝ)) * bpow beta cx := by ring
      _ ≤ (Mx : ℝ) * bpow beta cx :=
          mul_le_mul_of_nonneg_right h_Mx_real (le_of_lt h_bpow_cx_pos)
      _ = x := hMx_eq.symm
  -- β^prec · β^cx = β^m.
  have h_bpow_prec_cx_eq_m : (beta.val : ℝ) ^ prec.toNat * bpow beta cx = bpow beta m := by
    have h1 : (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) = bpow beta prec := by
      have := IZR_Zpower beta (le_of_lt hp)
      push_cast at this ⊢; linarith
    have h2 : (beta.val : ℝ) ^ prec.toNat = (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) := by
      push_cast; rfl
    rw [h2, h1, ← bpow_plus]; congr 1; rw [hcx_eq]; ring
  -- β · β^cx = β^(cx+1).
  have h_β_bpow_cx_eq : (beta.val : ℝ) * bpow beta cx = bpow beta (cx + 1) := by
    rw [show (cx + 1 : ℤ) = cx + 1 from rfl, bpow_plus, bpow_one]; ring
  -- x ≥ β^m - β^(cx+1).
  have h_x_ge : bpow beta m - bpow beta (cx + 1) ≤ x := by
    rw [← h_bpow_prec_cx_eq_m, ← h_β_bpow_cx_eq]
    exact h_x_ge_boundary
  -- p ≤ β^(s+m) + β^m (J1).
  have h_p_J1 : p ≤ bpow beta (s + m) + bpow beta m :=
    Veltkamp_p_le_J1_FLX beta prec hp choice Fx hx_pos (by linarith) (by linarith)
  -- p - x ≤ β^(s+m) + β^(cx+1).
  have h_p_minus_x : p - x ≤ bpow beta (s + m) + bpow beta (cx + 1) := by
    have : bpow beta m - (bpow beta m - bpow beta (cx + 1))
            = bpow beta (cx + 1) := by ring
    linarith
  -- p - x is below midpoint(β^(s+m), succ β^(s+m)) = β^(s+m) + β · β^(s+cx)/2.
  -- succ(β^(s+m)) = β^(s+m) + β^(s+m+1-prec) = β^(s+m) + β^(s+1+cx).
  set u := bpow beta (s + m) with hu_def
  have hu_pos : 0 < u := bpow_gt_0 _ _
  have hu_nn : 0 ≤ u := le_of_lt hu_pos
  have h_F_u : generic_format beta (FLX_exp prec) u :=
    generic_format_bpow beta (FLX_exp prec) (s + m) (by
      show FLX_exp prec ((s + m) + 1) ≤ (s + m)
      show s + m + 1 - prec ≤ s + m
      linarith)
  have h_succ_u : succ beta (FLX_exp prec) u
                  = u + bpow beta (s + m + 1 - prec) := by
    rw [succ_eq_pos beta (FLX_exp prec) hu_nn]
    rw [ulp_neq_0 beta _ (ne_of_gt hu_pos)]
    show u + bpow beta (cexp beta (FLX_exp prec) u) = u + bpow beta (s + m + 1 - prec)
    congr 1
    show bpow beta (mag beta u - prec) = bpow beta (s + m + 1 - prec)
    congr 1
    show mag beta (bpow beta (s + m)) - prec = s + m + 1 - prec
    rw [mag_bpow beta]
  -- p - x is in F? No, but it doesn't need to be for round_N_le_midp.
  -- We need (p - x) < (u + succ u)/2 = u + β^(s+m+1-prec)/2.
  -- We have p - x ≤ u + β^(cx+1).
  -- β^(cx+1) = β^(m-prec+1) < β^(s+m+1-prec)/2 ⟺ 2 · β < β^(s+1) ⟺ 2 < β^s. ✓ for s ≥ 2.
  have h_bpow_eq : bpow beta (s + m + 1 - prec) = bpow beta (s + 1) * bpow beta (cx - prec + prec) := by
    rw [hcx_eq]; rw [← bpow_plus]; congr 1; ring
  have h_midp_bound : 2 * bpow beta (cx + 1) < bpow beta (s + m + 1 - prec) := by
    -- 2 · β^(cx+1) < β^(s+m+1-prec) = β^s · β^(cx+1), so suffices 2 < β^s.
    have h_eq : bpow beta (s + m + 1 - prec) = bpow beta s * bpow beta (cx + 1) := by
      rw [show (s + m + 1 - prec : ℤ) = s + (cx + 1) from by rw [hcx_eq]; ring, bpow_plus]
    rw [h_eq]
    have h_bpow_cx1_pos : 0 < bpow beta (cx + 1) := bpow_gt_0 _ _
    have h_β_s_ge : (4 : ℝ) ≤ bpow beta s := by
      have h_bp2 : bpow beta 2 = (beta.val : ℝ) * (beta.val : ℝ) := by
        rw [show (2 : ℤ) = 1 + 1 from rfl, bpow_plus, bpow_one]
      have : (4 : ℝ) ≤ bpow beta 2 := by rw [h_bp2]; nlinarith
      exact le_trans this (bpow_le beta hs_lo)
    have h_2_lt : (2 : ℝ) < bpow beta s := by linarith
    exact (mul_lt_mul_iff_of_pos_right h_bpow_cx1_pos).mpr h_2_lt
  have h_below_midp : p - x < (u + succ beta (FLX_exp prec) u) / 2 := by
    rw [h_succ_u]
    have h_arith : (u + (u + bpow beta (s + m + 1 - prec))) / 2
                  = u + bpow beta (s + m + 1 - prec) / 2 := by ring
    rw [h_arith]
    have h_target : bpow beta (cx + 1) < bpow beta (s + m + 1 - prec) / 2 := by linarith
    linarith
  -- Apply round_N_le_midp with the opposite choice.
  set opp_choice : ℤ → Bool := fun n => !choice (-(n+1)) with hopp_def
  have h_round_le : round beta (FLX_exp prec) (Znearest opp_choice) (p - x) ≤ u :=
    round_N_le_midp beta (FLX_exp prec) (FLX_exp_valid prec hp) opp_choice h_F_u
      h_below_midp
  -- -q = round_N(opp_choice)(p - x). Use round_N_opp on argument (p - x).
  have h_neg_q : -q = round beta (FLX_exp prec) (Znearest opp_choice) (p - x) := by
    have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
    have h_opp := round_N_opp beta (FLX_exp prec) choice (p - x)
    -- h_opp : round (choice) (-(p-x)) = -round (opp_choice) (p-x)
    rw [show (-(p - x) : ℝ) = x - p from by ring] at h_opp
    -- h_opp : round (choice) (x - p) = -round (opp_choice) (p - x)
    rw [h_q_eq, h_opp, neg_neg]
  rw [h_neg_q]; exact h_round_le

/-- **`Veltkamp_aux_FLX_CaseB` boundary subcase**: when `M_x ≥ β^prec - β`, the
bound `|x - hx| ≤ β^(s + cexp x)/2` holds. The argument splits on whether
`q = -β^(s+m)` exactly (the Pff `eqLe` right branch) or `q > -β^(s+m)` strict
(the universal half-ulp argument). -/
theorem Veltkamp_aux_FLX_CaseB_boundary (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_Mx_boundary :
      (beta.val : ℤ) ^ prec.toNat - beta.val
        ≤ Ztrunc (scaled_mantissa beta (FLX_exp prec) x)) :
    |x - Veltkamp_hx_FLX beta prec choice s x|
      ≤ bpow beta (s + cexp beta (FLX_exp prec) x) / 2 := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  set Mx := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hMx_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hβ_int_ge_2 : (2 : ℤ) ≤ beta.val := beta.prop
  have hcx_eq : cx = m - prec := rfl
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hMx_eq : x = (Mx : ℝ) * bpow beta cx := Fx
  -- hxExact: x - hx = -(q - (x - p)).
  have h_hxExact : Veltkamp_hx_FLX beta prec choice s x = q + p :=
    hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_x_minus_hx : x - Veltkamp_hx_FLX beta prec choice s x
                    = -(q - (x - p)) := by rw [h_hxExact]; ring
  rw [h_x_minus_hx, abs_neg]
  -- q ≤ 0.
  have hq_nonpos : q ≤ 0 :=
    Veltkamp_q_nonpos_FLX beta prec hp choice Fx hx_pos (by linarith)
  -- -q ≤ β^(s+m).
  have h_neg_q_le : -q ≤ bpow beta (s + m) :=
    Veltkamp_neg_q_le_pow_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi h_Mx_boundary
  -- Split on q = -β^(s+m) vs q > -β^(s+m).
  by_cases hq_eq : q = -bpow beta (s + m)
  · -- Case: q = -β^(s+m). Subcase on x - p vs q.
    -- Setup: p ≤ β^(s+m) + β^m and x ≥ β^m - β · β^cx.
    have h_p_J1 : p ≤ bpow beta (s + m) + bpow beta m :=
      Veltkamp_p_le_J1_FLX beta prec hp choice Fx hx_pos (by linarith) (by linarith)
    have h_x_ge_boundary : bpow beta m - (beta.val : ℝ) * bpow beta cx ≤ x := by
      -- x = M_x · β^cx, M_x ≥ β^prec - β.
      have h_Mx_real : (((beta.val : ℤ) ^ prec.toNat - beta.val : ℤ) : ℝ) ≤ ((Mx : ℤ) : ℝ) := by
        exact_mod_cast h_Mx_boundary
      have h_cast_simpl : (((beta.val : ℤ) ^ prec.toNat - beta.val : ℤ) : ℝ)
                          = (beta.val : ℝ) ^ prec.toNat - (beta.val : ℝ) := by push_cast; ring
      rw [h_cast_simpl] at h_Mx_real
      have h_pow_eq : (beta.val : ℝ) ^ prec.toNat * bpow beta cx = bpow beta m := by
        have h1 : (beta.val : ℝ) ^ prec.toNat = bpow beta prec := by
          have := IZR_Zpower beta (le_of_lt hp)
          push_cast at this ⊢; linarith
        rw [h1, ← bpow_plus]; congr 1; rw [hcx_eq]; ring
      have h_bpow_cx_pos : 0 < bpow beta cx := bpow_gt_0 _ _
      calc bpow beta m - (beta.val : ℝ) * bpow beta cx
          = (beta.val : ℝ) ^ prec.toNat * bpow beta cx - (beta.val : ℝ) * bpow beta cx := by
              rw [h_pow_eq]
        _ = ((beta.val : ℝ) ^ prec.toNat - (beta.val : ℝ)) * bpow beta cx := by ring
        _ ≤ (Mx : ℝ) * bpow beta cx :=
            mul_le_mul_of_nonneg_right h_Mx_real (le_of_lt h_bpow_cx_pos)
        _ = x := hMx_eq.symm
    -- p - x ≤ β^(s+m) + β · β^cx.
    have h_p_minus_x : p - x ≤ bpow beta (s + m) + (beta.val : ℝ) * bpow beta cx := by
      linarith
    -- β · β^cx ≤ β^(s+cx)/2 (using s ≥ 2, β ≥ 2).
    have h_β_bpow_cx_le : (beta.val : ℝ) * bpow beta cx ≤ bpow beta (s + cx) / 2 := by
      -- 2β · β^cx ≤ β^s · β^cx, i.e., 2β ≤ β^s. For s ≥ 2, β^s ≥ 2β iff β^(s-1) ≥ 2, true for s ≥ 2.
      have h_β_s_ge_2β : (2 : ℝ) * (beta.val : ℝ) ≤ bpow beta s := by
        have h_β2 : (beta.val : ℝ) * (beta.val : ℝ) ≤ bpow beta s := by
          have : bpow beta 2 = (beta.val : ℝ) * (beta.val : ℝ) := by
            rw [show (2 : ℤ) = 1 + 1 from rfl, bpow_plus, bpow_one]
          rw [← this]
          exact bpow_le beta hs_lo
        nlinarith
      have h_bpow_cx_pos : 0 < bpow beta cx := bpow_gt_0 _ _
      have h_bpow_s_plus_cx_eq : bpow beta (s + cx) = bpow beta s * bpow beta cx := by
        rw [bpow_plus]
      rw [h_bpow_s_plus_cx_eq]
      have h1 : 2 * ((beta.val : ℝ) * bpow beta cx) ≤ bpow beta s * bpow beta cx := by
        have : 2 * (beta.val : ℝ) ≤ bpow beta s := h_β_s_ge_2β
        nlinarith
      linarith
    -- Now case-split on x - p vs q.
    by_cases h_xmp_le_q : x - p ≤ q
    · -- V''.a: x - p ≤ q. |err_q| = q - (x - p) = p - x - β^(s+m).
      have h_err_nonneg : 0 ≤ q - (x - p) := by linarith
      have h_abs : |q - (x - p)| = q - (x - p) := abs_of_nonneg h_err_nonneg
      rw [h_abs]
      -- q - (x - p) = -β^(s+m) - x + p = p - x - β^(s+m).
      have h_err_eq : q - (x - p) = p - x - bpow beta (s + m) := by rw [hq_eq]; ring
      rw [h_err_eq]
      -- p - x - β^(s+m) ≤ β · β^cx.
      have h_step : p - x - bpow beta (s + m) ≤ (beta.val : ℝ) * bpow beta cx := by
        linarith
      linarith
    · -- V''.b: x - p > q = -β^(s+m). Use error_le_half_ulp on x - p with mag(x-p) ≤ s+m.
      push_neg at h_xmp_le_q
      -- x - p > -β^(s+m), x - p ≤ 0 (since x ≤ p).
      have h_xp_le : x ≤ p := Veltkamp_x_le_p_FLX beta prec hp choice Fx hx_pos (by linarith)
      have h_xmp_le_zero : x - p ≤ 0 := by linarith
      have h_neg_xmp_lt : -(x - p) < bpow beta (s + m) := by
        rw [hq_eq] at h_xmp_le_q; linarith
      have h_abs_xmp_lt : |x - p| < bpow beta (s + m) := by
        rw [abs_of_nonpos h_xmp_le_zero]
        linarith
      -- mag(x - p) ≤ s + m.
      by_cases h_xmp_zero : x - p = 0
      · -- x - p = 0 ⟹ q = round(0) = 0, but q = -β^(s+m) ≠ 0. Contradiction.
        exfalso
        have h_q_zero : q = 0 := by
          have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
          rw [h_q_eq, h_xmp_zero, round_0]
        rw [h_q_zero] at hq_eq
        have h_bpow_pos : 0 < bpow beta (s + m) := bpow_gt_0 _ _
        linarith
      · have h_mag_xmp : mag beta (x - p) ≤ s + m :=
          mag_le_bpow beta h_xmp_zero h_abs_xmp_lt
        have h_cexp_xmp_le : cexp beta (FLX_exp prec) (x - p) ≤ s + cx := by
          show mag beta (x - p) - prec ≤ s + cx
          rw [hcx_eq]; linarith
        have h_bpow_cexp_le : bpow beta (cexp beta (FLX_exp prec) (x - p))
                              ≤ bpow beta (s + cx) := bpow_le beta h_cexp_xmp_le
        have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
        rw [h_q_eq]
        have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp)
                    choice (x - p)
        rw [ulp_neq_0 beta _ h_xmp_zero] at h
        linarith
  · -- Case: q ≠ -β^(s+m). Combined with -q ≤ β^(s+m), get -q < β^(s+m).
    have h_neg_q_lt : -q < bpow beta (s + m) := by
      rcases lt_or_eq_of_le h_neg_q_le with h_lt | h_eq
      · exact h_lt
      · -- -q = β^(s+m) ⟹ q = -β^(s+m), contradicting hq_eq.
        exfalso; apply hq_eq; linarith
    by_cases hq_zero : q = 0
    · -- q = 0: x - p = 0 (FLX), |err_q| = 0.
      have h_neg : negligible_exp (FLX_exp prec) = none :=
        negligible_exp_FLX prec hp
      have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
      have hq_round : round beta (FLX_exp prec) (Znearest choice) (x - p) = 0 := by
        rw [← h_q_eq]; exact hq_zero
      have h_xmp_zero : x - p = 0 :=
        eq_0_round_0_negligible_exp beta _ (FLX_exp_valid prec hp) h_neg _ hq_round
      rw [hq_zero, h_xmp_zero, sub_zero, abs_zero]
      have := bpow_ge_0 beta (s + cx); linarith
    · -- q ≠ 0: |q| < β^(s+m), mag(q) ≤ s+m, cexp(q) ≤ s+cx.
      have h_abs_q : |q| = -q := abs_of_nonpos hq_nonpos
      have h_abs_q_lt : |q| < bpow beta (s + m) := by rw [h_abs_q]; exact h_neg_q_lt
      have h_mag_q : mag beta q ≤ s + m := mag_le_bpow beta hq_zero h_abs_q_lt
      have h_cexp_q : cexp beta (FLX_exp prec) q ≤ s + cx := by
        show mag beta q - prec ≤ s + cx
        rw [hcx_eq]; linarith
      have h_bpow_cexp_le : bpow beta (cexp beta (FLX_exp prec) q)
                            ≤ bpow beta (s + cx) := bpow_le beta h_cexp_q
      have h_NotFTZ : Exp_not_FTZ (FLX_exp prec) :=
        monotone_exp_not_FTZ (FLX_exp_valid prec hp) (FLX_exp_monotone prec)
      have h := error_le_half_ulp_round beta (FLX_exp prec) (FLX_exp_valid prec hp)
                  h_NotFTZ (FLX_exp_monotone prec) choice (x - p)
      have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
      rw [← h_q_eq] at h
      rw [ulp_neq_0 beta _ hq_zero] at h
      linarith

/-! ### Unified `Veltkamp_aux_FLX_CaseB` and `Veltkamp_aux_FLX`

Combining the interior and boundary subcases on `M_x` gives the unified
Case B. Combining with Case A on `mag(x · C)` gives the full bound. -/

/-- **`Veltkamp_aux_FLX_CaseB`** (unified): when `mag(x · C) = m + s + 1`, the
bound holds. Dispatches on `M_x ≤ β^prec − β − 1` (interior) vs
`M_x ≥ β^prec − β` (boundary). -/
theorem Veltkamp_aux_FLX_CaseB (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_caseB : mag beta (x * Veltkamp_C beta s) = mag beta x + s + 1) :
    |x - Veltkamp_hx_FLX beta prec choice s x|
      ≤ bpow beta (s + cexp beta (FLX_exp prec) x) / 2 := by
  by_cases h_Mx_interior :
    Ztrunc (scaled_mantissa beta (FLX_exp prec) x)
      ≤ (beta.val : ℤ) ^ prec.toNat - beta.val - 1
  · exact Veltkamp_aux_FLX_CaseB_interior beta prec hp choice Fx hx_pos
      hs_lo hs_hi h_caseB h_Mx_interior
  · push_neg at h_Mx_interior
    exact Veltkamp_aux_FLX_CaseB_boundary beta prec hp choice Fx hx_pos
      hs_lo hs_hi (by omega)

/-- **`Veltkamp_aux_FLX`** (unified): the keystone bound. For `x > 0` in F(FLX, prec),
`2 ≤ s ≤ prec − 2`, the third Veltkamp step's error is at most `β^(s + cexp x)/2`.
Dispatches on `mag(x · C) = m + s` (Case A) vs `m + s + 1` (Case B). -/
theorem Veltkamp_aux_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    |x - Veltkamp_hx_FLX beta prec choice s x|
      ≤ bpow beta (s + cexp beta (FLX_exp prec) x) / 2 := by
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have h_mag_bounds := mag_xC_bounds beta hx_ne (by linarith : (1 : ℤ) ≤ s)
  have hC_unfold : Veltkamp_C beta s = bpow beta s + 1 := rfl
  -- mag(x·C) ∈ {m+s, m+s+1}.
  rcases eq_or_lt_of_le h_mag_bounds.1 with h_eq_A | h_lt
  · -- Case A: mag(x·C) = m+s.
    apply Veltkamp_aux_FLX_CaseA beta prec hp choice Fx hx_pos hs_lo hs_hi
    rw [hC_unfold]; exact h_eq_A.symm
  · -- mag(x·C) > m+s, combined with ≤ m+s+1, gives = m+s+1.
    have h_eq_B : mag beta (x * Veltkamp_C beta s) = mag beta x + s + 1 := by
      rw [hC_unfold]
      have := h_mag_bounds.2
      linarith
    exact Veltkamp_aux_FLX_CaseB beta prec hp choice Fx hx_pos hs_lo hs_hi h_eq_B

/-! ### Format-side helpers for `Veltkamp_aux_FLX`

The error-bound side gives `|x − hx| ≤ β^(s+cexp x)/2`. The format-side asks
`hx ∈ F(prec − s)`. Following Pff (`eqGe`, line 13641), the load-bearing piece
is `|q| ≥ β^(s+m−1)` (equivalently `cexp q ≥ s + cexp x`). The proof case-
splits on `x ≥ β^cx · (β^(prec−1) + β)` (the "comfortable" branch where the
rounding errors have room) vs the boundary branch (β specific values of `M_x`). -/

/-- **`q ≠ 0`**: in FLX with `x > 0` and `s ≥ 1`, the second rounding step is
nonzero. Reason: `x·C − x = x·β^s ≥ β^(m−1+s)` strictly exceeds `ulp(x)/2 =
β^(cx)/2`, so `p = round(x·C) > x`, hence `x − p < 0`, hence `q < 0`. -/
private theorem Veltkamp_q_ne_zero_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    Veltkamp_q_FLX beta prec choice s x ≠ 0 := by
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  -- Strategy: show p > x strictly, so x - p < 0, so q = round(x - p) < 0.
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  -- x ∈ [β^(m-1), β^m) since x > 0.
  have hx_lb : bpow beta (m - 1) ≤ x := by
    have := bpow_mag_le beta (ne_of_gt hx_pos)
    rwa [abs_of_pos hx_pos] at this
  -- p ≥ x · C (since x · C ∈ ? no, x · C may not be in F. But p ≥ x · β^s + x - β^(s+1+cx)/2).
  -- Actually simpler: x · C ≥ x · β^s + x > x + (ulp(x)/2). So round(x · C) ≥ x's successor.
  -- Let me try a more direct route: show p ≠ x.
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  have hxC_pos : 0 < x * Veltkamp_C beta s := by
    apply mul_pos hx_pos
    rw [hC_eq]; linarith [bpow_gt_0 beta s]
  -- |err_p| ≤ β^(cexp x·C)/2 ≤ β^(s+1+cx)/2 (using mag_xC_bounds).
  have h_mag_xC_le : mag beta (x * Veltkamp_C beta s) ≤ m + s + 1 :=
    (mag_xC_bounds beta (ne_of_gt hx_pos) (by linarith : (1 : ℤ) ≤ s)).2
  have h_err_p_bound : |p - x * Veltkamp_C beta s| ≤ bpow beta (s + 1 + cx) / 2 := by
    have h_p_eq : p = round beta (FLX_exp prec) (Znearest choice)
                       (x * Veltkamp_C beta s) := rfl
    rw [h_p_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                (x * Veltkamp_C beta s)
    rw [ulp_neq_0 beta _ (ne_of_gt hxC_pos)] at h
    have h_cexp : cexp beta (FLX_exp prec) (x * Veltkamp_C beta s)
                = mag beta (x * Veltkamp_C beta s) - prec := rfl
    have h_bpow_le : bpow beta (cexp beta (FLX_exp prec) (x * Veltkamp_C beta s))
                       ≤ bpow beta (s + 1 + cx) := by
      apply bpow_le
      rw [h_cexp, hcx_eq]; linarith
    linarith
  -- p ≥ x · C - β^(s+1+cx)/2 = x · β^s + x - β^(s+1+cx)/2.
  -- We want p > x, i.e., p - x > 0.
  -- p - x ≥ (x · C - β^(s+1+cx)/2) - x = x · β^s - β^(s+1+cx)/2.
  -- Show x · β^s > β^(s+1+cx)/2.
  -- x · β^s ≥ β^(m-1) · β^s = β^(s+m-1). β^(s+1+cx)/2 = β^(s+1+m-prec)/2.
  -- Need β^(s+m-1) > β^(s+1+m-prec)/2 iff β^(prec-2) > 1/2.
  -- For prec ≥ 2 (which we have from s ≥ 1 and s + 1 ≤ prec), β^(prec-2) ≥ β^0 = 1 > 1/2. ✓
  have h_bpow_s : 0 < bpow beta s := bpow_gt_0 _ _
  have h_xbs_lb : bpow beta (s + m - 1) ≤ x * bpow beta s := by
    calc bpow beta (s + m - 1)
        = bpow beta (m - 1) * bpow beta s := by rw [← bpow_plus]; congr 1; ring
      _ ≤ x * bpow beta s :=
          mul_le_mul_of_nonneg_right hx_lb (le_of_lt h_bpow_s)
  have h_bpow_compare : bpow beta (s + 1 + cx) / 2 < bpow beta (s + m - 1) := by
    have h_lt : bpow beta (s + 1 + cx) < bpow beta (s + m - 1) := by
      apply bpow_lt
      -- s + 1 + cx < s + m - 1 ↔ 1 + cx < m - 1 ↔ 2 ≤ m - cx = prec. ✓
      rw [hcx_eq]; linarith
    have h_pos : 0 < bpow beta (s + 1 + cx) := bpow_gt_0 _ _
    linarith
  -- p > x.
  have h_p_gt_x : x < p := by
    have h_abs_le : -(bpow beta (s + 1 + cx) / 2) ≤ p - x * Veltkamp_C beta s :=
      neg_le_of_abs_le h_err_p_bound
    -- p ≥ x · C - β^(s+1+cx)/2 = x · β^s + x - β^(s+1+cx)/2.
    have h_xC : x * Veltkamp_C beta s = x * bpow beta s + x := by rw [hC_eq]; ring
    have h_p_ge : x * bpow beta s + x - bpow beta (s + 1 + cx) / 2 ≤ p := by
      have : p ≥ x * Veltkamp_C beta s - bpow beta (s + 1 + cx) / 2 := by linarith
      linarith [this]
    -- x · β^s > β^(s+1+cx)/2.
    have : bpow beta (s + 1 + cx) / 2 < x * bpow beta s :=
      lt_of_lt_of_le h_bpow_compare h_xbs_lb
    linarith
  -- x - p < 0, so q = round(x - p) ≤ 0 with equality only if x - p = 0. But x ≠ p.
  have h_xmp_lt : x - p < 0 := by linarith
  have h_xmp_ne : x - p ≠ 0 := ne_of_lt h_xmp_lt
  -- q = round(x - p) and (x - p) ≠ 0, so q ≠ 0 (in FLX, round of nonzero nonzero in normal range).
  -- Specifically, |q - (x - p)| ≤ |x - p|/2 (relative error ≤ 1/2 from round-to-nearest).
  -- Hmm, simpler: |q| ≥ |x - p| - β^cexp(x-p)/2.
  -- We have |x - p| > 0; if q = 0, |q - (x - p)| = |x - p| > β^cexp/2, contradiction.
  intro hq_zero
  have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
  rw [h_q_eq] at hq_zero
  -- q = 0 and the round error ≤ ulp/2 means |x - p| ≤ ulp(x - p)/2.
  have h_err_q : |0 - (x - p)| ≤ ulp beta (FLX_exp prec) (x - p) / 2 := by
    rw [← hq_zero]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice (x - p)
    linarith
  rw [ulp_neq_0 beta _ h_xmp_ne] at h_err_q
  rw [zero_sub, abs_neg] at h_err_q
  -- |x - p| ≤ β^cexp(x-p)/2. But |x - p| = p - x > β^(s+1+cx)/2 ≥ β^cexp(x-p)/2 / ... hmm.
  -- Tighter: |x - p| ≥ x · β^s - β^(s+1+cx)/2 ≥ β^(s+m-1) - β^(s+1+cx)/2 > β^(s+m-1)/2.
  -- And β^cexp(x-p) ≤ β^(s+1+cx)? Not directly.
  -- Actually we have x - p < 0 and |x - p| = p - x. Use the bound directly.
  have h_abs_xmp : |x - p| = p - x := by
    rw [abs_of_neg h_xmp_lt]; ring
  -- p - x ≥ x · β^s - β^(s+1+cx)/2 ≥ β^(s+m-1) - β^(s+1+cx)/2.
  -- For s + 1 + cx < s + m - 1 (i.e., prec ≥ 2): β^(s+1+cx)/2 < β^(s+m-1)/2 < p - x.
  -- And bpow cexp(x-p) ≤ what? mag(x - p) is some integer. If x - p is "large", cexp is big.
  -- Hmm, no clean bound. Let me derive differently.
  -- |x - p| = p - x. p - x > β^(s+m-1) - β^(s+1+cx)/2. Need (p - x) > β^cexp(x-p)/2.
  -- Bound: cexp(x - p) = mag(x - p) - prec ≤ mag(x - p) - prec.
  -- We have |x - p| < β^mag(x - p), so |x - p| > β^(mag(x-p) - 1).
  -- β^cexp(x-p)/2 = β^(mag(x-p) - prec)/2 = β^(mag(x-p) - 1) / (2 β^(prec - 1)).
  -- So β^cexp(x-p)/2 ≤ |x-p| / (2 β^(prec - 1)) < |x - p| / 2 (for prec ≥ 2).
  -- So |x - p| > β^cexp(x-p)/2 (strict), contradicting h_err_q.
  -- Let's formalize: |x - p| / β^cexp(x-p) ≥ β^(prec - 1) > 1 for prec ≥ 2.
  -- Hmm need scaled_mantissa ≥ β^(prec-1).
  -- Actually simpler: mag(x - p) is defined as the integer e with β^(e-1) ≤ |x-p| < β^e.
  -- So β^(mag(x-p) - 1) ≤ |x - p|. And β^cexp(x-p) = β^(mag(x-p) - prec).
  -- Ratio: |x - p| / β^cexp ≥ β^(mag(x-p) - 1) / β^(mag(x-p) - prec) = β^(prec - 1).
  -- For prec ≥ 1, β^(prec - 1) ≥ 1, so |x - p| ≥ β^cexp. Hence |x - p| > β^cexp/2.
  have h_xmp_lb : bpow beta (mag beta (x - p) - 1) ≤ |x - p| := by
    exact bpow_mag_le beta h_xmp_ne
  have h_cexp_bound : bpow beta (cexp beta (FLX_exp prec) (x - p))
                      ≤ |x - p| := by
    show bpow beta (mag beta (x - p) - prec) ≤ |x - p|
    calc bpow beta (mag beta (x - p) - prec)
        ≤ bpow beta (mag beta (x - p) - 1) := bpow_le beta (by linarith)
      _ ≤ |x - p| := h_xmp_lb
  -- |x - p| ≤ β^cexp/2 < β^cexp ≤ |x - p|. Contradiction.
  have h_pos_cexp : 0 < bpow beta (cexp beta (FLX_exp prec) (x - p)) := bpow_gt_0 _ _
  linarith

/-- **eqGe at FLX, branch 1 (the "comfortable" case)**: when `x ≥ β^cx · (β^(prec−1) + β)`,
we have `|q| ≥ β^(s+m−1)`. The argument: `|q| ≥ |p − x| − |err_q|`, and `p − x ≥
x·β^s − |err_p|`, so `|q| ≥ x·β^s − |err_p| − |err_q| ≥ x·β^s − β^(s+1+cx)`. With
`x·β^s ≥ β^(s+m−1) + β^(s+1+cx)`, the bound closes. -/
private theorem Veltkamp_abs_q_ge_branch1_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_x_large : bpow beta (cexp beta (FLX_exp prec) x) *
                   (bpow beta (prec - 1) + (beta.val : ℝ)) ≤ x) :
    bpow beta (s + mag beta x - 1)
      ≤ |Veltkamp_q_FLX beta prec choice s x| := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  -- err_p bound: |p - x·C| ≤ β^(s+1+cx)/2.
  have hxC_pos : 0 < x * Veltkamp_C beta s := by
    apply mul_pos hx_pos
    rw [hC_eq]; linarith [bpow_gt_0 beta s]
  have h_mag_xC_le : mag beta (x * Veltkamp_C beta s) ≤ m + s + 1 :=
    (mag_xC_bounds beta hx_ne (by linarith : (1 : ℤ) ≤ s)).2
  have h_err_p : |p - x * Veltkamp_C beta s| ≤ bpow beta (s + 1 + cx) / 2 := by
    have h_p_eq : p = round beta (FLX_exp prec) (Znearest choice)
                       (x * Veltkamp_C beta s) := rfl
    rw [h_p_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice
                (x * Veltkamp_C beta s)
    rw [ulp_neq_0 beta _ (ne_of_gt hxC_pos)] at h
    have h_cexp : cexp beta (FLX_exp prec) (x * Veltkamp_C beta s)
                = mag beta (x * Veltkamp_C beta s) - prec := rfl
    have h_bpow_le : bpow beta (cexp beta (FLX_exp prec) (x * Veltkamp_C beta s))
                       ≤ bpow beta (s + 1 + cx) := by
      apply bpow_le
      rw [h_cexp, hcx_eq]; linarith
    linarith
  -- err_q bound: |q - (x - p)| ≤ β^(s+1+cx)/2.
  -- Need cexp(x - p) ≤ s + 1 + cx, which follows from mag(x - p) ≤ m + s + 1.
  have h_xmp_bound : |x - p| < bpow beta (m + s + 1) :=
    Veltkamp_abs_x_minus_p_lt_FLX beta prec hp choice hx_pos (by linarith) hs_hi
  have h_err_q : |q - (x - p)| ≤ bpow beta (s + 1 + cx) / 2 := by
    have h_q_eq : q = round beta (FLX_exp prec) (Znearest choice) (x - p) := rfl
    rw [h_q_eq]
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice (x - p)
    by_cases h_xmp_zero : x - p = 0
    · rw [h_xmp_zero, round_0, sub_zero, abs_zero]
      linarith [bpow_ge_0 beta (s + 1 + cx)]
    · rw [ulp_neq_0 beta _ h_xmp_zero] at h
      have h_mag_xmp_le : mag beta (x - p) ≤ m + s + 1 :=
        mag_le_bpow beta h_xmp_zero h_xmp_bound
      have h_cexp_xmp : cexp beta (FLX_exp prec) (x - p) ≤ s + 1 + cx := by
        show mag beta (x - p) - prec ≤ s + 1 + cx
        rw [hcx_eq]; linarith
      have h_bpow_le : bpow beta (cexp beta (FLX_exp prec) (x - p))
                          ≤ bpow beta (s + 1 + cx) := bpow_le beta h_cexp_xmp
      linarith
  -- p - x ≥ x · β^s - β^(s+1+cx)/2.
  have h_p_minus_x : x * bpow beta s - bpow beta (s + 1 + cx) / 2 ≤ p - x := by
    -- p - x · C = -(x · C - p). |p - x · C| ≤ β^(s+1+cx)/2, so p ≥ x · C - β^(s+1+cx)/2.
    -- p - x = (p - x · C) + (x · C - x) = (p - x · C) + x · β^s.
    have h_xC : x * Veltkamp_C beta s = x * bpow beta s + x := by rw [hC_eq]; ring
    have h_lb : -(bpow beta (s + 1 + cx) / 2) ≤ p - x * Veltkamp_C beta s :=
      neg_le_of_abs_le h_err_p
    linarith
  -- |q| ≥ (p - x) - |err_q| ≥ (x · β^s - β^(s+1+cx)/2) - β^(s+1+cx)/2 = x·β^s - β^(s+1+cx).
  have h_abs_q_lb : x * bpow beta s - bpow beta (s + 1 + cx) ≤ |q| := by
    -- q = (x - p) + err_q. |q| ≥ |x - p| - |err_q|.
    have h_re : |x - p| ≤ |q| + |q - (x - p)| := by
      have hh : x - p = q - (q - (x - p)) := by ring
      calc |x - p| = |q - (q - (x - p))| := by rw [← hh]
        _ ≤ |q| + |q - (x - p)| := abs_sub q (q - (x - p))
    have h_tri : |x - p| - |q - (x - p)| ≤ |q| := by linarith
    have hpx : p ≥ x := by
      have := h_p_minus_x
      have h_xbs_pos : 0 < x * bpow beta s := mul_pos hx_pos (bpow_gt_0 _ _)
      have h_xbs_ge : bpow beta (s + m - 1) ≤ x * bpow beta s := by
        have hx_lb : bpow beta (m - 1) ≤ x := by
          have := bpow_mag_le beta hx_ne
          rwa [abs_of_pos hx_pos] at this
        calc bpow beta (s + m - 1)
            = bpow beta (m - 1) * bpow beta s := by rw [← bpow_plus]; congr 1; ring
          _ ≤ x * bpow beta s :=
              mul_le_mul_of_nonneg_right hx_lb (le_of_lt (bpow_gt_0 _ _))
      have h_pow_lt : bpow beta (s + 1 + cx) ≤ bpow beta (s + m - 1) := by
        apply bpow_le; rw [hcx_eq]; linarith
      linarith
    have h_abs_xmp : |x - p| = p - x := by
      rw [abs_of_nonpos (by linarith : x - p ≤ 0)]; ring
    rw [h_abs_xmp] at h_tri
    linarith
  -- x · β^s ≥ (β^(m-1) + β^(cx+1)) · β^s = β^(s+m-1) + β^(s+1+cx).
  have h_xbs_ge : bpow beta (s + m - 1) + bpow beta (s + 1 + cx) ≤ x * bpow beta s := by
    have h_bps_pos : 0 < bpow beta s := bpow_gt_0 _ _
    have h_x_expand : bpow beta cx * (bpow beta (prec - 1) + (beta.val : ℝ))
                    = bpow beta (m - 1) + bpow beta (cx + 1) := by
      -- β^cx · β^(prec-1) = β^(cx + prec - 1) = β^(m - 1).
      -- β^cx · β.val = β^cx · β^1 = β^(cx + 1).
      have h1 : bpow beta cx * bpow beta (prec - 1) = bpow beta (m - 1) := by
        rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
      have h2 : bpow beta cx * (beta.val : ℝ) = bpow beta (cx + 1) := by
        rw [show bpow beta (cx + 1) = bpow beta cx * bpow beta 1 from by rw [← bpow_plus]]
        rw [show bpow beta 1 = (beta.val : ℝ) from by
          show ((beta.val : ℤ) : ℝ) ^ (1 : ℤ).toNat = _
          simp]
      linarith
    have h_x_ge : bpow beta (m - 1) + bpow beta (cx + 1) ≤ x := by
      rw [← h_x_expand]; exact h_x_large
    have h_step1 : (bpow beta (m - 1) + bpow beta (cx + 1)) * bpow beta s ≤ x * bpow beta s :=
      mul_le_mul_of_nonneg_right h_x_ge (le_of_lt h_bps_pos)
    have h_step2 : (bpow beta (m - 1) + bpow beta (cx + 1)) * bpow beta s
                 = bpow beta (s + m - 1) + bpow beta (s + 1 + cx) := by
      have ha : bpow beta (m - 1) * bpow beta s = bpow beta (s + m - 1) := by
        rw [← bpow_plus]; congr 1; ring
      have hb : bpow beta (cx + 1) * bpow beta s = bpow beta (s + 1 + cx) := by
        rw [← bpow_plus]; congr 1; ring
      linarith
    linarith
  -- Combine: |q| ≥ x·β^s - β^(s+1+cx) ≥ β^(s+m-1).
  linarith

/-- **eqGe at FLX, branch 2b (the exact-bpow boundary)**: when `x = β^(m−1)` exactly,
`x·C = β^(s+m−1) + β^(m−1)` is itself in `F(prec)`, so `p = x·C` exactly. Then
`x − p = -β^(s+m−1)` is in `F(prec)`, so `q = −β^(s+m−1)` exactly. Hence
`|q| = β^(s+m−1)` and the eqGe bound holds with equality. -/
private theorem Veltkamp_abs_q_ge_branch2b_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (hx_eq : x = bpow beta (mag beta x - 1))
    (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    bpow beta (s + mag beta x - 1)
      ≤ |Veltkamp_q_FLX beta prec choice s x| := by
  set m := mag beta x with hm_def
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  -- Step 1: x · C = β^(s+m-1) + β^(m-1) ∈ F(prec).
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  have h_xC_eq : x * Veltkamp_C beta s = bpow beta (s + m - 1) + bpow beta (m - 1) := by
    rw [hx_eq, hC_eq]
    have h_bpow_plus : bpow beta (m - 1) * bpow beta s = bpow beta (s + m - 1) := by
      rw [← bpow_plus]; congr 1; ring
    have := h_bpow_plus; linarith
  -- Step 2: x · C ∈ F(prec). It equals F2R⟨β^s + 1, m - 1⟩.
  have h_xC_F2R : x * Veltkamp_C beta s
                = F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩ := by
    rw [h_xC_eq]
    show bpow beta (s + m - 1) + bpow beta (m - 1)
       = ((((beta.val : ℤ) ^ s.toNat + 1 : ℤ) : ℝ)) * bpow beta (m - 1)
    have hs_nn : 0 ≤ s := by linarith
    have h_pow : (((beta.val : ℤ) ^ s.toNat : ℤ) : ℝ) = bpow beta s := IZR_Zpower beta hs_nn
    have h_lhs : bpow beta (s + m - 1) = bpow beta s * bpow beta (m - 1) := by
      rw [← bpow_plus]; congr 1; ring
    rw [h_lhs]
    have h_pow' : ((beta.val : ℝ) ^ s.toNat) = bpow beta s := by
      have : ((beta.val ^ s.toNat : ℤ) : ℝ) = bpow beta s := IZR_Zpower beta hs_nn
      push_cast at this; exact this
    rw [show (((beta.val : ℤ) ^ s.toNat + 1 : ℤ) : ℝ) * bpow beta (m - 1)
          = ((beta.val : ℝ) ^ s.toNat + 1) * bpow beta (m - 1) from by push_cast; ring]
    rw [h_pow']; ring
  have h_xC_format : generic_format beta (FLX_exp prec) (x * Veltkamp_C beta s) := by
    rw [h_xC_F2R]
    apply generic_format_F2R beta (FLX_exp prec) _ _
    intro h_ne
    -- cexp(F2R) ≤ m - 1.
    show FLX_exp prec (mag beta _) ≤ m - 1
    unfold FLX_exp
    have h_F2R_pos : 0 < F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩ := by
      rw [← h_xC_F2R]
      have hβs_pos : 0 < bpow beta s := bpow_gt_0 _ _
      have hβ_m_pos : 0 < bpow beta (m - 1) := bpow_gt_0 _ _
      rw [h_xC_eq]
      have h_eq : bpow beta (s + m - 1) = bpow beta s * bpow beta (m - 1) := by
        rw [← bpow_plus]; congr 1; ring
      have h_pos : 0 < bpow beta (s + m - 1) := bpow_gt_0 _ _
      linarith
    -- Need: mag(x · C) ≤ m - 1 + prec = m + prec - 1.
    -- We have x · C = β^(s+m-1) + β^(m-1) < 2 · β^(s+m-1) ≤ β · β^(s+m-1) = β^(s+m).
    -- So mag ≤ s + m. Need s + m ≤ m + prec - 1, i.e., s ≤ prec - 1. ✓.
    have h_F2R_lt : F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩
                   < bpow beta (m - 1 + prec) := by
      rw [← h_xC_F2R, h_xC_eq]
      -- s + m - 1 < m - 1 + prec ↔ s < prec, ✓ from s + 2 ≤ prec.
      have h1 : bpow beta (s + m - 1) < bpow beta (m + prec - 2) := bpow_lt beta (by linarith)
      have h2 : bpow beta (m - 1) ≤ bpow beta (m + prec - 2) := bpow_le beta (by linarith)
      have h3 : bpow beta (m + prec - 2) + bpow beta (m + prec - 2)
              ≤ bpow beta (m - 1 + prec) := by
        have h_double : bpow beta (m + prec - 2) + bpow beta (m + prec - 2)
                      = 2 * bpow beta (m + prec - 2) := by ring
        rw [h_double]
        have h_step : 2 * bpow beta (m + prec - 2) ≤ (beta.val : ℝ) * bpow beta (m + prec - 2) := by
          have h_pos : 0 < bpow beta (m + prec - 2) := bpow_gt_0 _ _
          nlinarith
        have h_β : (beta.val : ℝ) * bpow beta (m + prec - 2) = bpow beta (m - 1 + prec) := by
          have h_β_eq : (beta.val : ℝ) = bpow beta 1 := by
            show _ = ((beta.val : ℤ) : ℝ) ^ (1 : ℤ).toNat
            simp
          rw [h_β_eq, ← bpow_plus]; congr 1; ring
        linarith
      linarith
    have h_F2R_ne_zero : F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩ ≠ 0 := by
      have : 0 < F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩ := h_F2R_pos
      linarith
    have h_abs_F2R_lt : |F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩|
                       < bpow beta (m - 1 + prec) := by
      rw [abs_of_pos h_F2R_pos]; exact h_F2R_lt
    have h_mag_le : mag beta (F2R (beta := beta) ⟨(beta.val : ℤ) ^ s.toNat + 1, m - 1⟩)
                    ≤ m - 1 + prec :=
      mag_le_bpow beta h_F2R_ne_zero h_abs_F2R_lt
    linarith
  -- Step 3: p = x · C (round is identity on F).
  have h_p_eq : p = x * Veltkamp_C beta s := by
    show round beta (FLX_exp prec) (Znearest choice) (x * Veltkamp_C beta s)
       = x * Veltkamp_C beta s
    exact round_generic beta (FLX_exp prec) (Znearest choice) h_xC_format
  -- Step 4: x - p = -β^(s+m-1).
  have h_xmp_eq : x - p = -bpow beta (s + m - 1) := by
    rw [h_p_eq, h_xC_eq]
    have h_hx_re : x = bpow beta (m - 1) := hx_eq
    linarith
  -- Step 5: -β^(s+m-1) ∈ F(prec).
  have h_xmp_format : generic_format beta (FLX_exp prec) (x - p) := by
    rw [h_xmp_eq]
    apply generic_format_opp
    apply generic_format_bpow
    show FLX_exp prec (s + m - 1 + 1) ≤ s + m - 1
    unfold FLX_exp; linarith
  -- Step 6: q = x - p (round is identity).
  have h_q_eq : q = x - p := by
    show round beta (FLX_exp prec) (Znearest choice) (x - p) = (x - p)
    exact round_generic beta (FLX_exp prec) (Znearest choice) h_xmp_format
  -- Step 7: |q| = β^(s+m-1).
  rw [h_q_eq, h_xmp_eq, abs_neg, abs_of_pos (bpow_gt_0 _ _)]

/-- **eqGe at FLX, branch 2a (β−1 specific mantissa values)**: when
`x` lies in the half-open interval `[β^(m−1) + β^cx, β^(m−1) + β^(cx+1))`
(equivalently, `x ∈ F` with mantissa `M_x ∈ {β^(prec−1)+1, …, β^(prec−1)+β−1}`),
the explicit float `g₁ = β^(s+m−1) + β^(m−1) + β^(s+cx)`
(= `F2R⟨β^(prec−1) + β^(prec−s−1) + 1, s+cx⟩`) lies in `F(prec)` and satisfies
`g₁ ≤ x · C`. Hence `p = round(x · C) ≥ g₁`, so `p − x ≥ β^(s+m−1)`, and
`round_le_generic` applied to `−β^(s+m−1) ∈ F(prec)` gives
`q ≤ −β^(s+m−1)`, so `|q| ≥ β^(s+m−1)`. -/
private theorem Veltkamp_abs_q_ge_branch2a_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_x_lb : bpow beta (mag beta x - 1) + bpow beta (cexp beta (FLX_exp prec) x) ≤ x)
    (h_x_ub : x < bpow beta (mag beta x - 1)
                + bpow beta (cexp beta (FLX_exp prec) x + 1)) :
    bpow beta (s + mag beta x - 1)
      ≤ |Veltkamp_q_FLX beta prec choice s x| := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  have hβs_pos : 0 < bpow beta s := bpow_gt_0 _ _
  have h_xC_pos : 0 < x * Veltkamp_C beta s := by
    apply mul_pos hx_pos; rw [hC_eq]; linarith
  -- Useful bpow positivity facts.
  have h_bpow_sm1 : 0 < bpow beta (s + m - 1) := bpow_gt_0 _ _
  have h_bpow_m1 : 0 < bpow beta (m - 1) := bpow_gt_0 _ _
  have h_bpow_scx : 0 < bpow beta (s + cx) := bpow_gt_0 _ _
  have h_bpow_cx : 0 < bpow beta cx := bpow_gt_0 _ _
  have h_bpow_cx1 : 0 < bpow beta (cx + 1) := bpow_gt_0 _ _
  -- Cast/exponent helpers.
  have h_prec_sub_1_nn : 0 ≤ prec - 1 := by linarith
  have h_prec_sub_s_1_nn : 0 ≤ prec - s - 1 := by linarith
  have h_s_nn : 0 ≤ s := by linarith
  have h_pow_prec_1 : ((beta.val : ℝ)) ^ (prec - 1).toNat = bpow beta (prec - 1) := by
    have := IZR_Zpower beta h_prec_sub_1_nn
    push_cast at this; exact this
  have h_pow_prec_s_1 : ((beta.val : ℝ)) ^ (prec - s - 1).toNat
                      = bpow beta (prec - s - 1) := by
    have := IZR_Zpower beta h_prec_sub_s_1_nn
    push_cast at this; exact this
  -- Step 1: g₁ value as a real number.
  -- Mg = β^(prec-1) + β^(prec-s-1) + 1, viewed as an integer.
  set Mg : ℤ := (beta.val : ℤ) ^ (prec - 1).toNat
              + (beta.val : ℤ) ^ (prec - s - 1).toNat + 1 with hMg_def
  have h_Mg_real : (Mg : ℝ) = bpow beta (prec - 1) + bpow beta (prec - s - 1) + 1 := by
    show (((beta.val : ℤ) ^ (prec - 1).toNat
          + (beta.val : ℤ) ^ (prec - s - 1).toNat + 1 : ℤ) : ℝ)
       = bpow beta (prec - 1) + bpow beta (prec - s - 1) + 1
    push_cast
    rw [h_pow_prec_1, h_pow_prec_s_1]
  -- g₁ as a real number.
  set g₁ : ℝ := F2R (beta := beta) ⟨Mg, s + cx⟩ with hg₁_def
  -- Closed form for g₁.
  have h_g₁_value : g₁ = bpow beta (s + m - 1)
                       + bpow beta (m - 1) + bpow beta (s + cx) := by
    show (Mg : ℝ) * bpow beta (s + cx)
       = bpow beta (s + m - 1) + bpow beta (m - 1) + bpow beta (s + cx)
    rw [h_Mg_real]
    have h_t1 : bpow beta (prec - 1) * bpow beta (s + cx) = bpow beta (s + m - 1) := by
      rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
    have h_t2 : bpow beta (prec - s - 1) * bpow beta (s + cx) = bpow beta (m - 1) := by
      rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
    have h_expand :
        (bpow beta (prec - 1) + bpow beta (prec - s - 1) + 1) * bpow beta (s + cx)
        = bpow beta (prec - 1) * bpow beta (s + cx)
        + bpow beta (prec - s - 1) * bpow beta (s + cx)
        + bpow beta (s + cx) := by ring
    rw [h_expand, h_t1, h_t2]
  have h_g₁_pos : 0 < g₁ := by rw [h_g₁_value]; linarith
  -- Step 2: g₁ < β^(s+m), so mag(g₁) ≤ s+m and cexp(g₁) ≤ s+cx.
  -- Key inequality: β^(m-1) + β^(s+cx) < (β-1) · β^(s+m-1).
  -- Both LHS terms are ≤ β^(m-1) since s+cx = s+m-prec ≤ m-2 ≤ m-1.
  -- Also β^(s+m-1) ≥ β^s · β^(m-1) ≥ 4·β^(m-1) (s ≥ 2). So:
  --   β^(m-1) + β^(s+cx) ≤ 2·β^(m-1) ≤ (β-1)·β^(s+m-1) when (β-1)·β^s ≥ 2.
  -- For β=2, s≥2: (β-1)·β^s = 1·4 = 4 ≥ 2 ✓.
  -- For β≥3, s≥2: (β-1)·β^s ≥ 2·9 = 18 ≥ 2 ✓.
  have h_scx_le_m1 : s + cx ≤ m - 1 := by rw [hcx_eq]; linarith
  have h_bpow_scx_le_m1 : bpow beta (s + cx) ≤ bpow beta (m - 1) :=
    bpow_le beta h_scx_le_m1
  have h_bps_ge_4 : 4 ≤ bpow beta s := by
    have h2 : bpow beta 2 ≤ bpow beta s := bpow_le beta hs_lo
    have h_pow2 : bpow beta 2 = (beta.val : ℝ) * (beta.val : ℝ) := by
      show ((beta.val : ℤ) : ℝ) ^ (2 : ℤ).toNat = _
      simp; ring
    have h2_ge_4 : 4 ≤ bpow beta 2 := by rw [h_pow2]; nlinarith
    linarith
  -- g₁ < β · β^(s+m-1) = β^(s+m).
  have h_g₁_lt : g₁ < bpow beta (s + m) := by
    rw [h_g₁_value]
    have h_β_sm : bpow beta (s + m) = (beta.val : ℝ) * bpow beta (s + m - 1) := by
      have : bpow beta (s + m) = bpow beta 1 * bpow beta (s + m - 1) := by
        rw [← bpow_plus]; congr 1; ring
      rw [this, bpow_one]
    rw [h_β_sm]
    -- β · β^(s+m-1) - β^(s+m-1) = (β-1) · β^(s+m-1).
    -- Want: β^(m-1) + β^(s+cx) < (β-1) · β^(s+m-1).
    -- Use β^(s+m-1) = β^s · β^(m-1), and β^s ≥ 4 (s ≥ 2).
    have h_bps_factor : bpow beta (s + m - 1) = bpow beta s * bpow beta (m - 1) := by
      rw [← bpow_plus]; congr 1; ring
    -- β^(m-1) + β^(s+cx) ≤ 2·β^(m-1).
    have h_two_terms : bpow beta (m - 1) + bpow beta (s + cx) ≤ 2 * bpow beta (m - 1) := by
      linarith
    -- (β-1)·β^(s+m-1) = (β-1)·β^s·β^(m-1) ≥ (β-1)·4·β^(m-1).
    -- For β=2: (β-1)·4 = 4 ≥ 2 ✓.
    -- For β≥3: (β-1)·4 ≥ 8 ≥ 2 ✓.
    have h_β_m_1 : 1 ≤ (beta.val : ℝ) - 1 := by linarith
    have h_β_4 : 4 ≤ (beta.val : ℝ) * bpow beta s - bpow beta s := by
      have : ((beta.val : ℝ) - 1) * bpow beta s ≥ 1 * 4 := by
        apply mul_le_mul h_β_m_1 h_bps_ge_4 (by norm_num) (by linarith)
      nlinarith [bpow_gt_0 beta s]
    nlinarith [h_two_terms, h_bps_factor, h_bpow_m1, h_bpow_scx, h_bpow_sm1, h_bps_ge_4]
  -- g₁ ∈ F(prec).
  have h_g₁_ne_zero : g₁ ≠ 0 := ne_of_gt h_g₁_pos
  have h_abs_g₁_lt : |g₁| < bpow beta (s + m) := by
    rw [abs_of_pos h_g₁_pos]; exact h_g₁_lt
  have h_mag_g₁_le : mag beta g₁ ≤ s + m := mag_le_bpow beta h_g₁_ne_zero h_abs_g₁_lt
  have h_g₁_format : generic_format beta (FLX_exp prec) g₁ := by
    apply generic_format_F2R beta (FLX_exp prec) Mg (s + cx)
    intro _
    show FLX_exp prec (mag beta g₁) ≤ s + cx
    unfold FLX_exp
    rw [hcx_eq]; linarith
  -- Step 3: g₁ ≤ x · C.
  -- x · C = x · (β^s + 1) = x · β^s + x.
  -- We have x ≥ β^(m-1) + β^cx, so:
  --   x · β^s ≥ β^(s+m-1) + β^(s+cx)
  --   x ≥ β^(m-1) + β^cx
  -- Sum: x · C ≥ β^(s+m-1) + β^(s+cx) + β^(m-1) + β^cx = g₁ + β^cx > g₁.
  have h_g₁_le_xC : g₁ ≤ x * Veltkamp_C beta s := by
    rw [hC_eq]
    have h_xC_expand : x * (bpow beta s + 1) = x * bpow beta s + x := by ring
    rw [h_xC_expand]
    -- x · β^s ≥ (β^(m-1) + β^cx) · β^s = β^(s+m-1) + β^(s+cx).
    have h1 : (bpow beta (m - 1) + bpow beta cx) * bpow beta s ≤ x * bpow beta s :=
      mul_le_mul_of_nonneg_right h_x_lb (le_of_lt hβs_pos)
    have h_dist : (bpow beta (m - 1) + bpow beta cx) * bpow beta s
                = bpow beta (s + m - 1) + bpow beta (s + cx) := by
      have ha : bpow beta (m - 1) * bpow beta s = bpow beta (s + m - 1) := by
        rw [← bpow_plus]; congr 1; ring
      have hb : bpow beta cx * bpow beta s = bpow beta (s + cx) := by
        rw [← bpow_plus]; congr 1; ring
      linarith
    -- Now g₁ + β^cx ≤ x · β^s + x (using x ≥ β^(m-1) + β^cx).
    rw [h_g₁_value]
    linarith [h_x_lb, h_bpow_cx]
  -- Step 4: p ≥ g₁ via round_ge_generic.
  have h_p_ge : g₁ ≤ p := by
    show g₁ ≤ round beta (FLX_exp prec) (Znearest choice) (x * Veltkamp_C beta s)
    exact round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
      h_g₁_format h_g₁_le_xC
  -- Step 5: p - x ≥ β^(s+m-1).
  -- g₁ - x = β^(s+m-1) + β^(m-1) + β^(s+cx) - x.
  -- Using x < β^(m-1) + β^(cx+1):
  --   g₁ - x > β^(s+m-1) + β^(s+cx) - β^(cx+1) = β^(s+m-1) + β^(cx+1)·(β^(s-1) - 1).
  -- For s ≥ 2, β ≥ 2: β^(s-1) ≥ β ≥ 2 > 1, so β^(s+cx) - β^(cx+1) > 0.
  have h_β_pow_s_cx_ge_cx_1 : bpow beta (cx + 1) ≤ bpow beta (s + cx) := by
    apply bpow_le beta; linarith
  have h_p_minus_x_ge : bpow beta (s + m - 1) ≤ p - x := by
    have h_g_diff : bpow beta (s + m - 1) ≤ g₁ - x := by
      rw [h_g₁_value]
      -- β^(s+m-1) ≤ (β^(s+m-1) + β^(m-1) + β^(s+cx)) - x
      -- ↔ x ≤ β^(m-1) + β^(s+cx)
      -- We have x < β^(m-1) + β^(cx+1) ≤ β^(m-1) + β^(s+cx). ✓
      linarith [h_x_ub, h_β_pow_s_cx_ge_cx_1]
    linarith
  -- Step 6: x - p ≤ -β^(s+m-1) ∈ F(prec).
  have h_neg_bpow_format : generic_format beta (FLX_exp prec) (-bpow beta (s + m - 1)) := by
    apply generic_format_opp
    apply generic_format_bpow
    show FLX_exp prec (s + m - 1 + 1) ≤ s + m - 1
    unfold FLX_exp; linarith
  have h_xmp_le : x - p ≤ -bpow beta (s + m - 1) := by linarith
  -- Step 7: q ≤ -β^(s+m-1) via round_le_generic.
  have h_q_le : q ≤ -bpow beta (s + m - 1) := by
    show round beta (FLX_exp prec) (Znearest choice) (x - p) ≤ -bpow beta (s + m - 1)
    exact round_le_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
      h_neg_bpow_format h_xmp_le
  -- Step 8: |q| ≥ β^(s+m-1).
  have h_q_neg : q ≤ 0 := by linarith
  rw [abs_of_nonpos h_q_neg]
  linarith

/-- **Discreteness of `F(FLX, prec)`**: for `x ∈ F(prec)` with `x > 0` and
`x > β^(m-1)` (strict), the next representable value above `β^(m-1)` is
`β^(m-1) + β^cx`, so `x ≥ β^(m-1) + β^cx`. -/
private theorem Veltkamp_x_lb_above_bpow_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x)
    (hx_gt : bpow beta (mag beta x - 1) < x) :
    bpow beta (mag beta x - 1) + bpow beta (cexp beta (FLX_exp prec) x) ≤ x := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have h_bpow_cx_pos : 0 < bpow beta cx := bpow_gt_0 _ _
  -- Get x = M · β^cx for some integer M.
  set M : ℤ := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hM_def
  have h_x_F2R : x = (M : ℝ) * bpow beta cx := Fx
  -- β^(prec-1) < M as real (from x > β^(m-1)).
  have h_M_gt : bpow beta (prec - 1) < (M : ℝ) := by
    have h_bpow_split : bpow beta (m - 1) = bpow beta (prec - 1) * bpow beta cx := by
      rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
    have hx_gt' : bpow beta (prec - 1) * bpow beta cx < (M : ℝ) * bpow beta cx := by
      rw [← h_bpow_split, ← h_x_F2R]; exact hx_gt
    exact (mul_lt_mul_iff_of_pos_right h_bpow_cx_pos).mp hx_gt'
  -- Cast to integer: β^(prec-1) < M, hence M ≥ β^(prec-1) + 1.
  have h_prec_sub_1_nn : 0 ≤ prec - 1 := by linarith
  have h_pow_real : (((beta.val : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) = bpow beta (prec - 1) :=
    IZR_Zpower beta h_prec_sub_1_nn
  have h_pow_real_pushed : ((beta.val : ℝ)) ^ (prec - 1).toNat = bpow beta (prec - 1) := by
    have := h_pow_real; push_cast at this; exact this
  have h_M_int_gt : (beta.val : ℤ) ^ (prec - 1).toNat < M := by
    have : (((beta.val : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) < (M : ℝ) := by
      rw [h_pow_real]; exact h_M_gt
    exact_mod_cast this
  have h_M_ge : (beta.val : ℤ) ^ (prec - 1).toNat + 1 ≤ M := by linarith
  -- x ≥ (β^(prec-1) + 1) · β^cx = β^(m-1) + β^cx.
  have h_M_real_ge : (((beta.val : ℤ) ^ (prec - 1).toNat + 1 : ℤ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast h_M_ge
  have h_step : (((beta.val : ℤ) ^ (prec - 1).toNat + 1 : ℤ) : ℝ) * bpow beta cx
              ≤ (M : ℝ) * bpow beta cx :=
    mul_le_mul_of_nonneg_right h_M_real_ge (le_of_lt h_bpow_cx_pos)
  have h_left_eq : (((beta.val : ℤ) ^ (prec - 1).toNat + 1 : ℤ) : ℝ) * bpow beta cx
                 = bpow beta (m - 1) + bpow beta cx := by
    have h_split : bpow beta (m - 1) = bpow beta (prec - 1) * bpow beta cx := by
      rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
    push_cast
    rw [h_pow_real_pushed, h_split]
    ring
  linarith [h_x_F2R, h_step, h_left_eq]

/-- **Veltkamp's eqGe at FLX**: for `x ∈ F(prec)` with `x > 0`,
`2 ≤ s`, `s + 2 ≤ prec`, the second rounding error satisfies
`|q| ≥ β^(s + mag(x) − 1)`, equivalently `cexp(q) ≥ s + cexp(x)`.

This is the load-bearing inequality for the format-side of
`Veltkamp_aux`: it forces `q` to live at exponent at least `s + cx`,
which is what allows `hx = q + p` to be representable at the coarser
precision `prec − s`. -/
theorem Veltkamp_eqGe_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    bpow beta (s + mag beta x - 1)
      ≤ |Veltkamp_q_FLX beta prec choice s x| := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  -- Case 1: x = β^(m-1) (the exact bpow boundary).
  by_cases h_x_eq : x = bpow beta (m - 1)
  · exact Veltkamp_abs_q_ge_branch2b_FLX beta prec hp choice h_x_eq hs_lo hs_hi
  -- Case 2: x > β^(m-1). Establish x ≥ β^(m-1) + β^cx using integer-mantissa discreteness.
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have h_x_strict : bpow beta (m - 1) < x := by
    have h_mag_lo : bpow beta (m - 1) ≤ |x| := bpow_mag_le beta hx_ne
    rw [abs_of_pos hx_pos] at h_mag_lo
    rcases lt_or_eq_of_le h_mag_lo with h | h
    · exact h
    · exact absurd h.symm h_x_eq
  have h_x_lb : bpow beta (m - 1) + bpow beta cx ≤ x :=
    Veltkamp_x_lb_above_bpow_FLX beta prec hp Fx hx_pos h_x_strict
  -- Sub-case: x ≥ β^(m-1) + β^(cx+1) (branch 1 "comfortable") vs x < ... (branch 2a).
  by_cases h_upper : bpow beta (m - 1) + bpow beta (cx + 1) ≤ x
  · -- Branch 1: convert form `bpow cx * (bpow (prec-1) + β) = bpow (m-1) + bpow (cx+1)`.
    apply Veltkamp_abs_q_ge_branch1_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
    have h1 : bpow beta cx * bpow beta (prec - 1) = bpow beta (m - 1) := by
      rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
    have h2 : bpow beta cx * (beta.val : ℝ) = bpow beta (cx + 1) := by
      have hβ_eq : (beta.val : ℝ) = bpow beta 1 := by rw [bpow_one]
      rw [hβ_eq, ← bpow_plus]
    have h_conv : bpow beta cx * (bpow beta (prec - 1) + (beta.val : ℝ))
                = bpow beta (m - 1) + bpow beta (cx + 1) := by
      rw [mul_add, h1, h2]
    rw [h_conv]; exact h_upper
  · -- Branch 2a.
    push_neg at h_upper
    exact Veltkamp_abs_q_ge_branch2a_FLX beta prec hp choice hx_pos hs_lo hs_hi
      h_x_lb h_upper

/-! ### Format-side preparation: `p` and `q` at exponent `s + cx`

The format-side argument needs `hx = p + q` expressed as a multiple of
`β^(s+cx)`. Both `p` and `q` are in `F(prec)`; eqGe gives `cexp(q) ≥ s+cx`,
and in Case A (`mag(x·C) = m+s`) the round-monotonicity gives
`cexp(p) ≥ s+cx`. From there, `F2R_change_exp` rewrites each as an
integer multiple of `β^(s+cx)`. -/

/-- **`q` at exponent `s + cx`**: from eqGe `|q| ≥ β^(s+m−1)`,
`cexp(q) ≥ s+cx`, so `q` is an integer multiple of `β^(s+cx)`. -/
private theorem Veltkamp_q_at_scx_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    ∃ Mq : ℤ, Veltkamp_q_FLX beta prec choice s x
              = (Mq : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  -- q ∈ F(prec).
  have Fq : generic_format beta (FLX_exp prec) q := by
    show generic_format beta (FLX_exp prec)
      (round beta (FLX_exp prec) (Znearest choice)
        (x - Veltkamp_p_FLX beta prec choice s x))
    exact generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) _ _
  -- |q| ≥ β^(s+m-1) (eqGe).
  have h_q_abs_ge : bpow beta (s + m - 1) ≤ |q| :=
    Veltkamp_eqGe_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_bpow_pos : 0 < bpow beta (s + m - 1) := bpow_gt_0 _ _
  have hq_ne : q ≠ 0 := by
    intro h; rw [h, abs_zero] at h_q_abs_ge; linarith
  -- mag(q) ≥ s + m.
  have h_mag_q_ge : s + m ≤ mag beta q := by
    apply mag_ge_bpow beta
    have h_eq : s + m - 1 = (s + m) - 1 := by ring
    rw [← h_eq]; exact h_q_abs_ge
  -- cexp(q) ≥ s + cx.
  set cq := cexp beta (FLX_exp prec) q with hcq_def
  have h_cexp_q_ge : s + cx ≤ cq := by
    show s + cx ≤ FLX_exp prec (mag beta q)
    unfold FLX_exp
    rw [hcx_eq]; linarith
  -- Apply F2R_change_exp to drop the exponent.
  set Mz : ℤ := Ztrunc (scaled_mantissa beta (FLX_exp prec) q) with hMz_def
  have h_q_F2R : q = F2R (beta := beta) ⟨Mz, cq⟩ := Fq
  refine ⟨Mz * (beta.val : ℤ) ^ (cq - (s + cx)).toNat, ?_⟩
  rw [h_q_F2R]
  exact F2R_change_exp (beta := beta) (s + cx) Mz cq h_cexp_q_ge

/-- **`p` at exponent `s + cx`**: `mag(x·C) ≥ m+s` (from `mag_xC_bounds`),
so `p ≥ β^(m+s−1)` by round-monotonicity, hence `mag(p) ≥ m+s`, so
`cexp(p) ≥ s+cx`, and `p` is an integer multiple of `β^(s+cx)`. Note:
this holds in *both* Case A (`mag(x·C) = m+s`) and Case B
(`mag(x·C) = m+s+1`) since we only need the lower bound. -/
private theorem Veltkamp_p_at_scx_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    ∃ Mp : ℤ, Veltkamp_p_FLX beta prec choice s x
              = (Mp : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hC_eq : Veltkamp_C beta s = bpow beta s + 1 := rfl
  -- x · C > 0.
  have hxC_pos : 0 < x * Veltkamp_C beta s := by
    apply mul_pos hx_pos; rw [hC_eq]; linarith [bpow_gt_0 beta s]
  have hxC_ne : x * Veltkamp_C beta s ≠ 0 := ne_of_gt hxC_pos
  -- p ∈ F(prec).
  have Fp : generic_format beta (FLX_exp prec) p := by
    show generic_format beta (FLX_exp prec)
      (round beta (FLX_exp prec) (Znearest choice) (x * Veltkamp_C beta s))
    exact generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) _ _
  -- β^(m+s-1) ≤ x · C: from mag(x·C) ≥ m+s and bpow_mag_le.
  have h_mag_xC_ge : m + s ≤ mag beta (x * Veltkamp_C beta s) :=
    (mag_xC_bounds beta hx_ne (by linarith : (1 : ℤ) ≤ s)).1
  have h_xC_ge : bpow beta (m + s - 1) ≤ x * Veltkamp_C beta s := by
    have h_mag := bpow_mag_le beta hxC_ne
    rw [abs_of_pos hxC_pos] at h_mag
    have h_step : bpow beta (m + s - 1)
                ≤ bpow beta (mag beta (x * Veltkamp_C beta s) - 1) :=
      bpow_le beta (by linarith)
    linarith
  -- β^(m+s-1) ∈ F(prec).
  have h_bpow_format : generic_format beta (FLX_exp prec) (bpow beta (m + s - 1)) := by
    apply generic_format_bpow
    show FLX_exp prec (m + s - 1 + 1) ≤ m + s - 1
    unfold FLX_exp; linarith
  -- p ≥ β^(m+s-1) via round_ge_generic.
  have h_p_ge : bpow beta (m + s - 1) ≤ p := by
    show bpow beta (m + s - 1)
       ≤ round beta (FLX_exp prec) (Znearest choice) (x * Veltkamp_C beta s)
    exact round_ge_generic beta (FLX_exp prec) (FLX_exp_valid prec hp) _
      h_bpow_format h_xC_ge
  have h_p_pos : 0 < p := by
    have h_bpow_pos : 0 < bpow beta (m + s - 1) := bpow_gt_0 _ _
    linarith
  have hp_ne : p ≠ 0 := ne_of_gt h_p_pos
  -- mag(p) ≥ m + s.
  have h_mag_p_ge : m + s ≤ mag beta p := by
    apply mag_ge_bpow beta
    rw [abs_of_pos h_p_pos]
    have : m + s - 1 = (m + s) - 1 := by ring
    rw [← this]; exact h_p_ge
  -- cexp(p) ≥ s + cx.
  set cp := cexp beta (FLX_exp prec) p with hcp_def
  have h_cexp_p_ge : s + cx ≤ cp := by
    show s + cx ≤ FLX_exp prec (mag beta p)
    unfold FLX_exp
    rw [hcx_eq]; linarith
  -- Apply F2R_change_exp.
  set Mz : ℤ := Ztrunc (scaled_mantissa beta (FLX_exp prec) p) with hMz_def
  have h_p_F2R : p = F2R (beta := beta) ⟨Mz, cp⟩ := Fp
  refine ⟨Mz * (beta.val : ℤ) ^ (cp - (s + cx)).toNat, ?_⟩
  rw [h_p_F2R]
  exact F2R_change_exp (beta := beta) (s + cx) Mz cp h_cexp_p_ge

/-- **Format-side of `Veltkamp_aux_FLX`**: for `x > 0` in `F(FLX, prec)`,
`2 ≤ s ≤ prec − 2`, `hx ∈ F(prec − s)`.

The proof combines the two helpers above with the error bound from
`Veltkamp_aux_FLX` to get `hx = M · β^(s+cx)` with `|M| ≤ β^(prec−s)`.
The standard case `|M| < β^(prec−s)` uses `generic_format_F2R`; the
boundary case `|M| = β^(prec−s)` (so `hx = β^m`) uses
`generic_format_bpow`. This works in *both* Case A (`mag(x·C) = m+s`)
and Case B (`mag(x·C) = m+s+1`) since the proof only depends on the
keystone bound `|x − hx| ≤ β^(s+cx)/2` plus the `s+cx` exponent form
of `p` and `q`. -/
theorem Veltkamp_hx_format_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    generic_format beta (FLX_exp (prec - s))
      (Veltkamp_hx_FLX beta prec choice s x) := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  set hx := Veltkamp_hx_FLX beta prec choice s x with hhx_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have h_bpow_scx_pos : 0 < bpow beta (s + cx) := bpow_gt_0 _ _
  -- hx = q + p.
  have h_hxExact : hx = q + p :=
    hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  -- Express p and q at exponent s + cx.
  obtain ⟨Mp, hp_eq⟩ :=
    Veltkamp_p_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  obtain ⟨Mq, hq_eq⟩ :=
    Veltkamp_q_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  -- hx = (Mp + Mq) · β^(s+cx).
  set M_total : ℤ := Mq + Mp with hM_total_def
  have h_hx_form : hx = ((M_total : ℤ) : ℝ) * bpow beta (s + cx) := by
    rw [hcx_def, h_hxExact, hq_def, hp_def, hq_eq, hp_eq, hM_total_def]
    push_cast; ring
  -- Error bound and hx > 0.
  have h_err : |x - hx| ≤ bpow beta (s + cx) / 2 :=
    Veltkamp_aux_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_x_lt_bpow : x < bpow beta m := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos hx_pos] at this
  -- |hx| < β^m + β^(s+cx)/2.
  have h_hx_abs_lt : |hx| < bpow beta m + bpow beta (s + cx) / 2 := by
    have h_tri : |hx| ≤ |x| + |x - hx| := by
      calc |hx| = |-(x - hx) + x| := by ring_nf
        _ ≤ |-(x - hx)| + |x| := abs_add_le _ _
        _ = |x| + |x - hx| := by rw [abs_neg]; ring
    rw [abs_of_pos hx_pos] at h_tri
    linarith
  -- β^m = β^(prec-s) · β^(s+cx).
  have h_prec_s_nn : 0 ≤ prec - s := by linarith
  have h_bpow_m_eq : bpow beta m = bpow beta (prec - s) * bpow beta (s + cx) := by
    rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
  -- 2·|M_total| < 2·β^(prec-s) + 1 (as integers).
  have h_pow_real_pushed : ((beta.val : ℝ)) ^ (prec - s).toNat = bpow beta (prec - s) := by
    have := IZR_Zpower beta h_prec_s_nn; push_cast at this; exact this
  have h_M_abs_cast : ((|M_total| : ℤ) : ℝ) = |((M_total : ℤ) : ℝ)| := by push_cast; rfl
  have h_hx_abs_mul : |hx| = ((|M_total| : ℤ) : ℝ) * bpow beta (s + cx) := by
    rw [h_hx_form, abs_mul, abs_of_pos h_bpow_scx_pos]
    rw [h_M_abs_cast]
  have h_strict_real : ((|M_total| : ℤ) : ℝ) < bpow beta (prec - s) + 1/2 := by
    have h_step : ((|M_total| : ℤ) : ℝ) * bpow beta (s + cx)
                  < bpow beta m + bpow beta (s + cx) / 2 := by
      rw [← h_hx_abs_mul]; exact h_hx_abs_lt
    rw [h_bpow_m_eq] at h_step
    have h_factor : bpow beta (prec - s) * bpow beta (s + cx) + bpow beta (s + cx) / 2
                  = (bpow beta (prec - s) + 1/2) * bpow beta (s + cx) := by ring
    rw [h_factor] at h_step
    exact (mul_lt_mul_iff_of_pos_right h_bpow_scx_pos).mp h_step
  have h_2M_strict_int : 2 * |M_total| < 2 * (beta.val : ℤ) ^ (prec - s).toNat + 1 := by
    have h_real : (((2 * |M_total| : ℤ) : ℝ))
                  < (((2 * (beta.val : ℤ) ^ (prec - s).toNat + 1) : ℤ) : ℝ) := by
      push_cast
      rw [h_pow_real_pushed]
      linarith
    exact_mod_cast h_real
  have h_M_abs_le : |M_total| ≤ (beta.val : ℤ) ^ (prec - s).toNat := by omega
  -- Side case on |M_total| = β^(prec-s).
  by_cases h_boundary : |M_total| = (beta.val : ℤ) ^ (prec - s).toNat
  · -- |M_total| = β^(prec-s). Since hx > 0, M_total > 0, so M_total = β^(prec-s).
    -- hx = β^(prec-s) · β^(s+cx) = β^m.
    have h_hx_pos : 0 < hx := by
      have h_err_abs : |x - hx| < x := by
        -- β^(s+cx)/2 = β^(s+m-prec)/2 ≤ β^(m-2)/2 < β^(m-1) ≤ x.
        have h_xs_le : bpow beta (s + cx) ≤ bpow beta (m - 2) := by
          apply bpow_le beta; rw [hcx_eq]; linarith
        have h_m2_lt : bpow beta (m - 2) / 2 < bpow beta (m - 1) := by
          have h_half_lt : bpow beta (m - 2) / 2 ≤ bpow beta (m - 2) := by
            have := bpow_gt_0 beta (m - 2); linarith
          have h_strict : bpow beta (m - 2) < bpow beta (m - 1) := bpow_lt beta (by linarith)
          linarith
        have h_x_ge : bpow beta (m - 1) ≤ x := by
          have := bpow_mag_le beta (ne_of_gt hx_pos)
          rw [abs_of_pos hx_pos] at this; exact this
        have := bpow_gt_0 beta (s + cx)
        linarith
      have h_x_le : x - |x - hx| ≤ hx := by
        rcases le_or_lt (x - hx) 0 with h | h
        · rw [abs_of_nonpos h]; linarith
        · rw [abs_of_pos h]; linarith
      linarith
    have h_M_total_pos : 0 < M_total := by
      have h_real_pos : 0 < ((M_total : ℤ) : ℝ) := by
        have : 0 < ((M_total : ℤ) : ℝ) * bpow beta (s + cx) := by
          rw [← h_hx_form]; exact h_hx_pos
        exact (mul_pos_iff_of_pos_right h_bpow_scx_pos).mp this
      exact_mod_cast h_real_pos
    have h_M_eq : M_total = (beta.val : ℤ) ^ (prec - s).toNat := by
      have : |M_total| = M_total := abs_of_pos h_M_total_pos
      linarith [h_boundary]
    -- hx = β^m.
    have h_hx_eq_bpow : hx = bpow beta m := by
      rw [h_hx_form, h_M_eq]
      push_cast
      rw [h_pow_real_pushed]
      rw [h_bpow_m_eq]
    rw [h_hx_eq_bpow]
    apply generic_format_bpow
    show FLX_exp (prec - s) (m + 1) ≤ m
    unfold FLX_exp; linarith
  · -- |M_total| < β^(prec-s). Apply generic_format_F2R.
    have h_M_abs_lt : |M_total| < (beta.val : ℤ) ^ (prec - s).toNat := by
      cases lt_or_eq_of_le h_M_abs_le with
      | inl h => exact h
      | inr h => exact absurd h h_boundary
    -- hx = F2R⟨M_total, s+cx⟩.
    have h_hx_F2R : hx = F2R (beta := beta) ⟨M_total, s + cx⟩ := h_hx_form
    rw [h_hx_F2R]
    apply generic_format_F2R beta (FLX_exp (prec - s)) M_total (s + cx)
    intro h_M_ne_zero
    show FLX_exp (prec - s)
          (mag beta (F2R (beta := beta) ⟨M_total, s + cx⟩)) ≤ s + cx
    unfold FLX_exp
    -- mag(hx) ≤ m (from |hx| < β^(prec-s) · β^(s+cx) = β^m).
    have h_hx_abs_lt_bpow_m : |hx| < bpow beta m := by
      rw [h_hx_abs_mul]
      have h_M_real_lt : ((|M_total| : ℤ) : ℝ) < bpow beta (prec - s) := by
        have : (((|M_total| : ℤ)) : ℝ) < (((beta.val : ℤ) ^ (prec - s).toNat : ℤ) : ℝ) := by
          exact_mod_cast h_M_abs_lt
        rw [show (((beta.val : ℤ) ^ (prec - s).toNat : ℤ) : ℝ)
              = bpow beta (prec - s) from by
              rw [show (((beta.val : ℤ) ^ (prec - s).toNat : ℤ) : ℝ)
                    = ((beta.val : ℝ)) ^ (prec - s).toNat from by push_cast; rfl,
                  h_pow_real_pushed]] at this
        exact this
      rw [h_bpow_m_eq]
      exact (mul_lt_mul_iff_of_pos_right h_bpow_scx_pos).mpr h_M_real_lt
    have h_hx_ne : F2R (beta := beta) ⟨M_total, s + cx⟩ ≠ 0 := by
      rw [← h_hx_F2R]
      intro h_zero
      have : (M_total : ℝ) * bpow beta (s + cx) = 0 := by
        rw [← h_hx_form]; exact h_zero
      have h_M_real_zero : (M_total : ℝ) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exfalso; linarith [h_bpow_scx_pos]
      exact h_M_ne_zero (by exact_mod_cast h_M_real_zero)
    have h_mag_le : mag beta (F2R (beta := beta) ⟨M_total, s + cx⟩) ≤ m := by
      apply mag_le_bpow beta h_hx_ne
      rw [← h_hx_F2R]; exact h_hx_abs_lt_bpow_m
    linarith

/-- **The keystone `Veltkamp_aux` at FLX** (Pff's `Veltkamp_aux`,
line 14114, no underflow): for `x > 0` in `F(FLX, prec)`,
`2 ≤ s ≤ prec − 2`, the head `hx = round(round(x − round(x·C)) + round(x·C))`
satisfies both the error bound `|x − hx| ≤ β^(s + cexp x)/2` **and** the
format constraint `hx ∈ F(prec − s)`. This is the bundled form matching
the Coq/Pff theorem statement. -/
theorem Veltkamp_aux_FLX_complete (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    |x - Veltkamp_hx_FLX beta prec choice s x|
        ≤ bpow beta (s + cexp beta (FLX_exp prec) x) / 2 ∧
      generic_format beta (FLX_exp (prec - s))
        (Veltkamp_hx_FLX beta prec choice s x) :=
  ⟨Veltkamp_aux_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi,
   Veltkamp_hx_format_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi⟩

/-! ### Veltkamp tail

The complementary half of the split: the "tail" `tx = round(x − hx)` is
actually exact (no rounding error) and lives in `F(FLX, s)`. Combined,
`x = hx + tx` is a representation of `x` as the sum of a `prec − s`-digit
"head" and an `s`-digit "tail" — the goal of Veltkamp splitting. -/

/-- **Veltkamp tail at FLX**: `x = hx + tx` exactly, with `tx ∈ F(s)`.

The proof: express both `x` and `hx` as integer multiples of `β^cx`
(`x = M_x · β^cx` canonically; `hx = (Mq + Mp) · β^(s+cx) = ((Mq+Mp)·β^s) · β^cx`
via the format-side decomposition). Then `x − hx = M_tx · β^cx` with
`M_tx = M_x − (Mq+Mp)·β^s`. From `|x − hx| ≤ β^(s+cx)/2` we get
`|M_tx| ≤ β^s/2 < β^s`, hence `x − hx ∈ F(FLX, s)`. Since `s < prec`,
this also gives `x − hx ∈ F(FLX, prec)`, so the final rounding step is
identity: `tx = round_{prec}(x − hx) = x − hx`. -/
theorem Veltkamp_tail_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    x = Veltkamp_hx_FLX beta prec choice s x
        + Veltkamp_tx_FLX beta prec choice s x ∧
      generic_format beta (FLX_exp s)
        (Veltkamp_tx_FLX beta prec choice s x) := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = m - prec := rfl
  set p := Veltkamp_p_FLX beta prec choice s x with hp_def
  set q := Veltkamp_q_FLX beta prec choice s x with hq_def
  set hx := Veltkamp_hx_FLX beta prec choice s x with hhx_def
  set tx := Veltkamp_tx_FLX beta prec choice s x with htx_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : 0 < (beta.val : ℝ) := by linarith
  have hs_nn : 0 ≤ s := by linarith
  have h_bpow_cx_pos : 0 < bpow beta cx := bpow_gt_0 _ _
  have h_bpow_scx_pos : 0 < bpow beta (s + cx) := bpow_gt_0 _ _
  -- M_x: integer mantissa of x at cx.
  set M_x : ℤ := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hM_x_def
  have h_x_F2R : x = (M_x : ℝ) * bpow beta cx := Fx
  -- hx = (Mq + Mp) · β^(s + cx), via the format-side helpers.
  obtain ⟨Mp, hMp_eq⟩ :=
    Veltkamp_p_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  obtain ⟨Mq, hMq_eq⟩ :=
    Veltkamp_q_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_hxExact : hx = q + p :=
    hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  -- hx = ((Mq + Mp) · β^s) · β^cx.
  set M_hx_at_cx : ℤ := (Mq + Mp) * (beta.val : ℤ) ^ s.toNat with hM_hx_def
  have h_pow_s_real : (((beta.val : ℤ) ^ s.toNat : ℤ) : ℝ) = bpow beta s :=
    IZR_Zpower beta hs_nn
  have h_pow_s_pushed : ((beta.val : ℝ)) ^ s.toNat = bpow beta s := by
    have := h_pow_s_real; push_cast at this; exact this
  have h_hx_at_cx : hx = (M_hx_at_cx : ℝ) * bpow beta cx := by
    rw [hcx_def, h_hxExact, hq_def, hp_def, hMq_eq, hMp_eq, hM_hx_def]
    have h_split : bpow beta (s + cexp beta (FLX_exp prec) x)
                 = bpow beta s * bpow beta (cexp beta (FLX_exp prec) x) := by
      rw [← bpow_plus]
    rw [h_split]
    push_cast
    rw [h_pow_s_pushed]
    ring
  -- x - hx = (M_x - M_hx_at_cx) · β^cx.
  set M_tx : ℤ := M_x - M_hx_at_cx with hM_tx_def
  have h_diff_form : x - hx = (M_tx : ℝ) * bpow beta cx := by
    rw [h_x_F2R, h_hx_at_cx, hM_tx_def]
    push_cast; ring
  -- |M_tx| · β^cx = |x - hx| ≤ β^(s+cx)/2.
  have h_err : |x - hx| ≤ bpow beta (s + cx) / 2 :=
    Veltkamp_aux_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  -- |M_tx| < β^s.
  have h_M_tx_abs_lt : ((|M_tx| : ℤ) : ℝ) < bpow beta s := by
    have h_lhs : ((|M_tx| : ℤ) : ℝ) * bpow beta cx = |x - hx| := by
      rw [h_diff_form, abs_mul, abs_of_pos h_bpow_cx_pos]
      push_cast; rfl
    have h_pow_split : bpow beta (s + cx) = bpow beta s * bpow beta cx := by
      rw [← bpow_plus]
    have h_step : ((|M_tx| : ℤ) : ℝ) * bpow beta cx ≤ bpow beta s * bpow beta cx / 2 := by
      rw [h_lhs]
      rw [h_pow_split] at h_err
      exact h_err
    -- Divide both sides by β^cx > 0.
    have h_M_le_half : ((|M_tx| : ℤ) : ℝ) ≤ bpow beta s / 2 := by
      nlinarith [h_step, h_bpow_cx_pos]
    have h_bps_pos : 0 < bpow beta s := bpow_gt_0 _ _
    linarith
  -- Cast to integer bound.
  have h_M_tx_int_abs_lt : |M_tx| < (beta.val : ℤ) ^ s.toNat := by
    have h_real : ((|M_tx| : ℤ) : ℝ) < (((beta.val : ℤ) ^ s.toNat : ℤ) : ℝ) := by
      rw [h_pow_s_real]; exact h_M_tx_abs_lt
    exact_mod_cast h_real
  -- x - hx ∈ F(FLX, s).
  have h_xmhx_format_s : generic_format beta (FLX_exp s) (x - hx) := by
    rw [h_diff_form]
    show generic_format beta (FLX_exp s) (F2R (beta := beta) ⟨M_tx, cx⟩)
    apply generic_format_F2R beta (FLX_exp s) M_tx cx
    intro h_ne
    show FLX_exp s (mag beta (F2R (beta := beta) ⟨M_tx, cx⟩)) ≤ cx
    unfold FLX_exp
    -- mag(F2R) ≤ s + cx (from |F2R| < β^(s+cx)).
    have h_F2R_eq : F2R (beta := beta) ⟨M_tx, cx⟩ = x - hx := h_diff_form.symm
    have h_F2R_ne : F2R (beta := beta) ⟨M_tx, cx⟩ ≠ 0 := by
      rw [h_F2R_eq]
      intro h; rw [h_diff_form] at h
      have : (M_tx : ℝ) = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact h
        · linarith [h_bpow_cx_pos]
      have : M_tx = 0 := by exact_mod_cast this
      apply h_ne; exact this
    have h_abs_lt : |F2R (beta := beta) ⟨M_tx, cx⟩| < bpow beta (s + cx) := by
      rw [h_F2R_eq]
      have h_bpow_scx_pos' : 0 < bpow beta (s + cx) := h_bpow_scx_pos
      linarith
    have h_mag_le : mag beta (F2R (beta := beta) ⟨M_tx, cx⟩) ≤ s + cx :=
      mag_le_bpow beta h_F2R_ne h_abs_lt
    linarith
  -- x - hx ∈ F(FLX, prec) (since F(s) ⊂ F(prec) for s ≤ prec).
  have h_xmhx_format_prec : generic_format beta (FLX_exp prec) (x - hx) := by
    rw [h_diff_form]
    apply generic_format_F2R beta (FLX_exp prec) M_tx cx
    intro h_ne
    show FLX_exp prec (mag beta (F2R (beta := beta) ⟨M_tx, cx⟩)) ≤ cx
    unfold FLX_exp
    have h_F2R_eq : F2R (beta := beta) ⟨M_tx, cx⟩ = x - hx := h_diff_form.symm
    have h_F2R_ne : F2R (beta := beta) ⟨M_tx, cx⟩ ≠ 0 := by
      rw [h_F2R_eq]
      intro h; rw [h_diff_form] at h
      have : (M_tx : ℝ) = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact h
        · linarith [h_bpow_cx_pos]
      have : M_tx = 0 := by exact_mod_cast this
      apply h_ne; exact this
    have h_abs_lt : |F2R (beta := beta) ⟨M_tx, cx⟩| < bpow beta (s + cx) := by
      rw [h_F2R_eq]; linarith
    have h_mag_le : mag beta (F2R (beta := beta) ⟨M_tx, cx⟩) ≤ s + cx :=
      mag_le_bpow beta h_F2R_ne h_abs_lt
    linarith
  -- tx = x - hx.
  have h_tx_eq : tx = x - hx := by
    show round beta (FLX_exp prec) (Znearest choice) (x - hx) = x - hx
    exact round_generic beta (FLX_exp prec) (Znearest choice) h_xmhx_format_prec
  refine ⟨?_, ?_⟩
  · -- x = hx + tx
    rw [h_tx_eq]; ring
  · -- tx ∈ F(FLX, s)
    rw [h_tx_eq]; exact h_xmhx_format_s

/-! ### Veltkamp existence (∃ choice'): `hx = round_{prec−s, choice'} x`

The structural meaning of `hx ∈ F(prec−s)` and `|x − hx| ≤ ulp/2`: there
exists a tie-breaking function `choice'` for which the round-to-nearest
of `x` at the coarser precision `prec−s` produces exactly `hx`.

The witness is constructed by inspecting whether `hx` sits below or
above the integer-mantissa floor of `x` at the coarser precision:

  choice' k := (round_DN_{prec−s}(x) < hx)

For non-tie x: the round result is determined by x's position relative
to the midpoint, and matches hx (since hx is the unique F(prec−s) value
within ulp/2 of x). For midpoint x: choice' picks DN if hx = DN
(below) or UP if hx = UP (above), reproducing hx exactly. -/

/-- **Integer-mantissa core of Veltkamp**: `hx = M_h · β^(s+cx)` where
`M_h` is the integer mantissa, and `M_h` lies within 1/2 of `M_x · β^(-s)`
(the scaled mantissa of `x` at precision `prec−s`). This is the
"closeness" condition that drives the existence of `choice'`. -/
private theorem Veltkamp_M_h_close_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    ∃ M_x M_h : ℤ,
      x = (M_x : ℝ) * bpow beta (cexp beta (FLX_exp prec) x) ∧
      Veltkamp_hx_FLX beta prec choice s x
        = (M_h : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) ∧
      |(M_x : ℝ) - (M_h : ℝ) * bpow beta s| ≤ bpow beta s / 2 := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hs_nn : 0 ≤ s := by linarith
  have h_bpow_cx_pos : 0 < bpow beta cx := bpow_gt_0 _ _
  have h_bpow_scx_pos : 0 < bpow beta (s + cx) := bpow_gt_0 _ _
  -- Witnesses: M_x (canonical) and Mq + Mp (from format-side).
  obtain ⟨Mp, hMp_eq⟩ :=
    Veltkamp_p_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  obtain ⟨Mq, hMq_eq⟩ :=
    Veltkamp_q_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  refine ⟨Ztrunc (scaled_mantissa beta (FLX_exp prec) x), Mq + Mp, Fx, ?_, ?_⟩
  · -- hx = (Mq + Mp) · β^(s+cx).
    rw [hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi, hMq_eq, hMp_eq]
    push_cast; ring
  · -- |M_x - (Mq+Mp) · β^s| ≤ β^s/2.
    set hx_val := Veltkamp_hx_FLX beta prec choice s x with hx_val_def
    have h_err : |x - hx_val| ≤ bpow beta (s + cx) / 2 :=
      Veltkamp_aux_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
    set M_x : ℤ := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hM_x_def
    have h_x_F2R : x = (M_x : ℝ) * bpow beta cx := Fx
    have h_hx_form : hx_val = ((Mq + Mp : ℝ)) * bpow beta (s + cx) := by
      rw [hx_val_def, hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi, hMq_eq, hMp_eq]
      ring
    have h_diff_eq : x - hx_val
                   = ((M_x : ℝ) - (Mq + Mp : ℝ) * bpow beta s) * bpow beta cx := by
      rw [h_x_F2R, h_hx_form]
      have h_split : bpow beta (s + cx) = bpow beta s * bpow beta cx := by
        rw [← bpow_plus]
      rw [h_split]; ring
    rw [h_diff_eq, abs_mul, abs_of_pos h_bpow_cx_pos] at h_err
    have h_split : bpow beta (s + cx) / 2 = (bpow beta s / 2) * bpow beta cx := by
      rw [show bpow beta (s + cx) = bpow beta s * bpow beta cx from by rw [← bpow_plus]]
      ring
    rw [h_split] at h_err
    push_cast
    nlinarith [h_err, h_bpow_cx_pos]

/-- **Veltkamp existence (FLX)**: for `x > 0` in F(FLX, prec), `2 ≤ s ≤ prec − 2`,
there exists a tie-breaking function `choice'` such that
`round_{prec−s, Znearest choice'} x = Veltkamp_hx_FLX beta prec choice s x`.

This is Pff's `Veltkamp` theorem (Pff2Flocq.v:381–419): the result that `hx`
is reachable by a single round-to-nearest at the coarser precision `prec − s`.

Construction: `choice' k := decide (round_{prec−s, Zfloor} x < hx)`.
The half-ulp bound on `|x − hx|` plus `hx ∈ F(prec−s)` forces `M_h ∈ {q, q+1}`
where `q = ⌊M_x · β^(−s)⌋`. For non-tie x, Znearest picks the unique closest
regardless of choice; at tie, `choice'` flips correctly via `q < M_h`. -/
theorem Veltkamp_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    ∃ choice' : ℤ → Bool,
      round beta (FLX_exp (prec - s)) (Znearest choice') x
        = Veltkamp_hx_FLX beta prec choice s x := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set cx_s := s + cx with hcx_s_def
  set hx_val := Veltkamp_hx_FLX beta prec choice s x with hx_val_def
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos : (0 : ℝ) < (beta.val : ℝ) := by linarith
  have hp_minus_s_pos : 0 < prec - s := by linarith
  have hcx_eq : cx = m - prec := rfl
  have h_bpow_cx_pos : (0 : ℝ) < bpow beta cx := bpow_gt_0 _ _
  have h_bpow_s_pos : (0 : ℝ) < bpow beta s := bpow_gt_0 _ _
  have h_bpow_cxs_pos : (0 : ℝ) < bpow beta cx_s := bpow_gt_0 _ _
  have h_bpow_neg_s_pos : (0 : ℝ) < bpow beta (-s) := bpow_gt_0 _ _
  have h_bpow_s_inv : bpow beta s * bpow beta (-s) = 1 := by
    rw [← bpow_plus, show s + -s = 0 from by ring, bpow_zero]
  -- Extract M_x, M_h from M_h_close.
  obtain ⟨M_x, M_h, h_x_F2R, h_hx_eq, h_close⟩ :=
    Veltkamp_M_h_close_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  -- cexp at the coarser precision: m - (prec - s) = s + cx.
  have hcexp_s : cexp beta (FLX_exp (prec - s)) x = cx_s := by
    show FLX_exp (prec - s) (mag beta x) = s + cx
    rw [hcx_eq]; unfold FLX_exp; ring
  -- Scaled mantissa at the coarser precision is `M_x · β^(-s)`.
  set sm : ℝ := (M_x : ℝ) * bpow beta (-s) with hsm_def
  have h_sm_eq : scaled_mantissa beta (FLX_exp (prec - s)) x = sm := by
    show x * bpow beta (-cexp beta (FLX_exp (prec - s)) x) = sm
    rw [hcexp_s, h_x_F2R, mul_assoc, ← bpow_plus]
    have h_arg : cexp beta (FLX_exp prec) x + -cx_s = -s := by rw [hcx_s_def]; ring
    rw [h_arg]
  -- DN := round_{prec-s, Zfloor} x = ⌊sm⌋ · β^cx_s.
  set q : ℤ := ⌊sm⌋ with hq_def
  set DN : ℝ := round beta (FLX_exp (prec - s)) (fun y : ℝ => ⌊y⌋) x with hDN_def
  have h_DN_eq : DN = (q : ℝ) * bpow beta cx_s := by
    show F2R (beta := beta) ⟨⌊scaled_mantissa beta (FLX_exp (prec - s)) x⌋,
                             cexp beta (FLX_exp (prec - s)) x⟩
        = (q : ℝ) * bpow beta cx_s
    rw [h_sm_eq, hcexp_s]; rfl
  -- The witness.
  refine ⟨fun _ => decide (DN < hx_val), ?_⟩
  set choice' : ℤ → Bool := fun _ => decide (DN < hx_val) with hchoice'_def
  -- Unfold the LHS round.
  show F2R (beta := beta) ⟨Znearest choice' (scaled_mantissa beta (FLX_exp (prec - s)) x),
                           cexp beta (FLX_exp (prec - s)) x⟩ = hx_val
  rw [h_sm_eq, hcexp_s]
  show ((Znearest choice' sm : ℤ) : ℝ) * bpow beta cx_s
       = Veltkamp_hx_FLX beta prec choice s x
  rw [h_hx_eq]
  show ((Znearest choice' sm : ℤ) : ℝ) * bpow beta cx_s = (M_h : ℝ) * bpow beta cx_s
  -- Reduce to integer equality.
  suffices h_target : Znearest choice' sm = M_h by rw [h_target]
  -- Translate h_close to `|sm − M_h| ≤ 1/2`.
  have h_close_norm : |sm - (M_h : ℝ)| ≤ 1/2 := by
    have h_eq : sm - (M_h : ℝ)
              = ((M_x : ℝ) - (M_h : ℝ) * bpow beta s) * bpow beta (-s) := by
      rw [hsm_def]
      have h_dist : ((M_x : ℝ) - (M_h : ℝ) * bpow beta s) * bpow beta (-s)
                  = (M_x : ℝ) * bpow beta (-s)
                      - (M_h : ℝ) * (bpow beta s * bpow beta (-s)) := by ring
      rw [h_dist, h_bpow_s_inv, mul_one]
    rw [h_eq, abs_mul, abs_of_pos h_bpow_neg_s_pos]
    have h_bound : (bpow beta s / 2) * bpow beta (-s) = 1/2 := by
      field_simp; rw [h_bpow_s_inv]
    have h_mul_le : |(M_x : ℝ) - (M_h : ℝ) * bpow beta s| * bpow beta (-s)
                  ≤ (bpow beta s / 2) * bpow beta (-s) :=
      mul_le_mul_of_nonneg_right h_close (le_of_lt h_bpow_neg_s_pos)
    linarith
  -- Case-split: strict bound or exact tie.
  rcases lt_or_eq_of_le h_close_norm with h_strict | h_eq_abs
  · -- Strict |sm − M_h| < 1/2: any choice works (Znearest_imp).
    exact Znearest_imp choice' h_strict
  · -- Tie: |sm − M_h| = 1/2. Two subcases.
    have h_pair : sm - (M_h : ℝ) = 1/2 ∨ sm - (M_h : ℝ) = -1/2 := by
      have h := (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp h_eq_abs
      rcases h with h | h
      · left; exact h
      · right; linarith
    rcases h_pair with h_above | h_below
    · -- sm = M_h + 1/2: q = M_h, ⌈sm⌉ = M_h + 1.
      have h_floor : (⌊sm⌋ : ℤ) = M_h := by
        apply Int.floor_eq_iff.mpr
        refine ⟨by linarith, by push_cast; linarith⟩
      have h_ceil : (⌈sm⌉ : ℤ) = M_h + 1 := by
        apply Int.ceil_eq_iff.mpr
        refine ⟨by push_cast; linarith, by push_cast; linarith⟩
      -- DN = q · β^cx_s = M_h · β^cx_s = hx_val. So choice' M_h = false.
      have hqM : (q : ℝ) = (M_h : ℝ) := by
        rw [hq_def]; exact_mod_cast h_floor
      have h_DN_eq_hx : DN = hx_val := by
        rw [h_DN_eq]
        show (q : ℝ) * bpow beta cx_s = Veltkamp_hx_FLX beta prec choice s x
        rw [h_hx_eq, hqM]
      have h_choice'_eq : choice' M_h = false := by
        show decide (DN < hx_val) = false
        apply decide_eq_false
        rw [h_DN_eq_hx]; exact lt_irrefl _
      -- Unfold Znearest at the tie.
      unfold Znearest
      simp only [h_floor, h_ceil]
      have h_frac : sm - (M_h : ℝ) = 1/2 := h_above
      rw [h_frac]
      simp only [lt_self_iff_false, ↓reduceIte, h_choice'_eq, Bool.false_eq_true]
    · -- sm = M_h − 1/2: q = M_h − 1, ⌈sm⌉ = M_h.
      have h_floor : (⌊sm⌋ : ℤ) = M_h - 1 := by
        apply Int.floor_eq_iff.mpr
        refine ⟨by push_cast; linarith, by push_cast; linarith⟩
      have h_ceil : (⌈sm⌉ : ℤ) = M_h := by
        apply Int.ceil_eq_iff.mpr
        refine ⟨by linarith, by push_cast; linarith⟩
      -- DN = q · β^cx_s = (M_h−1) · β^cx_s < M_h · β^cx_s = hx_val. So choice' (M_h−1) = true.
      have hqM : (q : ℝ) = ((M_h - 1 : ℤ) : ℝ) := by
        rw [hq_def]; exact_mod_cast h_floor
      have h_DN_lt_hx : DN < hx_val := by
        rw [h_DN_eq]
        show (q : ℝ) * bpow beta cx_s < Veltkamp_hx_FLX beta prec choice s x
        rw [h_hx_eq, hqM]
        show ((M_h - 1 : ℤ) : ℝ) * bpow beta (s + cx) < (M_h : ℝ) * bpow beta (s + cx)
        have h_int_lt : ((M_h - 1 : ℤ) : ℝ) < (M_h : ℝ) := by push_cast; linarith
        exact (mul_lt_mul_iff_of_pos_right (bpow_gt_0 _ _)).mpr h_int_lt
      have h_choice'_eq : choice' (M_h - 1) = true := by
        show decide (DN < hx_val) = true
        exact decide_eq_true h_DN_lt_hx
      -- Unfold Znearest at the tie.
      unfold Znearest
      simp only [h_floor, h_ceil]
      have h_frac : sm - ((M_h - 1 : ℤ) : ℝ) = 1/2 := by push_cast; linarith
      rw [h_frac]
      simp only [lt_self_iff_false, ↓reduceIte, h_choice'_eq]

/-! ### Veltkamp_Even at FLX (odd-radix case)

For odd radix `β`, `β^s` is an odd integer and `β^s/2` is non-integer; the
half-ulp bound `|M_x − M_h · β^s| ≤ β^s/2` on integers forces the strict
inequality `< β^s/2`. Hence at the coarser precision `prec − s`, the
scaled mantissa `sm = M_x · β^(−s)` is *never* at a midpoint, so any
`Znearest choice'` (including `ZnearestE`) yields `M_h`. The algorithm's
output `hx` therefore matches `round_NE_{prec−s} x` regardless of the
internal tie-breaker. -/

/-- For odd radix, the algorithm's coarse-precision target is reachable
by *any* `Znearest choice'` at precision `prec − s` — including
round-to-nearest-even. This is the easy half of `Veltkamp_Even`: when
`β` is odd, ties cannot occur at the coarser precision. -/
theorem Veltkamp_Even_FLX_odd_radix (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (h_odd_beta : Odd beta.val)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    ∀ choice' : ℤ → Bool,
      round beta (FLX_exp (prec - s)) (Znearest choice') x
        = Veltkamp_hx_FLX beta prec choice s x := by
  intro choice'
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set cx_s := s + cx with hcx_s_def
  set hx_val := Veltkamp_hx_FLX beta prec choice s x with hx_val_def
  have hs_nn : 0 ≤ s := by linarith
  have h_bpow_s_pos : (0 : ℝ) < bpow beta s := bpow_gt_0 _ _
  have h_bpow_neg_s_pos : (0 : ℝ) < bpow beta (-s) := bpow_gt_0 _ _
  have h_bpow_s_inv : bpow beta s * bpow beta (-s) = 1 := by
    rw [← bpow_plus, show s + -s = 0 from by ring, bpow_zero]
  -- Extract M_x, M_h from the half-ulp core.
  obtain ⟨M_x, M_h, h_x_F2R, h_hx_eq, h_close⟩ :=
    Veltkamp_M_h_close_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  -- β^s as an odd integer.
  set βs : ℤ := beta.val ^ s.toNat with hβs_def
  have h_βs_real : (βs : ℝ) = bpow beta s := by
    show ((beta.val ^ s.toNat : ℤ) : ℝ) = bpow beta s
    exact IZR_Zpower beta hs_nn
  have h_βs_odd : Odd βs := h_odd_beta.pow
  -- cexp at coarser precision and scaled mantissa.
  have hcexp_s : cexp beta (FLX_exp (prec - s)) x = cx_s := by
    show FLX_exp (prec - s) (mag beta x) = s + cx
    have hcx_eq : cx = mag beta x - prec := rfl
    rw [hcx_eq]; unfold FLX_exp; ring
  set sm : ℝ := (M_x : ℝ) * bpow beta (-s) with hsm_def
  have h_sm_eq : scaled_mantissa beta (FLX_exp (prec - s)) x = sm := by
    show x * bpow beta (-cexp beta (FLX_exp (prec - s)) x) = sm
    rw [hcexp_s, h_x_F2R, mul_assoc, ← bpow_plus]
    have h_arg : cexp beta (FLX_exp prec) x + -cx_s = -s := by rw [hcx_s_def]; ring
    rw [h_arg]
  -- Strict closeness: |sm − M_h| < 1/2.
  have h_close_strict : |sm - (M_h : ℝ)| < 1/2 := by
    -- Step 1: convert h_close to an integer inequality.
    have h_diff_int : (M_x : ℝ) - (M_h : ℝ) * bpow beta s
                    = ((M_x - M_h * βs : ℤ) : ℝ) := by
      push_cast; rw [h_βs_real]
    rw [h_diff_int, ← h_βs_real] at h_close
    -- h_close : |((M_x − M_h * βs : ℤ) : ℝ)| ≤ (βs : ℝ) / 2
    -- Step 2: turn into 2 * |M_x − M_h * βs| ≤ βs (integer).
    have h_abs_real : |((M_x - M_h * βs : ℤ) : ℝ)| = ((|M_x - M_h * βs| : ℤ) : ℝ) := by
      push_cast; rfl
    rw [h_abs_real] at h_close
    have h_2D_le : 2 * |M_x - M_h * βs| ≤ βs := by
      have h_step : 2 * ((|M_x - M_h * βs| : ℤ) : ℝ) ≤ ((βs : ℤ) : ℝ) := by linarith
      have h_cast : ((2 * |M_x - M_h * βs| : ℤ) : ℝ) ≤ ((βs : ℤ) : ℝ) := by
        rw [show ((2 * |M_x - M_h * βs| : ℤ) : ℝ)
              = 2 * ((|M_x - M_h * βs| : ℤ) : ℝ) by push_cast; ring]
        exact h_step
      exact_mod_cast h_cast
    -- Step 3: parity forces strict.
    have h_D_nn : 0 ≤ |M_x - M_h * βs| := abs_nonneg _
    have h_2D_lt : 2 * |M_x - M_h * βs| < βs := by
      obtain ⟨k, hk⟩ := h_βs_odd
      -- βs = 2k + 1; 2D ≤ 2k + 1 with 2D even ⟹ 2D ≤ 2k < 2k+1.
      have hD : 2 * |M_x - M_h * βs| ≤ 2 * k + 1 := hk ▸ h_2D_le
      have : 2 * |M_x - M_h * βs| ≤ 2 * k := by omega
      omega
    -- Step 4: lift back to reals: |sm − M_h| < 1/2.
    rw [hsm_def]
    have h_sub : (M_x : ℝ) * bpow beta (-s) - (M_h : ℝ)
               = ((M_x : ℝ) - (M_h : ℝ) * bpow beta s) * bpow beta (-s) := by
      have h_dist : ((M_x : ℝ) - (M_h : ℝ) * bpow beta s) * bpow beta (-s)
                  = (M_x : ℝ) * bpow beta (-s)
                      - (M_h : ℝ) * (bpow beta s * bpow beta (-s)) := by ring
      rw [h_dist, h_bpow_s_inv, mul_one]
    rw [h_sub, h_diff_int, abs_mul, abs_of_pos h_bpow_neg_s_pos, h_abs_real]
    -- Goal: ((|M_x − M_h * βs| : ℤ) : ℝ) * bpow beta (-s) < 1/2.
    have h_lt_real : ((|M_x - M_h * βs| : ℤ) : ℝ) * bpow beta (-s)
                   < ((βs : ℤ) : ℝ) * bpow beta (-s) / 2 := by
      have h_step : 2 * ((|M_x - M_h * βs| : ℤ) : ℝ) < ((βs : ℤ) : ℝ) := by
        exact_mod_cast h_2D_lt
      have h_mul : 2 * ((|M_x - M_h * βs| : ℤ) : ℝ) * bpow beta (-s)
                 < ((βs : ℤ) : ℝ) * bpow beta (-s) :=
        (mul_lt_mul_iff_of_pos_right h_bpow_neg_s_pos).mpr h_step
      linarith
    have h_rhs : ((βs : ℤ) : ℝ) * bpow beta (-s) = 1 := by
      rw [show ((βs : ℤ) : ℝ) = bpow beta s from h_βs_real]
      exact h_bpow_s_inv
    rw [h_rhs] at h_lt_real
    linarith
  -- Apply Znearest_imp.
  have h_target : Znearest choice' sm = M_h :=
    Znearest_imp choice' h_close_strict
  -- Combine into the round formula.
  show F2R (beta := beta)
        ⟨Znearest choice' (scaled_mantissa beta (FLX_exp (prec - s)) x),
         cexp beta (FLX_exp (prec - s)) x⟩
       = hx_val
  rw [h_sm_eq, hcexp_s, h_target]
  show ((M_h : ℤ) : ℝ) * bpow beta cx_s = Veltkamp_hx_FLX beta prec choice s x
  rw [h_hx_eq]

/-- **Veltkamp_Even at FLX (odd-radix specialization)**: when `β` is odd,
the algorithm with *any* internal tie-breaker `choice` produces an `hx`
that equals `round_NE_{prec − s} x`. This is the easy half of
`Veltkamp_Even`. -/
theorem Veltkamp_Even_FLX_odd (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (h_odd_beta : Odd beta.val)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    round_NE beta (FLX_exp (prec - s)) x
      = Veltkamp_hx_FLX beta prec choice s x := by
  unfold round_NE ZnearestE
  exact Veltkamp_Even_FLX_odd_radix beta prec hp choice h_odd_beta
    Fx hx_pos hs_lo hs_hi _

/-! ### Veltkamp's `hx` is a closest representable at coarser precision

Foundation for `Veltkamp_Even` at any radix: by `Veltkamp_FLX` existence
plus `round_N_pt`, the algorithm's `hx` is a `Rnd_N_pt` at the coarser
precision `prec − s`. The remaining gap to `Rnd_NE_pt` is the parity of
the canonical mantissa of `hx` at ties — vacuous for odd radix, and a
substantial algorithmic argument for even radix (Pff `VeltkampEven1`). -/

/-- **Veltkamp's output is at a `Rnd_N_pt` of the coarser precision.**
This combines `Veltkamp_FLX` existence with `round_N_pt`: since some
`Znearest` rounding at precision `prec − s` produces exactly `hx`, the
value `hx` is a closest representable at that precision. -/
theorem Veltkamp_hx_Rnd_N_pt_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    Rnd_N_pt (generic_format beta (FLX_exp (prec - s))) x
             (Veltkamp_hx_FLX beta prec choice s x) := by
  have hp_minus_s_pos : 0 < prec - s := by linarith
  obtain ⟨choice', h_eq⟩ :=
    Veltkamp_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_pt := round_N_pt beta (FLX_exp (prec - s))
    (FLX_exp_valid (prec - s) hp_minus_s_pos) choice' x
  rw [← h_eq]; exact h_pt

/-! ### Bridge from `Rnd_NE_pt` to the `round_NE = hx` equality

Given that `hx` satisfies `Rnd_NE_pt` at the coarser precision, the
`round_NE = hx` equality (Pff's `Veltkamp_Even`) follows by uniqueness
of `Rnd_NE_pt`: both `round_NE_{prec−s} x` and `hx` are `Rnd_NE_pt` of
`x`, and `Rnd_NE_pt` is unique (`NE_unique_prop_holds`). -/

/-- **Conditional `Veltkamp_Even` at FLX**: given the `Rnd_NE_pt`
property for `hx`, the algorithm's output equals `round_NE` at the
coarser precision. Uniqueness of `Rnd_NE_pt` does the work; this
theorem is the bridge from "hx is the NE-rounded value" to "the round
formula evaluates to hx". -/
theorem Veltkamp_Even_FLX_of_Rnd_NE_pt (beta : radix) (prec : ℤ)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (hs_hi : s + 2 ≤ prec)
    (h_pt : Rnd_NE_pt beta (FLX_exp (prec - s)) x
              (Veltkamp_hx_FLX beta prec choice s x)) :
    round_NE beta (FLX_exp (prec - s)) x
      = Veltkamp_hx_FLX beta prec choice s x := by
  have hp_minus_s_pos : 0 < prec - s := by linarith
  have h_prec_minus_s_gt_1 : 1 < prec - s := by linarith
  haveI : Exists_NE beta (FLX_exp (prec - s)) :=
    exists_NE_FLX beta (prec - s) hp_minus_s_pos (Or.inr h_prec_minus_s_gt_1)
  have h_valid := FLX_exp_valid (prec - s) hp_minus_s_pos
  -- `round_NE x` is at `Rnd_NE_pt`.
  have h_round_pt : Rnd_NE_pt beta (FLX_exp (prec - s)) x
                      (round beta (FLX_exp (prec - s)) ZnearestE x) :=
    round_NE_pt beta (FLX_exp (prec - s)) h_valid x
  -- Uniqueness of `Rnd_NE_pt`.
  have h_unique := NE_unique_prop_holds beta (FLX_exp (prec - s)) h_valid
  show round_NE beta (FLX_exp (prec - s)) x
      = Veltkamp_hx_FLX beta prec choice s x
  unfold round_NE
  exact Rnd_NG_pt_unique _ _ h_unique h_round_pt h_pt

/-- **Veltkamp's `hx` is at `Rnd_NE_pt`, odd-radix case.** Discharges
the parity/uniqueness disjunction in `Rnd_NG_pt` via the no-tie property
established by `Veltkamp_Even_FLX_odd_radix`: any `Znearest` choice at
the coarser precision produces `hx`, so `hx` is the unique closest. -/
theorem Veltkamp_hx_Rnd_NE_pt_FLX_odd (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (h_odd_beta : Odd beta.val)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    Rnd_NE_pt beta (FLX_exp (prec - s)) x
              (Veltkamp_hx_FLX beta prec choice s x) := by
  have hp_minus_s_pos : 0 < prec - s := by linarith
  have h_prec_minus_s_gt_1 : 1 < prec - s := by linarith
  haveI : Exists_NE beta (FLX_exp (prec - s)) :=
    exists_NE_FLX beta (prec - s) hp_minus_s_pos (Or.inr h_prec_minus_s_gt_1)
  -- From `Veltkamp_Even_FLX_odd`: round_NE x = hx.
  have h_eq := Veltkamp_Even_FLX_odd beta prec hp choice h_odd_beta
    Fx hx_pos hs_lo hs_hi
  -- round_NE x is at Rnd_NE_pt.
  have h_pt := round_NE_pt beta (FLX_exp (prec - s))
    (FLX_exp_valid (prec - s) hp_minus_s_pos) x
  -- Transport.
  rw [round_NE] at h_eq
  rw [← h_eq]; exact h_pt

/-- **Veltkamp_Even at FLX (general form, conditional)**: the algorithm's
`hx` equals `round_NE_{prec−s} x` provided we know `hx` satisfies
`Rnd_NE_pt`. This collapses to a single hypothesis call: either supply
an odd-radix proof (Or.inl) or the parity-at-tie proof (Or.inr).
For odd radix it's discharged automatically. -/
theorem Veltkamp_Even_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_dispatch : Odd beta.val ∨
                  Rnd_NE_pt beta (FLX_exp (prec - s)) x
                            (Veltkamp_hx_FLX beta prec choice s x)) :
    round_NE beta (FLX_exp (prec - s)) x
      = Veltkamp_hx_FLX beta prec choice s x := by
  rcases h_dispatch with h_odd | h_pt
  · exact Veltkamp_Even_FLX_odd beta prec hp choice h_odd Fx hx_pos hs_lo hs_hi
  · exact Veltkamp_Even_FLX_of_Rnd_NE_pt beta prec choice hs_hi h_pt

/-! ### Veltkamp_Even at FLX (even-radix case) — path-2 dichotomy reduction

For even radix β, the parity-at-tie argument for `Veltkamp_Even` reduces to a
single hard subcase via the format-side dichotomy on `M_total = Mp + Mq`,
where `hx = M_total · β^(s+cx)`:

- **Boundary** (`|M_total| = β^(prec−s)`): `hx = ±β^m`. The canonical mantissa
  at coarser precision `prec − s` is `±β^(prec−s−1)`, which is divisible by β
  (since `prec − s − 1 ≥ 1`), hence even for even β.

- **Low-mag interior** (`|M_total| < β^(prec−s−1)`): `mag(hx) < m`. The canonical
  exponent is strictly less than `s+cx`, so the canonical mantissa is
  `M_total · β^d` for some `d ≥ 1`, hence divisible by β, hence even.

- **Hard interior** (`β^(prec−s−1) ≤ |M_total| < β^(prec−s)`): `mag(hx) = m`.
  The canonical mantissa is exactly `M_total`. Need `M_total` even — the
  remaining algorithmic content (Pff's `VeltkampEven1`, ~292 Coq lines of
  parity-tracking through the three NE-rounded steps).
-/

/-- **Path-2 helper: an even mantissa `g.Fnum` via a β-factor witness.**
If `f = N · β^e` with `β | N` and β is even, then `N` is even — and we can
package this into an `NE_prop` witness once we know the canonical exponent
matches `e`. This is the "easy" structural part of the dichotomy: any
representation of `hx` at a canonical exponent strictly below `s+cx` gives
us a multiple-of-β mantissa for free. -/
private theorem even_pow_of_pos (beta : radix) (h_even_beta : Even beta.val)
    {d : ℤ} (hd : 1 ≤ d) :
    Even ((beta.val : ℤ) ^ d.toNat) := by
  have hd_toNat_pos : 0 < d.toNat := by omega
  rw [show d.toNat = (d.toNat - 1) + 1 from by omega, pow_succ]
  exact Even.mul_left h_even_beta _

/-- **Path-2 dichotomy: `Veltkamp_Even` at FLX, even-radix case, NE_prop part.**
For even β, the parity-at-tie content reduces to a single hard subcase. Given
the parity hypothesis for the hard subcase (`β^(prec−s−1) ≤ |M| < β^(prec−s)`,
which corresponds to `mag(hx) = mag(x)`), `NE_prop` for `hx` holds. The other
two subcases (boundary `|M| = β^(prec−s)` → `hx = ±β^m`, low-mag
`|M| < β^(prec−s−1)` → `mag(hx) < mag(x)`) discharge automatically via the
divisibility-by-β structure of `hx`'s canonical mantissa. -/
theorem Veltkamp_hx_NE_prop_FLX_even_radix
    (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (h_even_beta : Even beta.val)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_parity_hard :
       ∀ M : ℤ,
         Veltkamp_hx_FLX beta prec choice s x
           = (M : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) →
         (beta.val : ℤ) ^ ((prec - s - 1).toNat) ≤ |M| →
         |M| < (beta.val : ℤ) ^ (prec - s).toNat →
         Even M) :
    NE_prop beta (FLX_exp (prec - s)) x
            (Veltkamp_hx_FLX beta prec choice s x) := by
  set m := mag beta x with hm_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set hx := Veltkamp_hx_FLX beta prec choice s x with hhx_def
  have hcx_eq : cx = m - prec := rfl
  have hβ_ge_2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have hβ_pos_int : (0 : ℤ) < beta.val := by have := beta.prop; linarith
  have h_bpow_scx_pos : (0 : ℝ) < bpow beta (s + cx) := bpow_gt_0 _ _
  have h_prec_s_nn : 0 ≤ prec - s := by linarith
  have h_prec_s_m1_nn : 0 ≤ prec - s - 1 := by linarith
  -- Extract M_total = Mq + Mp.
  obtain ⟨Mp, hp_eq⟩ :=
    Veltkamp_p_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  obtain ⟨Mq, hq_eq⟩ :=
    Veltkamp_q_at_scx_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_hxExact :
    hx = Veltkamp_q_FLX beta prec choice s x + Veltkamp_p_FLX beta prec choice s x :=
    hxExact_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  set M_total : ℤ := Mq + Mp with hM_def
  have h_hx_form : hx = ((M_total : ℤ) : ℝ) * bpow beta (s + cx) := by
    rw [h_hxExact, hq_eq, hp_eq, hM_def]; push_cast; ring
  -- hx > 0 (already known since |x - hx| < x).
  have h_err : |x - hx| ≤ bpow beta (s + cx) / 2 :=
    Veltkamp_aux_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  have h_x_ge : bpow beta (m - 1) ≤ x := by
    have := bpow_mag_le beta (ne_of_gt hx_pos); rwa [abs_of_pos hx_pos] at this
  have h_err_lt_x : |x - hx| < x := by
    have h_scx_le : bpow beta (s + cx) ≤ bpow beta (m - 2) := by
      apply bpow_le; rw [hcx_eq]; linarith
    have h_m2_lt : bpow beta (m - 2) / 2 < bpow beta (m - 1) := by
      have h_half_le : bpow beta (m - 2) / 2 ≤ bpow beta (m - 2) := by
        have := bpow_gt_0 beta (m - 2); linarith
      have h_strict : bpow beta (m - 2) < bpow beta (m - 1) := bpow_lt beta (by linarith)
      linarith
    linarith
  have h_hx_pos : 0 < hx := by
    rcases le_or_lt (x - hx) 0 with h | h
    · linarith [abs_of_nonpos h]
    · linarith [abs_of_pos h]
  have h_M_pos : 0 < M_total := by
    have h_M_real_pos : 0 < ((M_total : ℤ) : ℝ) := by
      have : 0 < ((M_total : ℤ) : ℝ) * bpow beta (s + cx) := by
        rw [← h_hx_form]; exact h_hx_pos
      exact (mul_pos_iff_of_pos_right h_bpow_scx_pos).mp this
    exact_mod_cast h_M_real_pos
  -- |M_total| ≤ β^(prec-s) from format-side (we reproduce the bound here).
  have h_bpow_m_eq : bpow beta m = bpow beta (prec - s) * bpow beta (s + cx) := by
    rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
  have h_x_lt_bpow : x < bpow beta m := by
    have := bpow_mag_gt beta x; rwa [abs_of_pos hx_pos] at this
  have h_hx_abs_lt : hx < bpow beta m + bpow beta (s + cx) / 2 := by
    have h_tri : |hx| ≤ |x| + |x - hx| := by
      calc |hx| = |-(x - hx) + x| := by ring_nf
        _ ≤ |-(x - hx)| + |x| := abs_add_le _ _
        _ = |x| + |x - hx| := by rw [abs_neg]; ring
    rw [abs_of_pos hx_pos, abs_of_pos h_hx_pos] at h_tri; linarith
  have h_pow_real_pushed :
      ((beta.val : ℝ)) ^ (prec - s).toNat = bpow beta (prec - s) := by
    have := IZR_Zpower beta h_prec_s_nn; push_cast at this; exact this
  have h_M_strict_real : ((M_total : ℤ) : ℝ) < bpow beta (prec - s) + 1/2 := by
    have h_step : ((M_total : ℤ) : ℝ) * bpow beta (s + cx)
                  < bpow beta m + bpow beta (s + cx) / 2 := by
      rw [← h_hx_form]; exact h_hx_abs_lt
    rw [h_bpow_m_eq] at h_step
    have h_factor : bpow beta (prec - s) * bpow beta (s + cx) + bpow beta (s + cx) / 2
                  = (bpow beta (prec - s) + 1/2) * bpow beta (s + cx) := by ring
    rw [h_factor] at h_step
    exact (mul_lt_mul_iff_of_pos_right h_bpow_scx_pos).mp h_step
  have h_2M_strict_int : 2 * M_total < 2 * (beta.val : ℤ) ^ (prec - s).toNat + 1 := by
    have h_real : (((2 * M_total : ℤ) : ℝ))
                < (((2 * (beta.val : ℤ) ^ (prec - s).toNat + 1 : ℤ) : ℝ)) := by
      push_cast; rw [h_pow_real_pushed]; linarith
    exact_mod_cast h_real
  have h_M_le_pow : M_total ≤ (beta.val : ℤ) ^ (prec - s).toNat := by omega
  -- |M_total| = M_total (since positive).
  have h_M_abs : |M_total| = M_total := abs_of_pos h_M_pos
  -- Three-way case split: boundary, hard, low-mag.
  -- Bridge: ((beta.val ^ d.toNat : ℤ) : ℝ) = bpow beta d for d ≥ 0.
  have h_bpow_psm1 : ((beta.val ^ (prec - s - 1).toNat : ℤ) : ℝ)
                   = bpow beta (prec - s - 1) :=
    IZR_Zpower beta h_prec_s_m1_nn
  have h_bpow_ps : ((beta.val ^ (prec - s).toNat : ℤ) : ℝ) = bpow beta (prec - s) :=
    IZR_Zpower beta h_prec_s_nn
  by_cases h_boundary : M_total = beta.val ^ (prec - s).toNat
  · -- BOUNDARY: M_total = β^(prec-s). hx = β^m. Canonical mantissa = β^(prec-s-1), even.
    have h_hx_eq_bpow : hx = bpow beta m := by
      rw [h_hx_form, h_boundary]
      rw [show ((beta.val ^ (prec - s).toNat : ℤ) : ℝ) * bpow beta (s + cx)
            = bpow beta (prec - s) * bpow beta (s + cx) from by rw [h_bpow_ps],
          ← h_bpow_m_eq]
    -- Build g = ⟨β^(prec-s-1), m+1-(prec-s)⟩.
    refine ⟨⟨beta.val ^ (prec - s - 1).toNat, m + 1 - (prec - s)⟩, ?_, ?_, ?_⟩
    · -- F2R g = hx = β^m.
      show hx = ((beta.val ^ (prec - s - 1).toNat : ℤ) : ℝ)
                * bpow beta (m + 1 - (prec - s))
      rw [h_hx_eq_bpow, h_bpow_psm1, ← bpow_plus]
      congr 1; ring
    · -- canonical: cexp at exp m+1-(prec-s).
      have h_F2R_eq : F2R (beta := beta)
                        ⟨beta.val ^ (prec - s - 1).toNat, m + 1 - (prec - s)⟩
                      = bpow beta m := by
        show ((beta.val ^ (prec - s - 1).toNat : ℤ) : ℝ)
             * bpow beta (m + 1 - (prec - s)) = bpow beta m
        rw [h_bpow_psm1, ← bpow_plus]
        congr 1; ring
      show m + 1 - (prec - s) = cexp beta (FLX_exp (prec - s)) _
      rw [h_F2R_eq]
      show m + 1 - (prec - s) = FLX_exp (prec - s) (mag beta (bpow beta m))
      rw [mag_bpow]
      unfold FLX_exp; ring
    · -- Even β^(prec-s-1) since prec-s-1 ≥ 1.
      exact even_pow_of_pos beta h_even_beta (by linarith : (1 : ℤ) ≤ prec - s - 1)
  · -- INTERIOR: M_total < β^(prec-s). Now subdivide on β^(prec-s-1).
    have h_M_lt_pow : M_total < (beta.val : ℤ) ^ (prec - s).toNat := by
      cases lt_or_eq_of_le h_M_le_pow with
      | inl h => exact h
      | inr h => exact absurd h h_boundary
    by_cases h_hard : beta.val ^ (prec - s - 1).toNat ≤ M_total
    · -- HARD INTERIOR: β^(prec-s-1) ≤ M_total < β^(prec-s). Use h_parity_hard.
      have h_M_even : Even M_total :=
        h_parity_hard M_total h_hx_form
          (by rw [h_M_abs]; exact h_hard)
          (by rw [h_M_abs]; exact h_M_lt_pow)
      -- Build g = ⟨M_total, s+cx⟩.
      refine ⟨⟨M_total, s + cx⟩, h_hx_form, ?_, h_M_even⟩
      -- Canonical: mag(hx) = m, so cexp_{prec-s}(hx) = m - (prec-s) = s+cx.
      show s + cx = cexp beta (FLX_exp (prec - s)) (F2R (beta := beta) ⟨M_total, s + cx⟩)
      have h_F2R_eq : F2R (beta := beta) ⟨M_total, s + cx⟩ = hx := h_hx_form.symm
      rw [h_F2R_eq]
      show s + cx = FLX_exp (prec - s) (mag beta hx)
      have h_mag_hx : mag beta hx = m := by
        apply mag_unique_pos beta
        · -- β^(m-1) ≤ hx
          have h_lo_real : ((beta.val ^ (prec - s - 1).toNat : ℤ) : ℝ)
                          ≤ ((M_total : ℤ) : ℝ) := by exact_mod_cast h_hard
          have h_lo_bpow : bpow beta (prec - s - 1) ≤ ((M_total : ℤ) : ℝ) := by
            rw [← h_bpow_psm1]; exact h_lo_real
          calc bpow beta (m - 1)
              = bpow beta (prec - s - 1) * bpow beta (s + cx) := by
                rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
            _ ≤ ((M_total : ℤ) : ℝ) * bpow beta (s + cx) :=
                mul_le_mul_of_nonneg_right h_lo_bpow (le_of_lt h_bpow_scx_pos)
            _ = hx := h_hx_form.symm
        · -- hx < β^m
          have h_M_real_lt : ((M_total : ℤ) : ℝ) < bpow beta (prec - s) := by
            have : (((M_total : ℤ)) : ℝ) < ((beta.val ^ (prec - s).toNat : ℤ) : ℝ) := by
              exact_mod_cast h_M_lt_pow
            rw [h_bpow_ps] at this; exact this
          calc hx = ((M_total : ℤ) : ℝ) * bpow beta (s + cx) := h_hx_form
            _ < bpow beta (prec - s) * bpow beta (s + cx) :=
                (mul_lt_mul_iff_of_pos_right h_bpow_scx_pos).mpr h_M_real_lt
            _ = bpow beta m := h_bpow_m_eq.symm
      rw [h_mag_hx]
      unfold FLX_exp; rw [hcx_eq]; ring
    · -- LOW-MAG INTERIOR: M_total < β^(prec-s-1). Build g at lower canonical exp.
      push_neg at h_hard
      have h_M_real_lt_low : ((M_total : ℤ) : ℝ) < bpow beta (prec - s - 1) := by
        have : (((M_total : ℤ)) : ℝ) < ((beta.val ^ (prec - s - 1).toNat : ℤ) : ℝ) := by
          exact_mod_cast h_hard
        rw [h_bpow_psm1] at this; exact this
      have h_hx_lt_bpow_m1 : hx < bpow beta (m - 1) := by
        calc hx = ((M_total : ℤ) : ℝ) * bpow beta (s + cx) := h_hx_form
          _ < bpow beta (prec - s - 1) * bpow beta (s + cx) :=
              (mul_lt_mul_iff_of_pos_right h_bpow_scx_pos).mpr h_M_real_lt_low
          _ = bpow beta (m - 1) := by rw [← bpow_plus]; congr 1; rw [hcx_eq]; ring
      -- Canonical exp = mag(hx) - (prec-s) ≤ (m-1) - (prec-s) = s + cx - 1.
      set e_can : ℤ := cexp beta (FLX_exp (prec - s)) hx with he_can_def
      have h_e_can_lt : e_can ≤ s + cx - 1 := by
        show FLX_exp (prec - s) (mag beta hx) ≤ s + cx - 1
        unfold FLX_exp
        have h_mag_le : mag beta hx ≤ m - 1 := by
          apply mag_le_bpow beta (ne_of_gt h_hx_pos)
          rw [abs_of_pos h_hx_pos]; exact h_hx_lt_bpow_m1
        linarith
      -- Build g = ⟨M_total · β^d, e_can⟩ where d = (s+cx) - e_can ≥ 1.
      set d : ℤ := (s + cx) - e_can with hd_def
      have hd_pos : 1 ≤ d := by simp [hd_def]; linarith
      have hd_nn : 0 ≤ d := by linarith
      have h_bpow_d : ((beta.val ^ d.toNat : ℤ) : ℝ) = bpow beta d :=
        IZR_Zpower beta hd_nn
      have h_bpow_split : bpow beta d * bpow beta e_can = bpow beta (s + cx) := by
        rw [← bpow_plus]; congr 1; simp [hd_def]
      refine ⟨⟨M_total * beta.val ^ d.toNat, e_can⟩, ?_, ?_, ?_⟩
      · -- F2R g = hx
        show hx = ((M_total * beta.val ^ d.toNat : ℤ) : ℝ) * bpow beta e_can
        rw [Int.cast_mul, h_bpow_d, mul_assoc, h_bpow_split]
        exact h_hx_form
      · -- canonical
        have h_F2R_eq : F2R (beta := beta)
                          ⟨M_total * beta.val ^ d.toNat, e_can⟩ = hx := by
          show ((M_total * beta.val ^ d.toNat : ℤ) : ℝ) * bpow beta e_can = hx
          rw [Int.cast_mul, h_bpow_d, mul_assoc, h_bpow_split]
          exact h_hx_form.symm
        show e_can = cexp beta (FLX_exp (prec - s)) _
        rw [h_F2R_eq]
      · -- Even M_total · β^d.toNat since d ≥ 1.
        have h_pow_even : Even (beta.val ^ d.toNat) :=
          even_pow_of_pos beta h_even_beta hd_pos
        exact h_pow_even.mul_left _

/-- **Veltkamp's `hx` is at `Rnd_NE_pt`, even-radix case (tie-conditional).**
For even radix β, combines `Veltkamp_hx_Rnd_N_pt_FLX` with an internal
case split on tie status at coarser precision:
- **No tie** (`|x − hx| < β^(s+cx)/2`): uniqueness branch of `Rnd_NG_pt`.
- **Tie** (`|x − hx| = β^(s+cx)/2`): `NE_prop` branch, dispatched via
  the `Veltkamp_hx_NE_prop_FLX_even_radix` dichotomy.

The hypothesis is tie-conditional: parity of `M_total` is only required
at a coarse tie in the hard interior subcase. This is the form that is
actually discharged by Pff's `VeltkampEven1` argument restricted to ties. -/
theorem Veltkamp_hx_Rnd_NE_pt_FLX_even_radix
    (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (h_even_beta : Even beta.val)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_parity_at_tie_hard :
       ∀ M : ℤ,
         Veltkamp_hx_FLX beta prec choice s x
           = (M : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) →
         |x - Veltkamp_hx_FLX beta prec choice s x|
           = bpow beta (s + cexp beta (FLX_exp prec) x) / 2 →
         (beta.val : ℤ) ^ ((prec - s - 1).toNat) ≤ |M| →
         |M| < (beta.val : ℤ) ^ (prec - s).toNat →
         Even M) :
    Rnd_NE_pt beta (FLX_exp (prec - s)) x
              (Veltkamp_hx_FLX beta prec choice s x) := by
  set hx := Veltkamp_hx_FLX beta prec choice s x with hhx_def
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  have hcx_eq : cx = mag beta x - prec := rfl
  have hp_minus_s_pos : 0 < prec - s := by linarith
  have hValid_coarse := FLX_exp_valid (prec - s) hp_minus_s_pos
  have h_Rnd_N : Rnd_N_pt (generic_format beta (FLX_exp (prec - s))) x hx :=
    Veltkamp_hx_Rnd_N_pt_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  refine ⟨h_Rnd_N, ?_⟩
  have h_err : |x - hx| ≤ bpow beta (s + cx) / 2 :=
    Veltkamp_aux_FLX beta prec hp choice Fx hx_pos hs_lo hs_hi
  rcases lt_or_eq_of_le h_err with h_strict | h_tie
  · -- No tie: prove uniqueness.
    right
    intro f Hf
    by_cases hF_x : generic_format beta (FLX_exp (prec - s)) x
    · -- x ∈ F(prec-s): both hx and f equal x.
      have h_hx_x : hx = x := Rnd_N_pt_idempotent _ h_Rnd_N hF_x
      have h_f_x : f = x := Rnd_N_pt_idempotent _ Hf hF_x
      rw [h_f_x, h_hx_x]
    · -- x ∉ F(prec-s): use Rnd_N_pt_unique.
      set d := round beta (FLX_exp (prec - s)) (fun y : ℝ => ⌊y⌋) x with hd_def
      set u := round beta (FLX_exp (prec - s)) (fun y : ℝ => ⌈y⌉) x with hu_def
      have h_dn : Rnd_DN_pt (generic_format beta (FLX_exp (prec - s))) x d :=
        round_DN_pt _ _ hValid_coarse x
      have h_up : Rnd_UP_pt (generic_format beta (FLX_exp (prec - s))) x u :=
        round_UP_pt _ _ hValid_coarse x
      -- u - d = β^(s+cx).
      have h_u_eq : u = d + ulp beta (FLX_exp (prec - s)) x :=
        round_UP_DN_ulp beta (FLX_exp (prec - s)) hF_x
      have h_ulp : ulp beta (FLX_exp (prec - s)) x = bpow beta (s + cx) := by
        rw [ulp_neq_0 beta _ (ne_of_gt hx_pos)]
        show bpow beta (FLX_exp (prec - s) (mag beta x)) = bpow beta (s + cx)
        congr 1
        unfold FLX_exp; rw [hcx_eq]; ring
      have h_u_d : u - d = bpow beta (s + cx) := by
        rw [h_u_eq, h_ulp]; ring
      -- x - d ≠ u - x: from strict |x - hx| < β^(s+cx)/2 and hx ∈ {d, u}.
      have h_no_tie : x - d ≠ u - x := by
        intro h_eq_dist
        have h_d_le_x : d ≤ x := h_dn.2.1
        have h_x_le_u : x ≤ u := h_up.2.1
        -- u - x = β^(s+cx) / 2 from h_eq_dist and h_u_d.
        have h_ux_half : u - x = bpow beta (s + cx) / 2 := by linarith
        have h_xd_half : x - d = bpow beta (s + cx) / 2 := by linarith
        -- hx ∈ {d, u}.
        rcases Rnd_N_pt_DN_or_UP _ h_Rnd_N with h_hx_DN | h_hx_UP
        · -- hx is Rnd_DN_pt, hence hx = d.
          have h_hx_d : hx = d := Rnd_DN_pt_unique _ h_hx_DN h_dn
          have h_dist : |x - hx| = bpow beta (s + cx) / 2 := by
            rw [h_hx_d, abs_of_nonneg (by linarith : 0 ≤ x - d), h_xd_half]
          linarith
        · -- hx is Rnd_UP_pt, hence hx = u.
          have h_hx_u : hx = u := Rnd_UP_pt_unique _ h_hx_UP h_up
          have h_dist : |x - hx| = bpow beta (s + cx) / 2 := by
            rw [h_hx_u]
            rw [show x - u = -(u - x) from by ring, abs_neg,
                abs_of_nonneg (by linarith : 0 ≤ u - x), h_ux_half]
          linarith
      exact Rnd_N_pt_unique _ h_dn h_up h_no_tie Hf h_Rnd_N
  · -- Tie: prove NE_prop via the dichotomy.
    left
    apply Veltkamp_hx_NE_prop_FLX_even_radix beta prec hp choice
      h_even_beta Fx hx_pos hs_lo hs_hi
    intro M hM h_lo h_hi
    exact h_parity_at_tie_hard M hM h_tie h_lo h_hi

/-! ### Pff parity argument at coarse tie + hard interior (sketch only)

The path-2 dichotomy reduces the parity-at-tie work to: for even β and
the NE choice, at a coarse tie in the hard interior, `M_total = Mp + Mq`
is even. The argument (Pff's `VeltkampEven1` lines 14375-14776, ~292 Coq
lines for the unrestricted problem; ~150-200 Lean lines for our
restricted version) has the following key algebraic structure:

At a coarse tie with `mag(hx) = mag(x)`,
`x = (M_total + ε/2) · β^(s+cx)` for some `ε ∈ {−1, +1}`. Then

  `x · C = (β^s + 1) · (2 M_total + ε) / 2 · β^(s+cx)`.

For even β with `s ≥ 1`, both `(β^s + 1)` (odd since `β^s` even) and
`(2 M_total + ε)` (odd) are odd. So `x · C` is at a half-integer
multiple of `β^(s+cx)`.

Subcases on `cexp(p)`:
- `cexp(p) = s + cx`: `x · C` is at the prec-precision midpoint. So
  `p = round_NE(x · C)` selects the even-canonical-mantissa side
  (via `round_NE_pt_pos` / `Rnd_NE_pt`'s `NE_prop` branch). Hence
  `Mp = M_p_canonical` is even.
- `cexp(p) = s + cx + 1`: `Mp = M_p_canonical · β`, β factor → even.

Symmetric argument for `Mq`: at the same coarse tie,
`x − p = (−2 M_x ± 1) · β^(s+cx) / 2`, also a half-integer multiple of
`β^(s+cx)`. Same subcases on `cexp(q)` give `Mq` even.

Hence `M_total = Mp + Mq` is even.

The work to port this is well-scoped: each Lean lemma corresponds to a
specific subcase of the argument, and the existing format-side helpers
(`Veltkamp_p_at_scx_FLX`, `Veltkamp_q_at_scx_FLX`, `hxExact_FLX`) plus
`round_NE_pt_pos` provide most of the machinery. Pending future
session(s).
-/

/-- **Veltkamp_Even at FLX (refined, even-radix, tie-conditional).** Takes
just the tie-conditional hard-case parity hypothesis (rather than the full
`Rnd_NE_pt`) and concludes `round_NE = hx`. For odd radix, prefer
`Veltkamp_Even_FLX_odd` (which discharges the parity gap entirely via
no-tie). For even radix, this is the cleanest entry point modulo the
remaining `M_total`-even at-tie parity work. -/
theorem Veltkamp_Even_FLX_even_radix
    (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (h_even_beta : Even beta.val)
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_pos : 0 < x) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec)
    (h_parity_at_tie_hard :
       ∀ M : ℤ,
         Veltkamp_hx_FLX beta prec choice s x
           = (M : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) →
         |x - Veltkamp_hx_FLX beta prec choice s x|
           = bpow beta (s + cexp beta (FLX_exp prec) x) / 2 →
         (beta.val : ℤ) ^ ((prec - s - 1).toNat) ≤ |M| →
         |M| < (beta.val : ℤ) ^ (prec - s).toNat →
         Even M) :
    round_NE beta (FLX_exp (prec - s)) x
      = Veltkamp_hx_FLX beta prec choice s x := by
  apply Veltkamp_Even_FLX_of_Rnd_NE_pt beta prec choice hs_hi
  exact Veltkamp_hx_Rnd_NE_pt_FLX_even_radix beta prec hp choice
    h_even_beta Fx hx_pos hs_lo hs_hi h_parity_at_tie_hard

end LeanFlocq
