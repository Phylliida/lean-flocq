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

end LeanFlocq
