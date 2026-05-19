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

end LeanFlocq
