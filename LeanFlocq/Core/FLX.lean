/-
Port of `flocq/src/Core/FLX.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Floating-point format with bounded normalized mantissas and unbounded
exponent range. `FLX_format beta prec x` holds when `x = F2R ⟨m, e⟩`
for some mantissa `m` with `|m| < β^prec`.
-/

import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FIX

namespace LeanFlocq

/-- A real `x` is in the FLX format with precision `prec` if it is the F2R of
some float with mantissa bounded by `β^prec`. -/
def FLX_format (beta : radix) (prec : ℤ) (x : ℝ) : Prop :=
  ∃ f : float beta, x = F2R f ∧ |f.Fnum| < (beta.val : ℤ) ^ prec.toNat

/-- The FLX exponent function: `e ↦ e - prec`. -/
def FLX_exp (prec : ℤ) : ℤ → ℤ := fun e => e - prec

/-- `FLX_exp prec` is a `Valid_exp` whenever `0 < prec`. The "large" branch is
vacuously true because `prec > 0` makes `k ≤ k - prec` impossible. -/
theorem FLX_exp_valid (prec : ℤ) (hp : 0 < prec) : Valid_exp (FLX_exp prec) := by
  intro k
  refine ⟨?_, ?_⟩
  · intro _; unfold FLX_exp; linarith
  · intro hk
    exfalso
    unfold FLX_exp at hk
    linarith

/-- Every FLX-format real is in the generic format with `FLX_exp prec`. -/
theorem generic_format_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : FLX_format beta prec x) : generic_format beta (FLX_exp prec) x := by
  obtain ⟨⟨mx, ex⟩, hx, hb⟩ := h
  rw [hx]
  apply generic_format_F2R beta (FLX_exp prec) mx ex
  intro hmx_ne
  show FLX_exp prec (mag beta (F2R (beta := beta) ⟨mx, ex⟩)) ≤ ex
  unfold FLX_exp
  -- Need: mag (F2R ⟨mx, ex⟩) - prec ≤ ex, i.e. mag ≤ ex + prec.
  have h_F2R_ne : F2R (beta := beta) ⟨mx, ex⟩ ≠ 0 := by
    intro hz; exact hmx_ne (eq_0_F2R (beta := beta) hz)
  -- Lift the integer bound on |mx| to a real bound.
  have hmx_real : (|(mx : ℝ)|) < bpow beta prec := by
    have hb_real : ((|mx| : ℤ) : ℝ) < ((beta.val ^ prec.toNat : ℤ) : ℝ) := by
      exact_mod_cast hb
    rw [show ((|mx| : ℤ) : ℝ) = |(mx : ℝ)| from by push_cast; rfl] at hb_real
    rwa [IZR_Zpower beta (le_of_lt hp)] at hb_real
  -- |F2R ⟨mx, ex⟩| < bpow (ex + prec)
  have h_abs_F2R : |F2R (beta := beta) ⟨mx, ex⟩| < bpow beta (ex + prec) := by
    unfold F2R
    show |(mx : ℝ) * bpow beta ex| < bpow beta (ex + prec)
    rw [abs_mul, abs_of_pos (bpow_gt_0 beta ex), bpow_plus, mul_comm (bpow beta ex) _]
    exact (mul_lt_mul_iff_of_pos_right (bpow_gt_0 beta ex)).mpr hmx_real
  have h_mag_le : mag beta (F2R (beta := beta) ⟨mx, ex⟩) ≤ ex + prec :=
    mag_le_bpow beta h_F2R_ne h_abs_F2R
  linarith

/-- Every generic-format-with-`FLX_exp` real is in the FLX format. -/
theorem FLX_format_generic (beta : radix) (prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : generic_format beta (FLX_exp prec) x) : FLX_format beta prec x := by
  refine ⟨⟨Ztrunc (scaled_mantissa beta (FLX_exp prec) x),
           cexp beta (FLX_exp prec) x⟩, h, ?_⟩
  show |Ztrunc (scaled_mantissa beta (FLX_exp prec) x)| < (beta.val : ℤ) ^ prec.toNat
  set sm := scaled_mantissa beta (FLX_exp prec) x with hsm_def
  -- Step 1: |sm| < bpow prec.
  have hsm_bound : |sm| < bpow beta prec := by
    by_cases hx : x = 0
    · rw [hsm_def]
      unfold scaled_mantissa
      rw [hx, zero_mul, abs_zero]
      exact bpow_gt_0 beta prec
    · rw [hsm_def]
      unfold scaled_mantissa
      rw [abs_mul, abs_of_pos (bpow_gt_0 beta _)]
      have h_mag : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
      have h_cexp : (cexp beta (FLX_exp prec) x : ℤ) = mag beta x - prec := by
        unfold cexp FLX_exp; rfl
      calc |x| * bpow beta (-cexp beta (FLX_exp prec) x)
          < bpow beta (mag beta x) * bpow beta (-cexp beta (FLX_exp prec) x) := by
            exact (mul_lt_mul_iff_of_pos_right (bpow_gt_0 beta _)).mpr h_mag
        _ = bpow beta (mag beta x + (-cexp beta (FLX_exp prec) x)) := by
            rw [← bpow_plus]
        _ = bpow beta prec := by
            rw [h_cexp]
            congr 1; ring
  -- Step 2: identify Ztrunc(sm) as sm.
  have h_eq_sm : ((Ztrunc sm : ℤ) : ℝ) = sm := by
    have := scaled_mantissa_generic beta (FLX_exp prec) h
    rw [← hsm_def] at this
    exact this.symm
  -- Step 3: bring the bound to integer form.
  have h_real : ((|Ztrunc sm| : ℤ) : ℝ) < ((beta.val ^ prec.toNat : ℤ) : ℝ) := by
    have h1 : ((|Ztrunc sm| : ℤ) : ℝ) = |((Ztrunc sm : ℤ) : ℝ)| := by push_cast; rfl
    rw [h1, h_eq_sm, IZR_Zpower beta (le_of_lt hp)]
    exact hsm_bound
  exact_mod_cast h_real

/-- The FLX format admits all the abstract round predicates from `Round_pred`. -/
theorem FLX_format_satisfies_any (beta : radix) (prec : ℤ) (hp : 0 < prec) :
    satisfies_any (FLX_format beta prec) := by
  refine satisfies_any_eq (F1 := generic_format beta (FLX_exp prec)) ?_
    (generic_format_satisfies_any beta (FLX_exp prec) (FLX_exp_valid prec hp))
  intro x
  exact ⟨FLX_format_generic beta prec hp, generic_format_FLX beta prec hp⟩

/-- `FLX_exp prec` is monotone — it's just the identity shifted by `-prec`. -/
theorem FLX_exp_monotone (prec : ℤ) : Monotone_exp (FLX_exp prec) := by
  intro ex ey hxy
  unfold FLX_exp
  linarith

/-- A FIX-format value within the magnitude band `bpow (e-1) ≤ |x| ≤ bpow e`
is in the FLX format. Uses `generic_inclusion`. -/
theorem FLX_format_FIX (beta : radix) (prec : ℤ) (hp : 0 < prec) {x : ℝ} (e : ℤ)
    (Hx : bpow beta (e - 1) ≤ |x| ∧ |x| ≤ bpow beta e)
    (Fx : FIX_format beta (e - prec) x) : FLX_format beta prec x := by
  apply FLX_format_generic beta prec hp
  have hg : generic_format beta (FIX_exp (e - prec)) x :=
    generic_format_FIX beta (e - prec) Fx
  -- Apply generic_inclusion: FIX_exp (e-prec) ≤ FLX_exp prec at e.
  have hle : FIX_exp (e - prec) e ≤ FLX_exp prec e := by
    unfold FIX_exp FLX_exp; linarith
  exact generic_inclusion beta (FIX_exp (e - prec)) (FLX_exp prec)
    (FIX_exp_valid (e - prec)) (FLX_exp_valid prec hp) e hle Hx hg

/-- The FLX format has no minimum exponent: `negligible_exp = none`. -/
theorem negligible_exp_FLX (prec : ℤ) (hp : 0 < prec) :
    negligible_exp (FLX_exp prec) = none := by
  classical
  unfold negligible_exp
  have h_no : ¬ ∃ n : ℤ, n ≤ FLX_exp prec n := by
    rintro ⟨n, hn⟩
    unfold FLX_exp at hn; linarith
  exact dif_neg h_no

/-- In FLX, `ulp 0 = 0` — there is no smallest representable positive value. -/
theorem ulp_FLX_0 (beta : radix) (prec : ℤ) (hp : 0 < prec) :
    ulp beta (FLX_exp prec) 0 = 0 := by
  unfold ulp
  rw [if_pos rfl, negligible_exp_FLX prec hp]

/-- `1` is in the FLX format. -/
theorem generic_format_FLX_1 (beta : radix) (prec : ℤ) (hp : 0 < prec) :
    generic_format beta (FLX_exp prec) 1 := by
  have h := generic_format_bpow' beta (FLX_exp prec)
    (FLX_exp_valid prec hp) 0 ?_
  · rwa [bpow_zero] at h
  · unfold FLX_exp; linarith

/-- In FLX, rounding to zero forces the input to be zero — there's no
underflow. -/
theorem eq_0_round_0_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ}
    (Hx : round beta (FLX_exp prec) rnd x = 0) : x = 0 :=
  eq_0_round_0_negligible_exp beta (FLX_exp prec) (FLX_exp_valid prec hp)
    (negligible_exp_FLX prec hp) rnd Hx

/-- In FLX, rounding preserves strict positivity: `0 < x → 0 < round x`. -/
theorem gt_0_round_gt_0_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ} (hx : 0 < x) :
    0 < round beta (FLX_exp prec) rnd x := by
  have h_round_nn : 0 ≤ round beta (FLX_exp prec) rnd x := by
    have := round_le beta (FLX_exp prec) (FLX_exp_valid prec hp) rnd (le_of_lt hx)
    rwa [round_0] at this
  rcases lt_or_eq_of_le h_round_nn with h | h
  · exact h
  · exfalso
    have := eq_0_round_0_FLX beta prec hp rnd h.symm
    linarith

/-- The ulp at `1` in FLX is `β^(1 - prec)`. -/
theorem ulp_FLX_1 (beta : radix) (prec : ℤ) :
    ulp beta (FLX_exp prec) 1 = bpow beta (1 - prec) := by
  rw [ulp_neq_0 beta (FLX_exp prec) one_ne_zero]
  show bpow beta (cexp beta (FLX_exp prec) 1) = bpow beta (1 - prec)
  unfold cexp FLX_exp
  rw [mag_1]

/-- The successor of `1` in FLX is `1 + β^(1 - prec)`. -/
theorem succ_FLX_1 (beta : radix) (prec : ℤ) :
    succ beta (FLX_exp prec) 1 = 1 + bpow beta (1 - prec) := by
  rw [succ_eq_pos beta (FLX_exp prec) (zero_le_one), ulp_FLX_1]

/-- A FLX value within the magnitude band `bpow(e-1) ≤ |x| ≤ bpow e` is in
the FIX format with exponent `e - prec`. Converse direction of `FLX_format_FIX`. -/
theorem FIX_format_FLX (beta : radix) (prec : ℤ) {x : ℝ} (e : ℤ)
    (Hx : bpow beta (e - 1) ≤ |x| ∧ |x| ≤ bpow beta e)
    (Fx : FLX_format beta prec x) : FIX_format beta (e - prec) x := by
  obtain ⟨⟨xm, xe⟩, h1, h2⟩ := Fx
  -- x = F2R ⟨xm, xe⟩, |xm| < β^prec.toNat, bpow(e-1) ≤ |x|.
  -- Apply F2R_prec_normalize with m=xm, e=xe, e'=e, p=prec.
  -- Get x = F2R ⟨xm * β^(xe - e + prec), e - prec⟩.
  refine ⟨⟨xm * (beta.val : ℤ) ^ (xe - e + prec).toNat, e - prec⟩, ?_, rfl⟩
  rw [h1]
  apply F2R_prec_normalize
  · exact h2
  · rw [← h1]; exact Hx.1

/-- The "normalized" FLX format: `x = F2R ⟨m, e⟩` with `β^(prec-1) ≤ |m| < β^prec`
when `x ≠ 0`. -/
def FLXN_format (beta : radix) (prec : ℤ) (x : ℝ) : Prop :=
  ∃ f : float beta,
    x = F2R f ∧
    (x ≠ 0 →
      (beta.val : ℤ) ^ (prec - 1).toNat ≤ |f.Fnum| ∧
      |f.Fnum| < (beta.val : ℤ) ^ prec.toNat)

/-- Every FLXN-format value is in the generic FLX format. -/
theorem generic_format_FLXN (beta : radix) (prec : ℤ) (hp : 0 < prec)
    {x : ℝ} (h : FLXN_format beta prec x) : generic_format beta (FLX_exp prec) x := by
  obtain ⟨⟨xm, xe⟩, hx, hb⟩ := h
  by_cases hx0 : x = 0
  · rw [hx0]; exact generic_format_0 beta _
  · apply generic_format_FLX beta prec hp
    refine ⟨⟨xm, xe⟩, hx, ?_⟩
    exact (hb hx0).2

/-- Every FLX value is FLXN — when nonzero, its canonical mantissa is normalized. -/
theorem FLXN_format_generic (beta : radix) (prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : generic_format beta (FLX_exp prec) x) : FLXN_format beta prec x := by
  refine ⟨⟨Ztrunc (scaled_mantissa beta (FLX_exp prec) x),
           cexp beta (FLX_exp prec) x⟩, h, ?_⟩
  intro hx0
  set m := Ztrunc (scaled_mantissa beta (FLX_exp prec) x) with hm_def
  show (beta.val : ℤ) ^ (prec - 1).toNat ≤ |m| ∧
       |m| < (beta.val : ℤ) ^ prec.toNat
  have hp1_nn : 0 ≤ prec - 1 := by linarith
  have hp_nn : 0 ≤ prec := by linarith
  have h_sm_eq : scaled_mantissa beta (FLX_exp prec) x = (m : ℝ) :=
    scaled_mantissa_generic beta (FLX_exp prec) h
  have h_mag_lo : bpow beta (mag beta x - 1) ≤ |x| := bpow_mag_le beta hx0
  have h_mag_hi : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
  -- |m| as ℝ = |x| * bpow(prec - mag x)
  have h_m_abs_real : (|m| : ℝ) = |x| * bpow beta (prec - mag beta x) := by
    have h_step : |scaled_mantissa beta (FLX_exp prec) x|
        = |x| * bpow beta (prec - mag beta x) := by
      unfold scaled_mantissa cexp FLX_exp
      rw [abs_mul, abs_of_pos (bpow_gt_0 _ _)]
      congr 1
      rw [show -(mag beta x - prec) = prec - mag beta x from by ring]
    rw [← h_step, h_sm_eq]
  -- Bounds in ℝ form
  have h_lower_real : bpow beta (prec - 1) ≤ (|m| : ℝ) := by
    rw [h_m_abs_real]
    calc bpow beta (prec - 1)
        = bpow beta (mag beta x - 1) * bpow beta (prec - mag beta x) := by
          rw [← bpow_plus]; congr 1; ring
      _ ≤ |x| * bpow beta (prec - mag beta x) :=
          mul_le_mul_of_nonneg_right h_mag_lo (bpow_ge_0 _ _)
  have h_upper_real : (|m| : ℝ) < bpow beta prec := by
    rw [h_m_abs_real]
    calc |x| * bpow beta (prec - mag beta x)
        < bpow beta (mag beta x) * bpow beta (prec - mag beta x) :=
          mul_lt_mul_of_pos_right h_mag_hi (bpow_gt_0 _ _)
      _ = bpow beta prec := by rw [← bpow_plus]; congr 1; ring
  -- Cast to integer form
  have h_lower : (beta.val : ℤ) ^ (prec - 1).toNat ≤ |m| := by
    have h_pow_eq : (((beta.val : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) = bpow beta (prec - 1) :=
      IZR_Zpower beta hp1_nn
    have : (((beta.val : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
      rw [h_pow_eq]; push_cast; exact h_lower_real
    exact_mod_cast this
  have h_upper : |m| < (beta.val : ℤ) ^ prec.toNat := by
    have h_pow_eq : (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) = bpow beta prec :=
      IZR_Zpower beta hp_nn
    have : ((|m| : ℤ) : ℝ) < (((beta.val : ℤ) ^ prec.toNat : ℤ) : ℝ) := by
      rw [h_pow_eq]; push_cast; exact h_upper_real
    exact_mod_cast this
  exact ⟨h_lower, h_upper⟩

/-- The FLXN format admits all the abstract round predicates. -/
theorem FLXN_format_satisfies_any (beta : radix) (prec : ℤ) (hp : 0 < prec) :
    satisfies_any (FLXN_format beta prec) := by
  refine satisfies_any_eq (F1 := generic_format beta (FLX_exp prec)) ?_
    (generic_format_satisfies_any beta (FLX_exp prec) (FLX_exp_valid prec hp))
  intro x
  exact ⟨FLXN_format_generic beta prec hp, generic_format_FLXN beta prec hp⟩

/-- In FLX, `ulp x ≤ |x| * β^(1-prec)` — the ulp grows at most this fast in `|x|`. -/
theorem ulp_FLX_le (beta : radix) (prec : ℤ) (hp : 0 < prec) (x : ℝ) :
    ulp beta (FLX_exp prec) x ≤ |x| * bpow beta (1 - prec) := by
  by_cases hx : x = 0
  · rw [hx, ulp_FLX_0 beta prec hp, abs_zero, zero_mul]
  · rw [ulp_neq_0 beta (FLX_exp prec) hx]
    show bpow beta (cexp beta (FLX_exp prec) x) ≤ |x| * bpow beta (1 - prec)
    unfold cexp FLX_exp
    rw [show mag beta x - prec = (mag beta x - 1) + (1 - prec) from by ring, bpow_plus]
    exact mul_le_mul_of_nonneg_right (bpow_mag_le beta hx) (bpow_ge_0 _ _)

/-- In FLX, `|x| * β^(-prec) ≤ ulp x` — the ulp is at least this fraction of `|x|`. -/
theorem ulp_FLX_ge (beta : radix) (prec : ℤ) (hp : 0 < prec) (x : ℝ) :
    |x| * bpow beta (-prec) ≤ ulp beta (FLX_exp prec) x := by
  by_cases hx : x = 0
  · rw [hx, ulp_FLX_0 beta prec hp, abs_zero, zero_mul]
  · rw [ulp_neq_0 beta (FLX_exp prec) hx]
    show |x| * bpow beta (-prec) ≤ bpow beta (cexp beta (FLX_exp prec) x)
    unfold cexp FLX_exp
    rw [show mag beta x - prec = mag beta x + (-prec) from by ring, bpow_plus]
    exact mul_le_mul_of_nonneg_right (le_of_lt (bpow_mag_gt beta x)) (bpow_ge_0 _ _)

/-- Ulp scales exactly by β^e under multiplication by β^e in FLX. -/
theorem ulp_FLX_exact_shift (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (x : ℝ) (e : ℤ) :
    ulp beta (FLX_exp prec) (x * bpow beta e)
      = ulp beta (FLX_exp prec) x * bpow beta e := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, ulp_FLX_0 beta prec hp]; ring
  · have h_xb_ne : x * bpow beta e ≠ 0 :=
      mul_ne_zero hx (ne_of_gt (bpow_gt_0 _ _))
    rw [ulp_neq_0 beta (FLX_exp prec) h_xb_ne, ulp_neq_0 beta (FLX_exp prec) hx]
    show bpow beta (cexp beta (FLX_exp prec) (x * bpow beta e))
        = bpow beta (cexp beta (FLX_exp prec) x) * bpow beta e
    unfold cexp FLX_exp
    rw [mag_mult_bpow beta hx e,
        show mag beta x + e - prec = (mag beta x - prec) + e from by ring,
        bpow_plus]

/-- Successor scales exactly by β^e under multiplication by β^e in FLX.
The positive case is `succ x = x + ulp x` distributing; the negative case
distributes through `pred_pos` with care at the `bpow` boundary. -/
theorem succ_FLX_exact_shift (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (x : ℝ) (e : ℤ) :
    succ beta (FLX_exp prec) (x * bpow beta e)
      = succ beta (FLX_exp prec) x * bpow beta e := by
  rcases le_or_gt 0 x with hx | hx
  · -- x ≥ 0: succ x = x + ulp x, distribute.
    have h_xe_nn : 0 ≤ x * bpow beta e :=
      mul_nonneg hx (bpow_ge_0 _ _)
    rw [succ_eq_pos beta (FLX_exp prec) h_xe_nn,
        succ_eq_pos beta (FLX_exp prec) hx,
        ulp_FLX_exact_shift beta prec hp]
    ring
  · -- x < 0: x * bpow e < 0 too. succ x = -pred_pos(-x).
    have h_bpow_pos : 0 < bpow beta e := bpow_gt_0 _ _
    have h_xe_neg : x * bpow beta e < 0 := mul_neg_of_neg_of_pos hx h_bpow_pos
    have h_neg_x_pos : 0 < -x := by linarith
    have h_succ_xe : succ beta (FLX_exp prec) (x * bpow beta e)
        = -(pred_pos beta (FLX_exp prec) (-x * bpow beta e)) := by
      unfold succ; rw [if_neg (not_le.mpr h_xe_neg)]
      rw [show -(x * bpow beta e) = -x * bpow beta e from by ring]
    have h_succ_x : succ beta (FLX_exp prec) x
        = -(pred_pos beta (FLX_exp prec) (-x)) := by
      unfold succ; rw [if_neg (not_le.mpr hx)]
    rw [h_succ_xe, h_succ_x]
    -- Goal: -pred_pos(-x * bpow e) = -pred_pos(-x) * bpow e
    -- Reduce to: pred_pos(-x * bpow e) = pred_pos(-x) * bpow e
    have h_pred_eq : pred_pos beta (FLX_exp prec) (-x * bpow beta e)
        = pred_pos beta (FLX_exp prec) (-x) * bpow beta e := by
      have h_neg_x_ne : -x ≠ 0 := ne_of_gt h_neg_x_pos
      have h_mag_xe : mag beta (-x * bpow beta e) = mag beta (-x) + e :=
        mag_mult_bpow beta h_neg_x_ne e
      by_cases h_bnd : -x = bpow beta (mag beta (-x) - 1)
      · -- Boundary case
        have h_xe_bnd : -x * bpow beta e
            = bpow beta (mag beta (-x * bpow beta e) - 1) := by
          rw [h_mag_xe,
              show mag beta (-x) + e - 1 = (mag beta (-x) - 1) + e from by ring,
              bpow_plus]
          conv_lhs => rw [h_bnd]
        unfold pred_pos
        rw [if_pos h_bnd, if_pos h_xe_bnd, h_mag_xe]
        unfold FLX_exp
        rw [show mag beta (-x) + e - 1 - prec
              = (mag beta (-x) - 1 - prec) + e from by ring, bpow_plus]
        ring
      · -- Non-boundary
        have h_xe_not_bnd : ¬ (-x * bpow beta e
            = bpow beta (mag beta (-x * bpow beta e) - 1)) := by
          intro heq
          apply h_bnd
          rw [h_mag_xe,
              show mag beta (-x) + e - 1 = (mag beta (-x) - 1) + e from by ring,
              bpow_plus] at heq
          exact mul_right_cancel₀ (ne_of_gt h_bpow_pos) heq
        unfold pred_pos
        rw [if_neg h_xe_not_bnd, if_neg h_bnd, ulp_FLX_exact_shift beta prec hp]
        ring
    rw [h_pred_eq]; ring

end LeanFlocq
