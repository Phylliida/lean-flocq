/-
Port of `flocq/src/Core/FTZ.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Floating-point format with abrupt underflow (flush-to-zero). Like FLX
but with a hard floor: values below `bpow (emin + prec - 1)` round to 0,
not to the nearest subnormal. The exponent function maps the small regime
to a fixed `emin + prec - 1`.
-/

import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FLX

namespace LeanFlocq

/-- A real `x` is in the FTZ format with parameters `(emin, prec)` if
`x = F2R ⟨m, e⟩` for some normalized mantissa `m` (with `β^(prec-1) ≤ |m| < β^prec`
when `x ≠ 0`) and exponent `e ≥ emin`. -/
def FTZ_format (beta : radix) (emin prec : ℤ) (x : ℝ) : Prop :=
  ∃ f : float beta,
    x = F2R f ∧
    (x ≠ 0 →
      (beta.val : ℤ) ^ (prec - 1).toNat ≤ |f.Fnum| ∧
      |f.Fnum| < (beta.val : ℤ) ^ prec.toNat) ∧
    emin ≤ f.Fexp

/-- The FTZ exponent function: in the small regime (`e - prec < emin`) it's
the constant `emin + prec - 1`; otherwise it's `e - prec` like FLX. -/
def FTZ_exp (emin prec : ℤ) : ℤ → ℤ := fun e =>
  if e - prec < emin then emin + prec - 1 else e - prec

/-- `FTZ_exp emin prec` is a `Valid_exp` whenever `0 < prec`. The "large"
branch is genuinely non-vacuous here: the small regime maps every `l ≤ emin + prec - 1`
to `emin + prec - 1` and stabilizes. -/
theorem FTZ_exp_valid (emin prec : ℤ) (hp : 0 < prec) :
    Valid_exp (FTZ_exp emin prec) := by
  intro k
  refine ⟨?_, ?_⟩
  · -- Branch 1: FTZ_exp k < k → FTZ_exp (k+1) ≤ k
    intro h_small
    by_cases hk1 : k - prec < emin
    · have hfk : FTZ_exp emin prec k = emin + prec - 1 := by
        unfold FTZ_exp; rw [if_pos hk1]
      rw [hfk] at h_small
      by_cases hk2 : (k + 1) - prec < emin
      · have hfk' : FTZ_exp emin prec (k + 1) = emin + prec - 1 := by
          unfold FTZ_exp; rw [if_pos hk2]
        rw [hfk']; linarith
      · have hfk' : FTZ_exp emin prec (k + 1) = (k + 1) - prec := by
          unfold FTZ_exp; rw [if_neg hk2]
        rw [hfk']; linarith
    · have hfk : FTZ_exp emin prec k = k - prec := by
        unfold FTZ_exp; rw [if_neg hk1]
      rw [hfk] at h_small
      push_neg at hk1
      by_cases hk2 : (k + 1) - prec < emin
      · have hfk' : FTZ_exp emin prec (k + 1) = emin + prec - 1 := by
          unfold FTZ_exp; rw [if_pos hk2]
        rw [hfk']; linarith
      · have hfk' : FTZ_exp emin prec (k + 1) = (k + 1) - prec := by
          unfold FTZ_exp; rw [if_neg hk2]
        rw [hfk']; linarith
  · -- Branch 2: k ≤ FTZ_exp k → stabilization conditions
    intro h_ge
    by_cases hk1 : k - prec < emin
    · have hfk : FTZ_exp emin prec k = emin + prec - 1 := by
        unfold FTZ_exp; rw [if_pos hk1]
      rw [hfk] at h_ge
      rw [hfk]
      refine ⟨?_, ?_⟩
      · -- FTZ_exp (emin + prec - 1 + 1) ≤ emin + prec - 1
        have hk2 : ¬ (emin + prec - 1 + 1) - prec < emin := by linarith
        have hfk' : FTZ_exp emin prec (emin + prec - 1 + 1) = (emin + prec - 1 + 1) - prec := by
          unfold FTZ_exp; rw [if_neg hk2]
        rw [hfk']; linarith
      · -- ∀ l ≤ emin + prec - 1, FTZ_exp l = emin + prec - 1
        intro l hl
        have hfl : FTZ_exp emin prec l = emin + prec - 1 := by
          unfold FTZ_exp
          rw [if_pos (by linarith : l - prec < emin)]
        rw [hfl]
    · -- emin ≤ k - prec, so FTZ_exp k = k - prec, h_ge : k ≤ k - prec → contradiction
      have hfk : FTZ_exp emin prec k = k - prec := by
        unfold FTZ_exp; rw [if_neg hk1]
      rw [hfk] at h_ge
      exfalso; linarith

/-- Every FTZ-format real is in the generic format with `FTZ_exp emin prec`. -/
theorem generic_format_FTZ (beta : radix) (emin prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : FTZ_format beta emin prec x) :
    generic_format beta (FTZ_exp emin prec) x := by
  obtain ⟨⟨xm, xe⟩, hx, hb, he⟩ := h
  rw [hx]
  apply generic_format_F2R beta (FTZ_exp emin prec) xm xe
  intro hxm_ne
  have h_F2R_ne : F2R (beta := beta) ⟨xm, xe⟩ ≠ 0 := by
    intro hz; exact hxm_ne (eq_0_F2R (beta := beta) hz)
  -- Reconstruct x ≠ 0 to access the bounds.
  have h_x_ne : x ≠ 0 := by
    intro hz; rw [hz] at hx; exact h_F2R_ne hx.symm
  obtain ⟨hb_lo, hb_hi⟩ := hb h_x_ne
  -- Lift integer bounds on |xm| to real bpow bounds.
  have hxm_lo_real : bpow beta (prec - 1) ≤ ((|xm| : ℤ) : ℝ) := by
    have h1 : ((beta.val ^ (prec - 1).toNat : ℤ) : ℝ) ≤ ((|xm| : ℤ) : ℝ) := by
      exact_mod_cast hb_lo
    rwa [IZR_Zpower beta (by linarith : (0 : ℤ) ≤ prec - 1)] at h1
  have hxm_hi_real : ((|xm| : ℤ) : ℝ) < bpow beta prec := by
    have h1 : ((|xm| : ℤ) : ℝ) < ((beta.val ^ prec.toNat : ℤ) : ℝ) := by
      exact_mod_cast hb_hi
    rwa [IZR_Zpower beta (le_of_lt hp)] at h1
  -- |F2R| = |xm| · β^xe.
  have h_abs_F2R : |F2R (beta := beta) ⟨xm, xe⟩| = ((|xm| : ℤ) : ℝ) * bpow beta xe := by
    unfold F2R
    show |(xm : ℝ) * bpow beta xe| = ((|xm| : ℤ) : ℝ) * bpow beta xe
    rw [abs_mul, abs_of_pos (bpow_gt_0 beta xe)]
    push_cast; rfl
  have h_F2R_lo : bpow beta (prec - 1 + xe) ≤ |F2R (beta := beta) ⟨xm, xe⟩| := by
    rw [h_abs_F2R, bpow_plus]
    exact mul_le_mul_of_nonneg_right hxm_lo_real (bpow_ge_0 _ _)
  have h_F2R_hi : |F2R (beta := beta) ⟨xm, xe⟩| < bpow beta (prec + xe) := by
    rw [h_abs_F2R, bpow_plus]
    exact mul_lt_mul_of_pos_right hxm_hi_real (bpow_gt_0 _ _)
  -- mag (F2R) = prec + xe via the bracketing.
  have h_mag : mag beta (F2R (beta := beta) ⟨xm, xe⟩) = prec + xe := by
    apply mag_unique beta
    · rw [show (prec + xe) - 1 = prec - 1 + xe from by ring]; exact h_F2R_lo
    · exact h_F2R_hi
  show cexp beta (FTZ_exp emin prec) (F2R (beta := beta) ⟨xm, xe⟩) ≤ xe
  unfold cexp
  rw [h_mag]
  unfold FTZ_exp
  rw [if_neg (by linarith : ¬ (prec + xe) - prec < emin)]
  linarith

/-- Every generic-format-with-`FTZ_exp` real is in the FTZ format. -/
theorem FTZ_format_generic (beta : radix) (emin prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : generic_format beta (FTZ_exp emin prec) x) :
    FTZ_format beta emin prec x := by
  by_cases hx0 : x = 0
  · -- x = 0: pick the canonical zero float ⟨0, emin⟩.
    refine ⟨⟨0, emin⟩, ?_, ?_, le_refl _⟩
    · rw [hx0]; exact (F2R_0 (beta := beta) emin).symm
    · intro hne; exact absurd hx0 hne
  · -- x ≠ 0
    set ex := mag beta x with hex_def
    have h_mag_lo : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta hx0
    have h_mag_hi : |x| < bpow beta ex := bpow_mag_gt beta x
    by_cases hex : ex - prec < emin
    · -- Subnormal regime: cexp = emin + prec - 1, contradicting the mag bounds.
      exfalso
      have h_cexp_eq : cexp beta (FTZ_exp emin prec) x = emin + prec - 1 := by
        unfold cexp FTZ_exp; rw [if_pos hex]
      set sm := scaled_mantissa beta (FTZ_exp emin prec) x with hsm_def
      set m := Ztrunc sm
      have h_x_eq : x = F2R (beta := beta) ⟨m, emin + prec - 1⟩ := by
        have hh := h
        unfold generic_format at hh
        rw [h_cexp_eq] at hh
        exact hh
      have h_m_ne : m ≠ 0 := by
        intro hzero
        apply hx0
        rw [h_x_eq, hzero]; exact F2R_0 _
      have h_abs_m_ge_1 : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by
        have h_pos : 0 < |m| := abs_pos.mpr h_m_ne
        have h1 : 1 ≤ |m| := by omega
        exact_mod_cast h1
      have h_x_abs_lo : bpow beta (emin + prec - 1) ≤ |x| := by
        rw [h_x_eq]
        unfold F2R
        show bpow beta (emin + prec - 1) ≤ |(m : ℝ) * bpow beta (emin + prec - 1)|
        rw [abs_mul, abs_of_pos (bpow_gt_0 _ _)]
        calc bpow beta (emin + prec - 1)
            = 1 * bpow beta (emin + prec - 1) := by ring
          _ ≤ ((|m| : ℤ) : ℝ) * bpow beta (emin + prec - 1) :=
              mul_le_mul_of_nonneg_right h_abs_m_ge_1 (bpow_ge_0 _ _)
          _ = |((m : ℤ) : ℝ)| * bpow beta (emin + prec - 1) := by push_cast; rfl
      have h_ex_le : ex ≤ emin + prec - 1 := by linarith
      have h_pow_le : bpow beta ex ≤ bpow beta (emin + prec - 1) := bpow_le beta h_ex_le
      linarith
    · -- Normal regime: cexp = ex - prec; build the FTZ float.
      push_neg at hex
      have h_cexp_eq : cexp beta (FTZ_exp emin prec) x = ex - prec := by
        unfold cexp FTZ_exp; rw [if_neg (not_lt.mpr hex)]
      set sm := scaled_mantissa beta (FTZ_exp emin prec) x with hsm_def
      set m := Ztrunc sm with hm_def
      have h_x_eq : x = F2R (beta := beta) ⟨m, ex - prec⟩ := by
        have hh := h
        unfold generic_format at hh
        rw [h_cexp_eq] at hh
        exact hh
      refine ⟨⟨m, ex - prec⟩, h_x_eq, ?_, hex⟩
      intro _
      -- |sm| ∈ [bpow(prec-1), bpow prec), then translate to integer bounds on m.
      have h_sm_lo : bpow beta (prec - 1) ≤ |sm| := by
        rw [hsm_def]
        unfold scaled_mantissa
        rw [h_cexp_eq, abs_mul, abs_of_pos (bpow_gt_0 _ _)]
        calc bpow beta (prec - 1)
            = bpow beta (ex - 1) * bpow beta (-(ex - prec)) := by
              rw [← bpow_plus]; congr 1; ring
          _ ≤ |x| * bpow beta (-(ex - prec)) :=
              mul_le_mul_of_nonneg_right h_mag_lo (bpow_ge_0 _ _)
      have h_sm_hi : |sm| < bpow beta prec := by
        rw [hsm_def]
        unfold scaled_mantissa
        rw [h_cexp_eq, abs_mul, abs_of_pos (bpow_gt_0 _ _)]
        calc |x| * bpow beta (-(ex - prec))
            < bpow beta ex * bpow beta (-(ex - prec)) :=
              mul_lt_mul_of_pos_right h_mag_hi (bpow_gt_0 _ _)
          _ = bpow beta prec := by rw [← bpow_plus]; congr 1; ring
      -- Identify m as sm via scaled_mantissa_generic.
      have h_m_real : ((m : ℤ) : ℝ) = sm := by
        rw [hm_def, hsm_def]
        have := scaled_mantissa_generic beta (FTZ_exp emin prec) h
        rw [← hsm_def] at this
        exact this.symm
      have h_abs_m_real_lo : bpow beta (prec - 1) ≤ ((|m| : ℤ) : ℝ) := by
        rw [show ((|m| : ℤ) : ℝ) = |((m : ℤ) : ℝ)| from by push_cast; rfl, h_m_real]
        exact h_sm_lo
      have h_abs_m_real_hi : ((|m| : ℤ) : ℝ) < bpow beta prec := by
        rw [show ((|m| : ℤ) : ℝ) = |((m : ℤ) : ℝ)| from by push_cast; rfl, h_m_real]
        exact h_sm_hi
      refine ⟨?_, ?_⟩
      · -- (beta^(prec-1) : ℤ) ≤ |m|
        have hpow_eq : bpow beta (prec - 1)
            = ((beta.val ^ (prec - 1).toNat : ℤ) : ℝ) :=
          (IZR_Zpower beta (by linarith : (0 : ℤ) ≤ prec - 1)).symm
        rw [hpow_eq] at h_abs_m_real_lo
        exact_mod_cast h_abs_m_real_lo
      · -- |m| < (beta^prec : ℤ)
        have hpow_eq : bpow beta prec = ((beta.val ^ prec.toNat : ℤ) : ℝ) :=
          (IZR_Zpower beta (le_of_lt hp)).symm
        rw [hpow_eq] at h_abs_m_real_hi
        exact_mod_cast h_abs_m_real_hi

/-- The FTZ format admits all the abstract round predicates from `Round_pred`. -/
theorem FTZ_format_satisfies_any (beta : radix) (emin prec : ℤ) (hp : 0 < prec) :
    satisfies_any (FTZ_format beta emin prec) := by
  refine satisfies_any_eq (F1 := generic_format beta (FTZ_exp emin prec)) ?_
    (generic_format_satisfies_any beta (FTZ_exp emin prec)
      (FTZ_exp_valid emin prec hp))
  intro x
  exact ⟨FTZ_format_generic beta emin prec hp,
         generic_format_FTZ beta emin prec hp⟩

/-! ### FTZ rounding mode (rounds to 0 below the threshold) -/

/-- The FTZ-style rounding function: rounds normally for `1 ≤ |x|`, else `0`. -/
noncomputable def Zrnd_FTZ (rnd : ℝ → ℤ) (x : ℝ) : ℤ :=
  if 1 ≤ |x| then rnd x else 0

/-- `Zrnd_FTZ rnd` is a valid rounding when `rnd` is. -/
instance valid_rnd_FTZ (rnd : ℝ → ℤ) [hv : Valid_rnd rnd] : Valid_rnd (Zrnd_FTZ rnd) where
  Zrnd_le := by
    intro x y hxy
    unfold Zrnd_FTZ
    by_cases hx : 1 ≤ |x|
    · by_cases hy : 1 ≤ |y|
      · rw [if_pos hx, if_pos hy]; exact hv.Zrnd_le x y hxy
      · -- |x| ≥ 1, |y| < 1: x ≤ y forces x ≤ -1, hence rnd x ≤ -1 ≤ 0.
        rw [if_pos hx, if_neg hy]
        push_neg at hy
        have h_y_lt : y < 1 := (abs_lt.mp hy).2
        rcases le_abs.mp hx with h_xge1 | h_xlen1
        · linarith
        · have h_le : rnd x ≤ rnd ((-1 : ℤ) : ℝ) :=
            hv.Zrnd_le x ((-1 : ℤ) : ℝ) (by push_cast; linarith)
          rw [hv.Zrnd_intCast (-1)] at h_le
          linarith
    · by_cases hy : 1 ≤ |y|
      · -- |x| < 1, |y| ≥ 1: 1 ≤ y, hence rnd y ≥ 1 ≥ 0.
        rw [if_neg hx, if_pos hy]
        push_neg at hx
        have h_x_lo : -1 < x := (abs_lt.mp hx).1
        rcases le_abs.mp hy with h_yge1 | h_ylen1
        · have h_ge : rnd ((1 : ℤ) : ℝ) ≤ rnd y :=
            hv.Zrnd_le ((1 : ℤ) : ℝ) y (by push_cast; linarith)
          rw [hv.Zrnd_intCast 1] at h_ge
          linarith
        · linarith
      · rw [if_neg hx, if_neg hy]
  Zrnd_intCast := by
    intro n
    unfold Zrnd_FTZ
    by_cases hn : 1 ≤ |((n : ℤ) : ℝ)|
    · rw [if_pos hn]; exact hv.Zrnd_intCast n
    · rw [if_neg hn]
      push_neg at hn
      have h_int : |n| < 1 := by
        have h1 : ((|n| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
          rw [show ((|n| : ℤ) : ℝ) = |((n : ℤ) : ℝ)| from by push_cast; rfl]
          push_cast; exact hn
        exact_mod_cast h1
      have h_n_zero : n = 0 := by
        rcases lt_trichotomy n 0 with hn | hn | hn
        · rw [abs_of_neg hn] at h_int; omega
        · exact hn
        · rw [abs_of_pos hn] at h_int; omega
      rw [h_n_zero]

/-- Above the FTZ threshold, FTZ rounding agrees with FLX rounding. -/
theorem round_FTZ_FLX (beta : radix) (emin prec : ℤ) (hp : 0 < prec)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ}
    (hx : bpow beta (emin + prec - 1) ≤ |x|) :
    round beta (FTZ_exp emin prec) (Zrnd_FTZ rnd) x
      = round beta (FLX_exp prec) rnd x := by
  have hx0 : x ≠ 0 := by
    intro hz; rw [hz, abs_zero] at hx
    exact absurd hx (not_le.mpr (bpow_gt_0 _ _))
  have h_mag_gt : emin + prec - 1 < mag beta x := mag_gt_bpow beta hx
  set ex := mag beta x with hex_def
  -- FTZ_exp ex = ex - prec = FLX_exp prec ex
  have h_FTZ_FLX_eq : FTZ_exp emin prec ex = FLX_exp prec ex := by
    unfold FTZ_exp FLX_exp
    rw [if_neg (by linarith : ¬ ex - prec < emin)]
  have h_cexp_eq : cexp beta (FTZ_exp emin prec) x = cexp beta (FLX_exp prec) x := by
    unfold cexp; rw [h_FTZ_FLX_eq]
  have h_sm_eq : scaled_mantissa beta (FTZ_exp emin prec) x
      = scaled_mantissa beta (FLX_exp prec) x := by
    unfold scaled_mantissa; rw [h_cexp_eq]
  -- |sm_FLX| ≥ 1, so Zrnd_FTZ doesn't activate the flush.
  have h_sm_abs_ge_1 : 1 ≤ |scaled_mantissa beta (FLX_exp prec) x| := by
    unfold scaled_mantissa
    rw [abs_mul, abs_of_pos (bpow_gt_0 _ _)]
    have h_cexp_FLX : cexp beta (FLX_exp prec) x = ex - prec := by
      unfold cexp FLX_exp; rfl
    rw [h_cexp_FLX]
    have h_x_lo : bpow beta (ex - 1) ≤ |x| := bpow_mag_le beta hx0
    calc (1 : ℝ) = bpow beta 0 := (bpow_zero beta).symm
      _ ≤ bpow beta (prec - 1) := bpow_le beta (by linarith)
      _ = bpow beta (ex - 1) * bpow beta (-(ex - prec)) := by
          rw [← bpow_plus]; congr 1; ring
      _ ≤ |x| * bpow beta (-(ex - prec)) :=
          mul_le_mul_of_nonneg_right h_x_lo (bpow_ge_0 _ _)
  unfold round
  rw [h_cexp_eq, h_sm_eq]
  apply F2R_eq
  unfold Zrnd_FTZ
  rw [if_pos h_sm_abs_ge_1]

/-- Below the FTZ threshold, FTZ rounding always returns 0. -/
theorem round_FTZ_small (beta : radix) (emin prec : ℤ)
    (rnd : ℝ → ℤ) [Valid_rnd rnd] {x : ℝ}
    (hx : |x| < bpow beta (emin + prec - 1)) :
    round beta (FTZ_exp emin prec) (Zrnd_FTZ rnd) x = 0 := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact round_0 beta _ _
  · set ex := mag beta x with hex_def
    have h_mag_le : ex ≤ emin + prec - 1 := mag_le_bpow beta hx0 hx
    have h_small : ex - prec < emin := by linarith
    have h_cexp : cexp beta (FTZ_exp emin prec) x = emin + prec - 1 := by
      unfold cexp FTZ_exp; rw [if_pos h_small]
    have h_sm_lt_1 : |scaled_mantissa beta (FTZ_exp emin prec) x| < 1 := by
      unfold scaled_mantissa
      rw [h_cexp, abs_mul, abs_of_pos (bpow_gt_0 _ _)]
      calc |x| * bpow beta (-(emin + prec - 1))
          < bpow beta (emin + prec - 1) * bpow beta (-(emin + prec - 1)) :=
            mul_lt_mul_of_pos_right hx (bpow_gt_0 _ _)
        _ = bpow beta 0 := by rw [← bpow_plus]; congr 1; ring
        _ = 1 := bpow_zero beta
    have h_zr : Zrnd_FTZ rnd (scaled_mantissa beta (FTZ_exp emin prec) x) = 0 := by
      unfold Zrnd_FTZ; rw [if_neg (not_le.mpr h_sm_lt_1)]
    unfold round
    rw [h_zr]
    exact F2R_0 _

end LeanFlocq
