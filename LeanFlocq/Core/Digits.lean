/-
Port of relevant content from `flocq/src/Core/Digits.v`
(Sylvie Boldo, Guillaume Melquiond, LGPL).

Provides `Zdigits` — the number of base-β digits of an integer — as the
`mag` of its real cast. This makes the bridge `Zdigits_mag` definitional.
-/

import LeanFlocq.Core.Raux

namespace LeanFlocq

/-- The number of digits of an integer `n` in base `β`. Defined as the `mag`
of `n` viewed as a real, so `Zdigits β 0 = 0` and for `n ≠ 0` we get the
unique `d` with `β^(d-1) ≤ |n| < β^d`. -/
noncomputable def Zdigits (beta : radix) (n : ℤ) : ℤ :=
  mag beta (n : ℝ)

@[simp] theorem Zdigits_zero (beta : radix) : Zdigits beta 0 = 0 := by
  unfold Zdigits; push_cast; exact mag_zero beta

theorem Zdigits_neg (beta : radix) (n : ℤ) :
    Zdigits beta (-n) = Zdigits beta n := by
  unfold Zdigits
  rw [show ((-n : ℤ) : ℝ) = -(n : ℝ) from by push_cast; ring]
  exact mag_opp beta (n : ℝ)

theorem Zdigits_abs (beta : radix) (n : ℤ) :
    Zdigits beta |n| = Zdigits beta n := by
  unfold Zdigits
  rw [show ((|n| : ℤ) : ℝ) = |(n : ℝ)| from by push_cast; rfl]
  exact mag_abs beta (n : ℝ)

/-- The defining property: `β^(Zdigits n - 1) ≤ |n| < β^(Zdigits n)` for `n ≠ 0`. -/
theorem Zdigits_correct (beta : radix) {n : ℤ} (hn : n ≠ 0) :
    bpow beta (Zdigits beta n - 1) ≤ |(n : ℝ)| ∧
      |(n : ℝ)| < bpow beta (Zdigits beta n) := by
  have h_n_real_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · exact bpow_mag_le beta h_n_real_ne
  · exact bpow_mag_gt beta (n : ℝ)

/-- Uniqueness: any `d` satisfying the bounds equals `Zdigits n`. -/
theorem Zdigits_unique (beta : radix) {n : ℤ} {d : ℤ}
    (h_low : bpow beta (d - 1) ≤ |(n : ℝ)|)
    (h_high : |(n : ℝ)| < bpow beta d) :
    Zdigits beta n = d := by
  unfold Zdigits
  exact mag_unique beta h_low h_high

theorem Zdigits_gt_0 (beta : radix) {n : ℤ} (hn : n ≠ 0) :
    0 < Zdigits beta n := by
  have ⟨h_lo, _⟩ := Zdigits_correct beta hn
  by_contra h_le
  push_neg at h_le
  have h_n_pos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  -- bpow(d-1) ≤ |n| with d ≤ 0 means bpow(d-1) ≤ |n|, but d-1 ≤ -1 means bpow(d-1) ≤ bpow(-1) = 1/β.
  -- Hmm we need 0 < bpow(d-1) ≤ |n| but also |n| < bpow d ≤ bpow 0 = 1, so |n| < 1.
  -- |n| ≥ 1 (since n is a nonzero integer): contradiction.
  have ⟨_, h_hi⟩ := Zdigits_correct beta hn
  have h_n_ge_1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have h_d_le_0 : Zdigits beta n ≤ 0 := h_le
  have h_bpow_d : bpow beta (Zdigits beta n) ≤ bpow beta 0 := bpow_le beta h_d_le_0
  rw [bpow_zero] at h_bpow_d
  linarith

theorem Zdigits_ge_0 (beta : radix) (n : ℤ) : 0 ≤ Zdigits beta n := by
  by_cases hn : n = 0
  · rw [hn, Zdigits_zero]
  · exact le_of_lt (Zdigits_gt_0 beta hn)

/-- If `|n| < β^k` (with `k ≥ 0`), then `Zdigits β n ≤ k`. -/
theorem Zdigits_le_Zpower (beta : radix) {n k : ℤ} (Hk : 0 ≤ k)
    (Hn : |n| < (beta.val : ℤ) ^ k.toNat) : Zdigits beta n ≤ k := by
  by_cases hn : n = 0
  · rw [hn, Zdigits_zero]; exact Hk
  · -- Use mag_le_bpow: |n| < bpow β k → mag n ≤ k.
    unfold Zdigits
    apply mag_le_bpow beta (by exact_mod_cast hn : (n : ℝ) ≠ 0)
    rw [show ((n : ℝ)) = ((n : ℤ) : ℝ) from rfl]
    rw [show |((n : ℤ) : ℝ)| = ((|n| : ℤ) : ℝ) from by push_cast; rfl]
    rw [← IZR_Zpower beta Hk]
    exact_mod_cast Hn

/-- `Zdigits (m / β^e) = Zdigits m - e` for `0 ≤ m` and `0 ≤ e ≤ Zdigits m`. -/
theorem Zdigits_div_Zpower (beta : radix) {m e : ℤ}
    (Hm : 0 ≤ m) (He : 0 ≤ e ∧ e ≤ Zdigits beta m) :
    Zdigits beta (m / (beta.val : ℤ) ^ e.toNat) = Zdigits beta m - e := by
  obtain ⟨He0, He1⟩ := He
  set d := Zdigits beta m with hd_def
  have hβ_pos : 0 < (beta.val : ℤ) := by
    have := beta.prop; omega
  have hpow_pos : 0 < (beta.val : ℤ) ^ e.toNat := pow_pos hβ_pos _
  by_cases hm0 : m = 0
  · -- m = 0: Zdigits 0 = 0, e = 0 (forced by e ≤ 0).
    have hd_zero : d = 0 := by rw [hd_def, hm0, Zdigits_zero]
    have he_zero : e = 0 := by omega
    have h_div_zero : (0 : ℤ) / (beta.val : ℤ) ^ e.toNat = 0 :=
      Int.zero_ediv _
    rw [hm0, h_div_zero, Zdigits_zero, hd_zero, he_zero]; rfl
  -- m > 0, so d ≥ 1.
  have hm_pos : 0 < m := lt_of_le_of_ne Hm (Ne.symm hm0)
  have hd_pos : 0 < d := Zdigits_gt_0 beta hm0
  have h_low : bpow beta (d - 1) ≤ |(m : ℝ)| := bpow_mag_le beta (by exact_mod_cast hm0 : (m : ℝ) ≠ 0)
  have h_high : |(m : ℝ)| < bpow beta d := bpow_mag_gt beta (m : ℝ)
  have h_m_abs : |(m : ℝ)| = (m : ℝ) := abs_of_nonneg (by exact_mod_cast Hm)
  rw [h_m_abs] at h_low h_high
  -- bpow β k = ((β^k : ℤ) : ℝ) for k ≥ 0.
  have h_bpow_d : bpow beta d = ((beta.val ^ d.toNat : ℤ) : ℝ) := (IZR_Zpower beta (le_of_lt hd_pos)).symm
  have h_bpow_dm1 : bpow beta (d - 1) = ((beta.val ^ (d - 1).toNat : ℤ) : ℝ) :=
    (IZR_Zpower beta (by omega)).symm
  -- The case e = d: m / β^d = 0.
  by_cases hed : e = d
  · subst hed
    have h_m_lt : m < (beta.val : ℤ) ^ d.toNat := by
      rw [h_bpow_d] at h_high
      exact_mod_cast h_high
    have h_div_zero : m / (beta.val : ℤ) ^ d.toNat = 0 :=
      Int.ediv_eq_zero_of_lt Hm h_m_lt
    rw [h_div_zero, Zdigits_zero]; ring
  -- The case e < d.
  have he_lt_d : e < d := lt_of_le_of_ne He1 hed
  -- Set q := m / β^e. Need to show Zdigits q = d - e.
  set q := m / (beta.val : ℤ) ^ e.toNat with hq_def
  have hq_nn : 0 ≤ q := Int.ediv_nonneg Hm (le_of_lt hpow_pos)
  -- Upper bound: q < β^(d - e), since q * β^e ≤ m < β^d.
  have h_q_lt : q < (beta.val : ℤ) ^ (d - e).toNat := by
    have h_m_lt : m < (beta.val : ℤ) ^ d.toNat := by
      rw [h_bpow_d] at h_high
      exact_mod_cast h_high
    -- q * β^e ≤ m < β^d, so q ≤ (m - 1) / β^e... actually simpler:
    -- if q ≥ β^(d - e), then q * β^e ≥ β^(d - e) * β^e = β^d > m, contradicting q * β^e ≤ m.
    by_contra h_not
    push_neg at h_not
    have h_q_mul : q * (beta.val : ℤ) ^ e.toNat ≤ m := Int.ediv_mul_le m (ne_of_gt hpow_pos)
    have h_pow_split : (beta.val : ℤ) ^ d.toNat
        = (beta.val : ℤ) ^ (d - e).toNat * (beta.val : ℤ) ^ e.toNat := by
      rw [← pow_add]
      congr 1
      omega
    have h_qe_ge : (beta.val : ℤ) ^ d.toNat
        ≤ q * (beta.val : ℤ) ^ e.toNat := by
      rw [h_pow_split]
      exact mul_le_mul_of_nonneg_right h_not (le_of_lt hpow_pos)
    linarith
  -- Lower bound: β^(d - e - 1) ≤ q, since m ≥ β^(d-1) and β^(d-1) = β^(d-e-1) * β^e.
  have h_q_ge : (beta.val : ℤ) ^ (d - e - 1).toNat ≤ q := by
    have h_m_ge_int : (beta.val : ℤ) ^ (d - 1).toNat ≤ m := by
      rw [h_bpow_dm1] at h_low
      exact_mod_cast h_low
    -- β^(d-1) = β^(d-e-1) * β^e (when d - 1 - e ≥ 0).
    have h_pow_split : (beta.val : ℤ) ^ (d - 1).toNat
        = (beta.val : ℤ) ^ (d - e - 1).toNat * (beta.val : ℤ) ^ e.toNat := by
      rw [← pow_add]
      congr 1
      omega
    -- q := m / β^e ≥ β^(d - 1) / β^e = β^(d - e - 1) * β^e / β^e = β^(d - e - 1).
    rw [h_pow_split] at h_m_ge_int
    have h_step : (beta.val : ℤ) ^ (d - e - 1).toNat * (beta.val : ℤ) ^ e.toNat
                  ≤ q * (beta.val : ℤ) ^ e.toNat + (m % (beta.val : ℤ) ^ e.toNat) := by
      have h_div_mod_eq : m = q * (beta.val : ℤ) ^ e.toNat + m % (beta.val : ℤ) ^ e.toNat := by
        rw [hq_def, mul_comm, Int.ediv_add_emod]
      linarith
    have h_mod_lt : m % (beta.val : ℤ) ^ e.toNat < (beta.val : ℤ) ^ e.toNat :=
      Int.emod_lt_of_pos _ hpow_pos
    by_contra h_not
    push_neg at h_not
    -- q < β^(d-e-1), so q ≤ β^(d-e-1) - 1, so q * β^e ≤ (β^(d-e-1) - 1) * β^e = β^(d-1) - β^e.
    -- m = q*β^e + mod < β^(d-1) - β^e + β^e = β^(d-1). Contradicts m ≥ β^(d-1).
    have h_q_le : q ≤ (beta.val : ℤ) ^ (d - e - 1).toNat - 1 := by linarith
    have h_q_mul_le : q * (beta.val : ℤ) ^ e.toNat
                ≤ ((beta.val : ℤ) ^ (d - e - 1).toNat - 1) * (beta.val : ℤ) ^ e.toNat :=
      mul_le_mul_of_nonneg_right h_q_le (le_of_lt hpow_pos)
    have h_distrib : ((beta.val : ℤ) ^ (d - e - 1).toNat - 1) * (beta.val : ℤ) ^ e.toNat
        = (beta.val : ℤ) ^ (d - e - 1).toNat * (beta.val : ℤ) ^ e.toNat
          - (beta.val : ℤ) ^ e.toNat := by ring
    rw [h_distrib] at h_q_mul_le
    have h_div_mod_eq : m = q * (beta.val : ℤ) ^ e.toNat + m % (beta.val : ℤ) ^ e.toNat := by
      rw [hq_def, mul_comm, Int.ediv_add_emod]
    linarith
  -- Now apply Zdigits_unique.
  apply Zdigits_unique
  · -- bpow (d - e - 1) ≤ |(q : ℝ)|.
    rw [abs_of_nonneg (by exact_mod_cast hq_nn : (0 : ℝ) ≤ (q : ℝ))]
    show bpow beta (d - e - 1) ≤ (q : ℝ)
    have h_eq : bpow beta (d - e - 1) = ((beta.val ^ (d - e - 1).toNat : ℤ) : ℝ) :=
      (IZR_Zpower beta (by omega)).symm
    rw [h_eq]; exact_mod_cast h_q_ge
  · -- |(q : ℝ)| < bpow (d - e).
    rw [abs_of_nonneg (by exact_mod_cast hq_nn : (0 : ℝ) ≤ (q : ℝ))]
    show (q : ℝ) < bpow beta (d - e)
    have h_eq : bpow beta (d - e) = ((beta.val ^ (d - e).toNat : ℤ) : ℝ) :=
      (IZR_Zpower beta (by omega)).symm
    rw [h_eq]; exact_mod_cast h_q_lt

end LeanFlocq
