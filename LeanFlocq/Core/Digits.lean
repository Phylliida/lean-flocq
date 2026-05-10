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

end LeanFlocq
