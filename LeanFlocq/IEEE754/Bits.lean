/-
Lean port of Coq Flocq's `IEEE754/Bits.v` — bit-level encoding/decoding
of IEEE 754 binary floats.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.

Initial port: `join_bits`, `split_bits`, and `join_bits_range`. The full
round-trip theorems and the `bits_of_binary_float` family are deferred.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Binary

namespace LeanFlocq

/-! ### Bit-level encoding

`join_bits s m e` packs a sign bit, a `mw`-bit mantissa, and an `ew`-bit
exponent into a single integer:
  `(s ? 2^ew : 0 + e) << mw + m`
-/

/-- Pack `(sign, mantissa, exponent)` into an integer. -/
def join_bits (mw ew : ℤ) (s : Bool) (m e : ℤ) : ℤ :=
  ((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat + m

/-- Unpack an integer into `(sign, mantissa, exponent)`. -/
def split_bits (mw ew : ℤ) (x : ℤ) : Bool × ℤ × ℤ :=
  let mm : ℤ := (2 : ℤ) ^ mw.toNat
  let em : ℤ := (2 : ℤ) ^ ew.toNat
  (decide (mm * em ≤ x), x % mm, (x / mm) % em)

/-- The packed integer fits in `mw + ew + 1` bits. -/
theorem join_bits_range (mw ew : ℤ) (Hmw : 0 ≤ mw) (Hew : 0 ≤ ew)
    (s : Bool) (m e : ℤ)
    (Hm : 0 ≤ m ∧ m < (2 : ℤ) ^ mw.toNat)
    (He : 0 ≤ e ∧ e < (2 : ℤ) ^ ew.toNat) :
    0 ≤ join_bits mw ew s m e ∧
    join_bits mw ew s m e < (2 : ℤ) ^ (mw + ew + 1).toNat := by
  obtain ⟨Hm0, Hm1⟩ := Hm
  obtain ⟨He0, He1⟩ := He
  have hmw_nn : (0 : ℤ) ≤ (2 : ℤ) ^ mw.toNat := pow_nonneg (by norm_num) _
  have hew_nn : (0 : ℤ) ≤ (2 : ℤ) ^ ew.toNat := pow_nonneg (by norm_num) _
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  refine ⟨?_, ?_⟩
  · -- 0 ≤ join_bits.
    unfold join_bits
    have h_first_nn : 0 ≤ (if s then (2 : ℤ) ^ ew.toNat else 0) + e := by
      cases s with
      | false => simp; exact He0
      | true => simp; linarith
    have : 0 ≤ ((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat :=
      mul_nonneg h_first_nn hmw_nn
    linarith
  · -- join_bits < 2^(mw+ew+1).
    unfold join_bits
    have h_first_lt : (if s then (2 : ℤ) ^ ew.toNat else 0) + e + 1
        ≤ (2 : ℤ) ^ ew.toNat + (2 : ℤ) ^ ew.toNat := by
      cases s with
      | false => simp; linarith
      | true => simp; linarith
    have h_pow_split : (2 : ℤ) ^ (mw + ew + 1).toNat
        = ((2 : ℤ) ^ ew.toNat + (2 : ℤ) ^ ew.toNat) * (2 : ℤ) ^ mw.toNat := by
      have h_pos : 0 ≤ mw + ew + 1 := by linarith
      have h_pos' : 0 ≤ ew + 1 := by linarith
      have h_eq : (mw + ew + 1).toNat = ew.toNat + 1 + mw.toNat := by
        have h1 : mw + ew + 1 = (ew + 1) + mw := by ring
        rw [h1, Int.toNat_add h_pos' Hmw]
        congr 1
        rw [show ew + 1 = ew + 1 from rfl]
        rw [Int.toNat_add Hew (by norm_num : (0 : ℤ) ≤ 1)]
        rfl
      rw [h_eq]
      rw [show ew.toNat + 1 + mw.toNat = (ew.toNat + 1) + mw.toNat from rfl]
      rw [pow_add, pow_succ]
      ring
    rw [h_pow_split]
    have h_upper : ((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat + m
        < (((if s then (2 : ℤ) ^ ew.toNat else 0) + e) + 1) * (2 : ℤ) ^ mw.toNat := by
      nlinarith
    have h_step :
        (((if s then (2 : ℤ) ^ ew.toNat else 0) + e) + 1) * (2 : ℤ) ^ mw.toNat
          ≤ ((2 : ℤ) ^ ew.toNat + (2 : ℤ) ^ ew.toNat) * (2 : ℤ) ^ mw.toNat :=
      mul_le_mul_of_nonneg_right h_first_lt hmw_nn
    linarith

/-- Splitting a packed value recovers `(s, m, e)`. -/
theorem split_join_bits (mw ew : ℤ) (Hmw : 0 ≤ mw) (Hew : 0 ≤ ew)
    (s : Bool) (m e : ℤ)
    (Hm : 0 ≤ m ∧ m < (2 : ℤ) ^ mw.toNat)
    (He : 0 ≤ e ∧ e < (2 : ℤ) ^ ew.toNat) :
    split_bits mw ew (join_bits mw ew s m e) = (s, m, e) := by
  obtain ⟨Hm0, Hm1⟩ := Hm
  obtain ⟨He0, He1⟩ := He
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  have hew_pos : 0 < (2 : ℤ) ^ ew.toNat := pow_pos (by norm_num) _
  have hmw_ne : (2 : ℤ) ^ mw.toNat ≠ 0 := ne_of_gt hmw_pos
  -- Compute each component.
  -- v := join_bits mw ew s m e
  -- v % 2^mw = m (since m < 2^mw and 2^mw * stuff vanishes mod 2^mw).
  have h_mod : (join_bits mw ew s m e) % (2 : ℤ) ^ mw.toNat = m := by
    unfold join_bits
    -- Reorder to (m + ((if ...) + e) * 2^mw), then add_mul_emod_self_right.
    rw [show (((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat + m)
          = m + ((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat from by ring]
    rw [Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt Hm0 Hm1
  -- v / 2^mw = (if s then 2^ew else 0) + e (m/2^mw = 0 since m < 2^mw).
  have h_div : (join_bits mw ew s m e) / (2 : ℤ) ^ mw.toNat
              = (if s then (2 : ℤ) ^ ew.toNat else 0) + e := by
    unfold join_bits
    rw [show (((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat + m)
          = m + ((if s then (2 : ℤ) ^ ew.toNat else 0) + e) * (2 : ℤ) ^ mw.toNat from by ring]
    rw [Int.add_mul_ediv_right _ _ hmw_ne]
    rw [Int.ediv_eq_zero_of_lt Hm0 Hm1, zero_add]
  -- The mod-2^ew of the divided value gives e.
  have h_div_mod : ((join_bits mw ew s m e) / (2 : ℤ) ^ mw.toNat) % (2 : ℤ) ^ ew.toNat = e := by
    rw [h_div]
    cases s with
    | false =>
      simp only [Bool.false_eq_true, if_false, zero_add]
      exact Int.emod_eq_of_lt He0 He1
    | true =>
      simp only [if_true]
      -- (2^ew + e) % 2^ew = e. Rewrite as (e + 2^ew * 1) % 2^ew, use add_mul_emod_self_left.
      rw [show (2 : ℤ) ^ ew.toNat + e = e + (2 : ℤ) ^ ew.toNat * 1 from by ring]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt He0 He1
  -- The decide gives s.
  have h_dec : decide ((2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat ≤ join_bits mw ew s m e) = s := by
    cases s with
    | false =>
      rw [decide_eq_false_iff_not]; push_neg
      unfold join_bits
      simp only [Bool.false_eq_true, if_false, zero_add]
      -- 2^mw * 2^ew > e * 2^mw + m (since e < 2^ew and m < 2^mw)
      nlinarith
    | true =>
      rw [decide_eq_true_iff]
      unfold join_bits
      simp only [if_true]
      -- 2^mw * 2^ew ≤ (2^ew + e) * 2^mw + m, since e ≥ 0 and m ≥ 0 and mul_comm.
      nlinarith
  -- Assemble.
  unfold split_bits
  show (decide ((2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat ≤ join_bits mw ew s m e),
        (join_bits mw ew s m e) % (2 : ℤ) ^ mw.toNat,
        ((join_bits mw ew s m e) / (2 : ℤ) ^ mw.toNat) % (2 : ℤ) ^ ew.toNat) = (s, m, e)
  rw [h_dec, h_mod, h_div_mod]

/-- Packing a split value recovers the original integer (in range). -/
theorem join_split_bits (mw ew : ℤ) (Hmw : 0 ≤ mw) (Hew : 0 ≤ ew) (x : ℤ)
    (Hx : 0 ≤ x ∧ x < (2 : ℤ) ^ (mw + ew + 1).toNat) :
    let p := split_bits mw ew x
    join_bits mw ew p.1 p.2.1 p.2.2 = x := by
  obtain ⟨Hx0, Hx1⟩ := Hx
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  have hew_pos : 0 < (2 : ℤ) ^ ew.toNat := pow_pos (by norm_num) _
  have hmw_ne : (2 : ℤ) ^ mw.toNat ≠ 0 := ne_of_gt hmw_pos
  have hew_ne : (2 : ℤ) ^ ew.toNat ≠ 0 := ne_of_gt hew_pos
  -- Bound on x in terms of 2^mw * 2^ew * 2.
  have h_pow_eq : (2 : ℤ) ^ (mw + ew + 1).toNat
                = (2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat * 2 := by
    have h_eq : (mw + ew + 1).toNat = mw.toNat + ew.toNat + 1 := by omega
    rw [h_eq, pow_succ, pow_add]
  have Hx1' : x < (2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat * 2 := by
    rw [← h_pow_eq]; exact Hx1
  -- Let q = x / 2^mw, r = x % 2^mw. Then x = q * 2^mw + r.
  set q := x / (2 : ℤ) ^ mw.toNat with hq_def
  set r := x % (2 : ℤ) ^ mw.toNat with hr_def
  have h_x_eq : x = q * (2 : ℤ) ^ mw.toNat + r := by
    rw [hq_def, hr_def]
    have h := Int.ediv_add_emod x ((2 : ℤ) ^ mw.toNat)
    linarith [mul_comm ((2 : ℤ) ^ mw.toNat) (x / (2 : ℤ) ^ mw.toNat)]
  have h_r_lt : r < (2 : ℤ) ^ mw.toNat := Int.emod_lt_of_pos x hmw_pos
  have h_r_nn : 0 ≤ r := Int.emod_nonneg x hmw_ne
  have h_q_nn : 0 ≤ q := Int.ediv_nonneg Hx0 (le_of_lt hmw_pos)
  -- q < 2^ew * 2 (from x < 2^mw * 2^ew * 2 and r ≥ 0).
  have h_q_lt : q < (2 : ℤ) ^ ew.toNat * 2 := by
    have : x < (2 : ℤ) ^ mw.toNat * ((2 : ℤ) ^ ew.toNat * 2) := by
      rw [← mul_assoc]; exact Hx1'
    have h_q_lt_strict : q * (2 : ℤ) ^ mw.toNat
                  < ((2 : ℤ) ^ ew.toNat * 2) * (2 : ℤ) ^ mw.toNat := by
      rw [mul_comm ((2 : ℤ) ^ ew.toNat * 2) ((2 : ℤ) ^ mw.toNat)]
      linarith
    have := (mul_lt_mul_right hmw_pos).mp h_q_lt_strict
    exact this
  -- Split on whether x ≥ 2^mw * 2^ew (i.e., q ≥ 2^ew).
  show join_bits mw ew _ _ _ = x
  unfold split_bits
  simp only
  -- The triple from split_bits is (decide(2^mw * 2^ew ≤ x), x % 2^mw, (x / 2^mw) % 2^ew)
  -- = (decide(2^mw * 2^ew ≤ x), r, q % 2^ew).
  rw [show x / (2 : ℤ) ^ mw.toNat = q from rfl]
  rw [show x % (2 : ℤ) ^ mw.toNat = r from rfl]
  unfold join_bits
  by_cases h_branch : (2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat ≤ x
  · -- s = true: q ≥ 2^ew, q % 2^ew = q - 2^ew.
    rw [decide_eq_true h_branch]
    simp only [if_true]
    -- Need: ((2^ew + q % 2^ew) * 2^mw + r = x = q * 2^mw + r
    -- Equivalent to: 2^ew + q % 2^ew = q.
    -- i.e., q % 2^ew = q - 2^ew, where q ∈ [2^ew, 2*2^ew).
    have h_q_ge : (2 : ℤ) ^ ew.toNat ≤ q := by
      -- From 2^mw * 2^ew ≤ x = q * 2^mw + r ≤ q * 2^mw + 2^mw - 1 < (q+1) * 2^mw.
      -- So 2^mw * 2^ew < (q+1) * 2^mw, i.e., 2^ew < q + 1, i.e., q ≥ 2^ew.
      have h_chain : (2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat
                  < (q + 1) * (2 : ℤ) ^ mw.toNat := by
        have : x < (q + 1) * (2 : ℤ) ^ mw.toNat := by
          rw [h_x_eq, add_mul, one_mul]; linarith
        linarith
      have h_div : (2 : ℤ) ^ ew.toNat < q + 1 := by
        rw [mul_comm] at h_chain
        exact (mul_lt_mul_right hmw_pos).mp h_chain
      linarith
    have h_q_mod : q % (2 : ℤ) ^ ew.toNat = q - (2 : ℤ) ^ ew.toNat := by
      have h_le : q - (2 : ℤ) ^ ew.toNat < (2 : ℤ) ^ ew.toNat := by linarith
      have h_ge : 0 ≤ q - (2 : ℤ) ^ ew.toNat := by linarith
      conv_lhs => rw [show q = (q - (2 : ℤ) ^ ew.toNat) + (2 : ℤ) ^ ew.toNat * 1 from by ring]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt h_ge h_le
    rw [h_q_mod]
    rw [h_x_eq]
    ring
  · -- s = false: q < 2^ew, q % 2^ew = q.
    push_neg at h_branch
    rw [decide_eq_false (not_le.mpr h_branch)]
    simp only [Bool.false_eq_true, if_false, zero_add]
    have h_q_lt' : q < (2 : ℤ) ^ ew.toNat := by
      -- x < 2^mw * 2^ew = (2^ew) * 2^mw, so q < 2^ew.
      have h_chain : q * (2 : ℤ) ^ mw.toNat < (2 : ℤ) ^ ew.toNat * (2 : ℤ) ^ mw.toNat := by
        rw [mul_comm ((2 : ℤ) ^ ew.toNat) ((2 : ℤ) ^ mw.toNat)]; linarith
      exact (mul_lt_mul_right hmw_pos).mp h_chain
    rw [Int.emod_eq_of_lt h_q_nn h_q_lt']
    rw [h_x_eq]

/-- `split_bits` is injective on the valid range `[0, 2^(mw+ew+1))`. -/
theorem split_bits_inj (mw ew : ℤ) (Hmw : 0 ≤ mw) (Hew : 0 ≤ ew)
    (x y : ℤ)
    (Hx : 0 ≤ x ∧ x < (2 : ℤ) ^ (mw + ew + 1).toNat)
    (Hy : 0 ≤ y ∧ y < (2 : ℤ) ^ (mw + ew + 1).toNat)
    (H : split_bits mw ew x = split_bits mw ew y) :
    x = y := by
  have hjx := join_split_bits mw ew Hmw Hew x Hx
  have hjy := join_split_bits mw ew Hmw Hew y Hy
  simp only at hjx hjy
  rw [H] at hjx
  linarith [hjx, hjy]

end LeanFlocq
