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

end LeanFlocq
