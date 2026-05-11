/-
Lean port of Coq Flocq's `IEEE754/Bits.v` — bit-level encoding/decoding
of IEEE 754 binary floats.

Original Coq is © 2010–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.

Initial port: `join_bits`, `split_bits`, and `join_bits_range`. The full
round-trip theorems and the `bits_of_binary_float` family are deferred.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Zaux
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Digits
import LeanFlocq.Core.Binary

namespace LeanFlocq

open radix (radix2)

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

/-! ### IEEE 754 encoding of `binary_float` -/

/-- Pack a `binary_float` into its IEEE 754 integer representation.

Parameterized by mantissa width `mw` and exponent width `ew`.
Recovers Coq's `prec := mw + 1` (with hidden bit) and `emax := 2^(ew - 1)`. -/
noncomputable def bits_of_binary_float (mw ew : ℤ)
    (x : binary_float (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat)) : ℤ :=
  match x with
  | .B754_zero s => join_bits mw ew s 0 0
  | .B754_infinity s => join_bits mw ew s 0 ((2 : ℤ) ^ ew.toNat - 1)
  | .B754_nan s pl _ => join_bits mw ew s pl ((2 : ℤ) ^ ew.toNat - 1)
  | .B754_finite s m e _ =>
    let mm := m - (2 : ℤ) ^ mw.toNat
    if 0 ≤ mm then
      join_bits mw ew s mm (e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1)
    else
      join_bits mw ew s m 0

/-- The integer encoding of a `binary_float` lies in `[0, 2^(mw+ew+1))`. -/
theorem bits_of_binary_float_range (mw ew : ℤ) (Hmw : 0 ≤ mw) (Hew : 0 < ew)
    (x : binary_float (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat)) :
    0 ≤ bits_of_binary_float mw ew x
      ∧ bits_of_binary_float mw ew x < (2 : ℤ) ^ (mw + ew + 1).toNat := by
  have Hew' : 0 ≤ ew := le_of_lt Hew
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  have hew_pos : 0 < (2 : ℤ) ^ ew.toNat := pow_pos (by norm_num) _
  have hew_m1_pos : 0 < (2 : ℤ) ^ (ew - 1).toNat := pow_pos (by norm_num) _
  -- 2^ew = 2 * 2^(ew - 1).
  have h_pow_ew : (2 : ℤ) ^ ew.toNat = 2 * (2 : ℤ) ^ (ew - 1).toNat := by
    have h_toNat : ew.toNat = (ew - 1).toNat + 1 := by omega
    rw [h_toNat, pow_succ]; ring
  cases x with
  | B754_zero s =>
    show 0 ≤ join_bits mw ew s 0 0 ∧ _
    exact join_bits_range mw ew Hmw Hew' s 0 0
            ⟨le_refl _, hmw_pos⟩ ⟨le_refl _, hew_pos⟩
  | B754_infinity s =>
    show 0 ≤ join_bits mw ew s 0 ((2 : ℤ) ^ ew.toNat - 1) ∧ _
    refine join_bits_range mw ew Hmw Hew' s 0 ((2 : ℤ) ^ ew.toNat - 1)
            ⟨le_refl _, hmw_pos⟩ ⟨?_, ?_⟩
    · linarith
    · linarith
  | B754_nan s pl h_nan =>
    obtain ⟨h_pl_pos, h_pl_digits⟩ := h_nan
    show 0 ≤ join_bits mw ew s pl ((2 : ℤ) ^ ew.toNat - 1) ∧ _
    refine join_bits_range mw ew Hmw Hew' s pl ((2 : ℤ) ^ ew.toNat - 1)
            ⟨by linarith, ?_⟩ ⟨by linarith, by linarith⟩
    have h_pl_lt_pow : pl < (2 : ℤ) ^ mw.toNat := by
      have h_mag : Zdigits radix2 pl ≤ mw := by linarith
      have h_pl_ne : pl ≠ 0 := by linarith
      have h_corr := Zdigits_correct radix2 h_pl_ne
      have h_pl_lt : |(pl : ℝ)| < bpow radix2 (Zdigits radix2 pl) := h_corr.2
      have h_pow_le : bpow radix2 (Zdigits radix2 pl) ≤ bpow radix2 mw := bpow_le _ h_mag
      have h_pl_abs : |(pl : ℝ)| = (pl : ℝ) := abs_of_pos (by exact_mod_cast (by linarith : 0 < pl))
      have h_pl_bpow : (pl : ℝ) < bpow radix2 mw := by
        rw [← h_pl_abs]; linarith
      have h_bpow_eq : bpow radix2 mw = ((2 : ℤ) ^ mw.toNat : ℝ) := by
        rw [← IZR_Zpower radix2 Hmw]
        push_cast
        rfl
      rw [h_bpow_eq] at h_pl_bpow
      exact_mod_cast h_pl_bpow
    exact h_pl_lt_pow
  | B754_finite s m e h_bd =>
    have h_m_pos : 1 ≤ m := h_bd.1
    have h_canon : canonical_mantissa (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat) m e := h_bd.2.1
    have h_e_le : e ≤ (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) := h_bd.2.2
    have h_m_ne : m ≠ 0 := by linarith
    -- m < 2 * 2^mw: from Zdigits radix2 m ≤ prec = mw + 1.
    have h_m_digits : Zdigits radix2 m ≤ mw + 1 := by
      unfold canonical_mantissa FLT_exp at h_canon
      have h_d_pos : 1 ≤ Zdigits radix2 m := Zdigits_gt_0 radix2 h_m_ne
      have h_max_le : (Zdigits radix2 m + e) - (mw + 1) ≤ e := by
        have h_le_right : ((Zdigits radix2 m + e) - (mw + 1))
            ≤ max ((Zdigits radix2 m + e) - (mw + 1))
                  (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) :=
          le_max_left _ _
        linarith [le_of_eq h_canon, h_le_right]
      linarith
    have h_m_lt : m < 2 * (2 : ℤ) ^ mw.toNat := by
      have h_corr := Zdigits_correct radix2 h_m_ne
      have h_m_lt_bpow : |(m : ℝ)| < bpow radix2 (Zdigits radix2 m) := h_corr.2
      have h_pow_le : bpow radix2 (Zdigits radix2 m) ≤ bpow radix2 (mw + 1) :=
        bpow_le _ h_m_digits
      have h_m_abs : |(m : ℝ)| = (m : ℝ) := abs_of_pos (by exact_mod_cast (by linarith : 0 < m))
      have h_m_bpow : (m : ℝ) < bpow radix2 (mw + 1) := by
        rw [← h_m_abs]; linarith
      have h_bpow_eq : bpow radix2 (mw + 1) = ((2 : ℤ) ^ (mw + 1).toNat : ℝ) := by
        rw [← IZR_Zpower radix2 (by linarith : (0 : ℤ) ≤ mw + 1)]
        push_cast
        rfl
      rw [h_bpow_eq] at h_m_bpow
      have h_m_lt_int : m < (2 : ℤ) ^ (mw + 1).toNat := by exact_mod_cast h_m_bpow
      have h_pow_succ : (2 : ℤ) ^ (mw + 1).toNat = 2 * (2 : ℤ) ^ mw.toNat := by
        have : (mw + 1).toNat = mw.toNat + 1 := by omega
        rw [this, pow_succ]; ring
      linarith
    -- emin ≤ e from h_canon (via max ≥ emin).
    have h_emin_le : 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) ≤ e := by
      unfold canonical_mantissa FLT_exp at h_canon
      have h_max_ge :
          (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1))
          ≤ max ((Zdigits radix2 m + e) - (mw + 1))
                (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) :=
        le_max_right _ _
      linarith [le_of_eq h_canon]
    -- Compute the bits_of_binary_float for the finite case explicitly.
    show 0 ≤ bits_of_binary_float mw ew (.B754_finite s m e h_bd)
          ∧ bits_of_binary_float mw ew (.B754_finite s m e h_bd)
              < (2 : ℤ) ^ (mw + ew + 1).toNat
    unfold bits_of_binary_float
    simp only
    by_cases h_mm : 0 ≤ m - (2 : ℤ) ^ mw.toNat
    · rw [if_pos h_mm]
      refine join_bits_range mw ew Hmw Hew' s (m - (2 : ℤ) ^ mw.toNat)
              (e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1)
              ⟨h_mm, by linarith [h_m_lt]⟩ ⟨by linarith, ?_⟩
      rw [h_pow_ew]
      linarith
    · push_neg at h_mm
      have h_m_lt_pow : m < (2 : ℤ) ^ mw.toNat := by linarith
      rw [if_neg (not_le.mpr h_mm)]
      exact join_bits_range mw ew Hmw Hew' s m 0
              ⟨by linarith, h_m_lt_pow⟩ ⟨le_refl _, hew_pos⟩

/-- Structural unpacking of a `binary_float` into `(sign, mantissa, exponent)`.
This mirrors `bits_of_binary_float` but produces the tuple directly. -/
noncomputable def split_bits_of_binary_float (mw ew : ℤ)
    (x : binary_float (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat)) : Bool × ℤ × ℤ :=
  match x with
  | .B754_zero s => (s, 0, 0)
  | .B754_infinity s => (s, 0, (2 : ℤ) ^ ew.toNat - 1)
  | .B754_nan s pl _ => (s, pl, (2 : ℤ) ^ ew.toNat - 1)
  | .B754_finite s m e _ =>
    let mm := m - (2 : ℤ) ^ mw.toNat
    if 0 ≤ mm then
      (s, mm, e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1)
    else
      (s, m, 0)

/-- The integer encoding splits to the same tuple as the structural unpacking. -/
theorem split_bits_of_binary_float_correct (mw ew : ℤ) (Hmw : 0 ≤ mw) (Hew : 0 < ew)
    (x : binary_float (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat)) :
    split_bits mw ew (bits_of_binary_float mw ew x) = split_bits_of_binary_float mw ew x := by
  have Hew' : 0 ≤ ew := le_of_lt Hew
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  have hew_pos : 0 < (2 : ℤ) ^ ew.toNat := pow_pos (by norm_num) _
  -- 2^ew = 2 * 2^(ew - 1).
  have h_pow_ew : (2 : ℤ) ^ ew.toNat = 2 * (2 : ℤ) ^ (ew - 1).toNat := by
    have h_toNat : ew.toNat = (ew - 1).toNat + 1 := by omega
    rw [h_toNat, pow_succ]; ring
  cases x with
  | B754_zero s =>
    show split_bits mw ew (join_bits mw ew s 0 0) = (s, 0, 0)
    exact split_join_bits mw ew Hmw Hew' s 0 0
            ⟨le_refl _, hmw_pos⟩ ⟨le_refl _, hew_pos⟩
  | B754_infinity s =>
    show split_bits mw ew (join_bits mw ew s 0 ((2 : ℤ) ^ ew.toNat - 1))
         = (s, 0, (2 : ℤ) ^ ew.toNat - 1)
    exact split_join_bits mw ew Hmw Hew' s 0 ((2 : ℤ) ^ ew.toNat - 1)
            ⟨le_refl _, hmw_pos⟩ ⟨by linarith, by linarith⟩
  | B754_nan s pl h_nan =>
    obtain ⟨h_pl_pos, h_pl_digits⟩ := h_nan
    show split_bits mw ew (join_bits mw ew s pl ((2 : ℤ) ^ ew.toNat - 1))
         = (s, pl, (2 : ℤ) ^ ew.toNat - 1)
    -- Same proof as in bits_of_binary_float_range for the NaN case.
    have h_pl_lt_pow : pl < (2 : ℤ) ^ mw.toNat := by
      have h_mag : Zdigits radix2 pl ≤ mw := by linarith
      have h_pl_ne : pl ≠ 0 := by linarith
      have h_corr := Zdigits_correct radix2 h_pl_ne
      have h_pl_lt : |(pl : ℝ)| < bpow radix2 (Zdigits radix2 pl) := h_corr.2
      have h_pow_le : bpow radix2 (Zdigits radix2 pl) ≤ bpow radix2 mw := bpow_le _ h_mag
      have h_pl_abs : |(pl : ℝ)| = (pl : ℝ) := abs_of_pos (by exact_mod_cast (by linarith : 0 < pl))
      have h_pl_bpow : (pl : ℝ) < bpow radix2 mw := by
        rw [← h_pl_abs]; linarith
      have h_bpow_eq : bpow radix2 mw = ((2 : ℤ) ^ mw.toNat : ℝ) := by
        rw [← IZR_Zpower radix2 Hmw]; push_cast; rfl
      rw [h_bpow_eq] at h_pl_bpow
      exact_mod_cast h_pl_bpow
    exact split_join_bits mw ew Hmw Hew' s pl ((2 : ℤ) ^ ew.toNat - 1)
            ⟨by linarith, h_pl_lt_pow⟩ ⟨by linarith, by linarith⟩
  | B754_finite s m e h_bd =>
    have h_m_pos : 1 ≤ m := h_bd.1
    have h_canon : canonical_mantissa (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat) m e := h_bd.2.1
    have h_e_le : e ≤ (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) := h_bd.2.2
    have h_m_ne : m ≠ 0 := by linarith
    have h_m_digits : Zdigits radix2 m ≤ mw + 1 := by
      unfold canonical_mantissa FLT_exp at h_canon
      have h_d_pos : 1 ≤ Zdigits radix2 m := Zdigits_gt_0 radix2 h_m_ne
      have h_max_le : (Zdigits radix2 m + e) - (mw + 1) ≤ e := by
        have h_le_right : ((Zdigits radix2 m + e) - (mw + 1))
            ≤ max ((Zdigits radix2 m + e) - (mw + 1))
                  (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) :=
          le_max_left _ _
        linarith [le_of_eq h_canon, h_le_right]
      linarith
    have h_m_lt : m < 2 * (2 : ℤ) ^ mw.toNat := by
      have h_corr := Zdigits_correct radix2 h_m_ne
      have h_m_lt_bpow : |(m : ℝ)| < bpow radix2 (Zdigits radix2 m) := h_corr.2
      have h_pow_le : bpow radix2 (Zdigits radix2 m) ≤ bpow radix2 (mw + 1) :=
        bpow_le _ h_m_digits
      have h_m_abs : |(m : ℝ)| = (m : ℝ) := abs_of_pos (by exact_mod_cast (by linarith : 0 < m))
      have h_m_bpow : (m : ℝ) < bpow radix2 (mw + 1) := by
        rw [← h_m_abs]; linarith
      have h_bpow_eq : bpow radix2 (mw + 1) = ((2 : ℤ) ^ (mw + 1).toNat : ℝ) := by
        rw [← IZR_Zpower radix2 (by linarith : (0 : ℤ) ≤ mw + 1)]; push_cast; rfl
      rw [h_bpow_eq] at h_m_bpow
      have h_m_lt_int : m < (2 : ℤ) ^ (mw + 1).toNat := by exact_mod_cast h_m_bpow
      have h_pow_succ : (2 : ℤ) ^ (mw + 1).toNat = 2 * (2 : ℤ) ^ mw.toNat := by
        have : (mw + 1).toNat = mw.toNat + 1 := by omega
        rw [this, pow_succ]; ring
      linarith
    have h_emin_le : 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) ≤ e := by
      unfold canonical_mantissa FLT_exp at h_canon
      have h_max_ge :
          (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1))
          ≤ max ((Zdigits radix2 m + e) - (mw + 1))
                (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) :=
        le_max_right _ _
      linarith [le_of_eq h_canon]
    show split_bits mw ew (bits_of_binary_float mw ew (.B754_finite s m e h_bd))
         = split_bits_of_binary_float mw ew (.B754_finite s m e h_bd)
    unfold bits_of_binary_float split_bits_of_binary_float
    simp only
    by_cases h_mm : 0 ≤ m - (2 : ℤ) ^ mw.toNat
    · rw [if_pos h_mm, if_pos h_mm]
      apply split_join_bits mw ew Hmw Hew' s (m - (2 : ℤ) ^ mw.toNat)
              (e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1)
              ⟨h_mm, by linarith [h_m_lt]⟩ ⟨by linarith, ?_⟩
      rw [h_pow_ew]; linarith
    · push_neg at h_mm
      have h_m_lt_pow : m < (2 : ℤ) ^ mw.toNat := by linarith
      rw [if_neg (not_le.mpr h_mm), if_neg (not_le.mpr h_mm)]
      exact split_join_bits mw ew Hmw Hew' s m 0
              ⟨by linarith, h_m_lt_pow⟩ ⟨le_refl _, hew_pos⟩

/-! ### Decoding bits to a `full_float`

The decoding side produces a `full_float` (the validation-erased
version of `binary_float`). Lifting to `binary_float` requires
`binary_float_of_bits_aux_correct`, which is deferred (it needs
`bounded_canonical_lt_emax` that we haven't ported yet).
-/

/-- Decode an integer bit pattern into a `full_float`. -/
noncomputable def binary_float_of_bits_aux (mw ew : ℤ) (x : ℤ) : full_float :=
  let p := split_bits mw ew x
  let sx := p.1
  let mx := p.2.1
  let ex := p.2.2
  let emin : ℤ := 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)
  if ex = 0 then
    -- Subnormal or zero.
    if mx = 0 then full_float.F754_zero sx
    else if 0 < mx then full_float.F754_finite sx mx emin
    else full_float.F754_nan false 1  -- dummy (unreachable: mx is a remainder, ≥ 0)
  else if ex = (2 : ℤ) ^ ew.toNat - 1 then
    -- Infinity or NaN (max exponent).
    if mx = 0 then full_float.F754_infinity sx
    else if 0 < mx then full_float.F754_nan sx mx
    else full_float.F754_nan false 1  -- dummy
  else
    -- Normal: prepend the hidden bit.
    let m := mx + (2 : ℤ) ^ mw.toNat
    if 0 < m then full_float.F754_finite sx m (ex + emin - 1)
    else full_float.F754_nan false 1  -- dummy

/-! ### Correctness of decoding -/

/-- `bpow radix2` agrees with integer `2 ^ _.toNat` cast to ℝ. -/
private theorem bpow_radix2_eq (k : ℤ) (Hk : 0 ≤ k) :
    bpow radix2 k = ((2 : ℤ) ^ k.toNat : ℝ) := by
  rw [← IZR_Zpower radix2 Hk]
  push_cast
  rfl

/-- `Zdigits radix2 1 = 1`. -/
private theorem Zdigits_radix2_one : Zdigits radix2 1 = 1 := by
  apply Zdigits_unique
  · rw [show (1 - 1 : ℤ) = 0 from by ring, bpow_zero]
    simp
  · rw [show (1 : ℤ) = 1 from rfl]
    rw [bpow_radix2_eq 1 (by norm_num)]
    push_cast; norm_num

/-- The decoding function always produces a valid `full_float`. -/
theorem binary_float_of_bits_aux_correct (mw ew : ℤ) (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < (2 : ℤ) ^ (ew - 1).toNat) (x : ℤ) :
    valid_binary (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat)
      (binary_float_of_bits_aux mw ew x) := by
  set prec := mw + 1 with hprec_def
  set emax := (2 : ℤ) ^ (ew - 1).toNat with hemax_def
  set emin := 3 - emax - prec with hemin_def
  have hprec_pos : 0 < prec := by linarith
  have hmw_nn : 0 ≤ mw := le_of_lt Hmw
  have hew_nn : 0 ≤ ew := le_of_lt Hew
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  have hew_pos : 0 < (2 : ℤ) ^ ew.toNat := pow_pos (by norm_num) _
  have hemax_pos : 0 < emax := by rw [hemax_def]; exact pow_pos (by norm_num) _
  have h_emin_le : emin ≤ emax - prec := by rw [hemin_def]; linarith
  have h_pow_ew : (2 : ℤ) ^ ew.toNat = 2 * emax := by
    rw [hemax_def]
    have h_toNat : ew.toNat = (ew - 1).toNat + 1 := by omega
    rw [h_toNat, pow_succ]; ring
  have h_nan_one : nan_pl prec 1 := by
    refine ⟨le_refl _, ?_⟩
    rw [Zdigits_radix2_one]; linarith
  -- Unfold the function and split_bits, then set the projection variables.
  show valid_binary prec emax (binary_float_of_bits_aux mw ew x)
  unfold binary_float_of_bits_aux split_bits
  simp only
  set mx := x % (2 : ℤ) ^ mw.toNat with hmx_def
  set ex := x / (2 : ℤ) ^ mw.toNat % (2 : ℤ) ^ ew.toNat with hex_def
  have hmx_nn : 0 ≤ mx := Int.emod_nonneg _ (ne_of_gt hmw_pos)
  have hmx_lt : mx < (2 : ℤ) ^ mw.toNat := Int.emod_lt_of_pos _ hmw_pos
  have hex_nn : 0 ≤ ex := Int.emod_nonneg _ (ne_of_gt hew_pos)
  have hex_lt : ex < (2 : ℤ) ^ ew.toNat := Int.emod_lt_of_pos _ hew_pos
  by_cases h_ex0 : ex = 0
  · rw [if_pos h_ex0]
    by_cases h_mx0 : mx = 0
    · rw [if_pos h_mx0]; trivial  -- F754_zero
    · rw [if_neg h_mx0]
      by_cases h_mx_pos : 0 < mx
      · rw [if_pos h_mx_pos]
        -- F754_finite sx mx emin
        show bounded prec emax mx emin
        refine ⟨h_mx_pos, ?_, h_emin_le⟩
        -- canonical_mantissa: FLT_exp emin prec (Zdigits mx + emin) = emin.
        show FLT_exp emin prec (Zdigits radix2 mx + emin) = emin
        unfold FLT_exp
        have h_d : Zdigits radix2 mx ≤ mw := by
          apply Zdigits_le_Zpower radix2 hmw_nn
          rw [abs_of_nonneg hmx_nn]; exact hmx_lt
        -- max(Zdigits mx + emin - prec, emin) = emin since Zdigits mx ≤ mw = prec - 1.
        rw [max_eq_right]
        linarith
      · -- mx ≤ 0 but mx ≠ 0 ⟹ contradicts hmx_nn.
        push_neg at h_mx_pos
        exfalso
        have : mx = 0 := le_antisymm h_mx_pos hmx_nn
        exact h_mx0 this
  · rw [if_neg h_ex0]
    by_cases h_ex_max : ex = (2 : ℤ) ^ ew.toNat - 1
    · rw [if_pos h_ex_max]
      by_cases h_mx0 : mx = 0
      · rw [if_pos h_mx0]; trivial  -- F754_infinity
      · rw [if_neg h_mx0]
        by_cases h_mx_pos : 0 < mx
        · rw [if_pos h_mx_pos]
          -- F754_nan sx mx, need nan_pl prec mx.
          show nan_pl prec mx
          refine ⟨h_mx_pos, ?_⟩
          have h_d : Zdigits radix2 mx ≤ mw := by
            apply Zdigits_le_Zpower radix2 hmw_nn
            rw [abs_of_nonneg hmx_nn]; exact hmx_lt
          linarith
        · push_neg at h_mx_pos
          exfalso
          have : mx = 0 := le_antisymm h_mx_pos hmx_nn
          exact h_mx0 this
    · rw [if_neg h_ex_max]
      -- Normal: m = mx + 2^mw.
      set m := mx + (2 : ℤ) ^ mw.toNat with hm_def
      have hm_ge : (2 : ℤ) ^ mw.toNat ≤ m := by linarith
      have hm_lt : m < 2 * (2 : ℤ) ^ mw.toNat := by linarith
      have hm_pos : 0 < m := by linarith
      have hm_ge_1 : 1 ≤ m := by linarith
      rw [if_pos hm_pos]
      -- F754_finite sx m (ex + emin - 1).
      show bounded prec emax m (ex + emin - 1)
      have h_Zdigits_m : Zdigits radix2 m = prec := by
        apply Zdigits_unique
        · rw [show (prec - 1 : ℤ) = mw from by rw [hprec_def]; ring]
          rw [bpow_radix2_eq mw hmw_nn]
          rw [abs_of_pos (by exact_mod_cast hm_pos : (0 : ℝ) < (m : ℝ))]
          exact_mod_cast hm_ge
        · rw [bpow_radix2_eq prec (le_of_lt hprec_pos)]
          rw [abs_of_pos (by exact_mod_cast hm_pos : (0 : ℝ) < (m : ℝ))]
          have h_pow_prec : (2 : ℤ) ^ prec.toNat = 2 * (2 : ℤ) ^ mw.toNat := by
            rw [hprec_def]
            have : (mw + 1).toNat = mw.toNat + 1 := by omega
            rw [this, pow_succ]; ring
          have h_m_lt_int : m < (2 : ℤ) ^ prec.toNat := by
            rw [h_pow_prec]; exact hm_lt
          exact_mod_cast h_m_lt_int
      have h_ex_pos : 1 ≤ ex := by
        rcases lt_or_eq_of_le hex_nn with h | h
        · exact h
        · exact absurd h.symm h_ex0
      have h_ex_le : ex ≤ (2 : ℤ) ^ ew.toNat - 2 := by
        have : ex ≠ (2 : ℤ) ^ ew.toNat - 1 := h_ex_max
        omega
      refine ⟨hm_ge_1, ?_, ?_⟩
      · -- canonical_mantissa: FLT_exp emin prec (Zdigits m + (ex + emin - 1)) = ex + emin - 1.
        show FLT_exp emin prec (Zdigits radix2 m + (ex + emin - 1)) = ex + emin - 1
        unfold FLT_exp
        rw [h_Zdigits_m]
        -- max((prec + ex + emin - 1) - prec, emin) = max(ex + emin - 1, emin) = ex + emin - 1.
        rw [show (prec + (ex + emin - 1) - prec : ℤ) = ex + emin - 1 from by ring]
        rw [max_eq_left]
        linarith
      · -- ex + emin - 1 ≤ emax - prec.
        rw [hemin_def]
        rw [h_pow_ew] at h_ex_le
        linarith

/-- Decode an integer bit pattern into a `binary_float`. -/
noncomputable def binary_float_of_bits (mw ew : ℤ) (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < (2 : ℤ) ^ (ew - 1).toNat) (x : ℤ) :
    binary_float (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat) :=
  binary_float.FF2B (binary_float_of_bits_aux mw ew x)
    (binary_float_of_bits_aux_correct mw ew Hmw Hew Hmax x)

/-- The `bits_of_binary_float` function lifted to `full_float`.
Equivalent to `bits_of_binary_float ∘ FF2B`, but with no dependent
typing constraints (FF2B's validity proof is bypassed via case analysis). -/
private noncomputable def bits_of_full_float (mw ew : ℤ) (ff : full_float) : ℤ :=
  match ff with
  | .F754_zero s => join_bits mw ew s 0 0
  | .F754_infinity s => join_bits mw ew s 0 ((2 : ℤ) ^ ew.toNat - 1)
  | .F754_nan s pl => join_bits mw ew s pl ((2 : ℤ) ^ ew.toNat - 1)
  | .F754_finite s m e =>
    let mm := m - (2 : ℤ) ^ mw.toNat
    if 0 ≤ mm then
      join_bits mw ew s mm (e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1)
    else
      join_bits mw ew s m 0

private theorem bits_of_FF2B (mw ew : ℤ) (ff : full_float)
    (h : valid_binary (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat) ff) :
    bits_of_binary_float mw ew (binary_float.FF2B ff h)
      = bits_of_full_float mw ew ff := by
  cases ff <;> rfl

/-! ### Round-trip theorems -/

/-- 2^ew - 1 > 0 (the max exponent field is nonzero). -/
private theorem pow_ew_minus_one_ne_zero (ew : ℤ) (Hew : 0 < ew) :
    (2 : ℤ) ^ ew.toNat - 1 ≠ 0 := by
  have h_ne : ew.toNat ≠ 0 := by omega
  have h_one_lt : (1 : ℤ) < (2 : ℤ) ^ ew.toNat :=
    one_lt_pow₀ (by norm_num : (1 : ℤ) < 2) h_ne
  linarith

/-- For a subnormal finite value (`m < 2^mw`), the exponent equals `emin`. -/
private theorem subnormal_exp_eq_emin (mw ew : ℤ) (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < (2 : ℤ) ^ (ew - 1).toNat)
    {m e : ℤ}
    (h_bd : bounded (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat) m e)
    (h_m_lt : m < (2 : ℤ) ^ mw.toNat) :
    e = 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) := by
  obtain ⟨h_m_pos, h_canon, _⟩ := h_bd
  -- canonical_mantissa: FLT_exp emin prec (Zdigits m + e) = e.
  unfold canonical_mantissa FLT_exp at h_canon
  have h_m_ne : m ≠ 0 := by linarith
  have h_Zd_le : Zdigits radix2 m ≤ mw := by
    apply Zdigits_le_Zpower radix2 (le_of_lt Hmw)
    rw [abs_of_pos (by linarith : (0 : ℤ) < m)]; exact h_m_lt
  -- (Zdigits m + e) - (mw+1) ≤ mw + e - (mw+1) = e - 1 < e.
  -- So the max with emin must be emin (else it would be ≤ e-1, giving e ≤ e-1).
  -- Thus emin = e.
  rcases le_or_lt ((Zdigits radix2 m + e) - (mw + 1))
                  (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) with h_le | h_lt
  · rw [max_eq_right h_le] at h_canon
    linarith
  · rw [max_eq_left (le_of_lt h_lt)] at h_canon
    -- h_canon : (Zdigits m + e) - (mw+1) = e, so Zdigits m = mw+1, contradicting Zd ≤ mw.
    linarith

/-- For a normal finite value (`2^mw ≤ m`), the encoded exponent field
`e - emin + 1` is in the valid range `[1, 2^ew - 1)`. -/
private theorem normal_exp_field_bounds (mw ew : ℤ) (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < (2 : ℤ) ^ (ew - 1).toNat)
    {m e : ℤ}
    (h_bd : bounded (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat) m e)
    (h_m_ge : (2 : ℤ) ^ mw.toNat ≤ m) :
    let emin := 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)
    1 ≤ e - emin + 1 ∧ e - emin + 1 < (2 : ℤ) ^ ew.toNat - 1 := by
  obtain ⟨_, h_canon, h_e_le⟩ := h_bd
  set emin := 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) with hemin_def
  -- From canonical_mantissa: max(Zdigits m + e - (mw+1), emin) = e.
  unfold canonical_mantissa FLT_exp at h_canon
  -- emin ≤ e (since the max ≥ emin and equals e).
  have h_emin_le_e : emin ≤ e := by
    have : emin ≤ max ((Zdigits radix2 m + e) - (mw + 1)) emin := le_max_right _ _
    linarith [le_of_eq h_canon]
  refine ⟨by linarith, ?_⟩
  -- e - emin + 1 < 2^ew - 1 ↔ e < 2^ew + emin - 2 = 2*emax + emin - 2.
  -- Substituting emin = 3 - emax - (mw+1): 2*emax + 3 - emax - (mw+1) - 2 = emax - (mw+1) + ... let me compute.
  -- 2^ew = 2 * 2^(ew-1) = 2 * emax (where emax = 2^(ew-1)).
  have h_pow_ew : (2 : ℤ) ^ ew.toNat = 2 * (2 : ℤ) ^ (ew - 1).toNat := by
    have h_toNat : ew.toNat = (ew - 1).toNat + 1 := by omega
    rw [h_toNat, pow_succ]; ring
  rw [h_pow_ew, hemin_def]
  linarith

/-- Decoding the encoding of a `binary_float` recovers the original. -/
theorem binary_float_of_bits_of_binary_float (mw ew : ℤ) (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < (2 : ℤ) ^ (ew - 1).toNat)
    (x : binary_float (mw + 1) ((2 : ℤ) ^ (ew - 1).toNat)) :
    binary_float_of_bits mw ew Hmw Hew Hmax (bits_of_binary_float mw ew x) = x := by
  apply binary_float.B2FF_inj
  -- B2FF (binary_float_of_bits ...) = binary_float_of_bits_aux (bits_of_binary_float x).
  show binary_float.B2FF
        (binary_float.FF2B (binary_float_of_bits_aux mw ew (bits_of_binary_float mw ew x)) _)
       = binary_float.B2FF x
  rw [binary_float.B2FF_FF2B]
  unfold binary_float_of_bits_aux
  rw [split_bits_of_binary_float_correct mw ew (le_of_lt Hmw) Hew x]
  have h_pow_ew_ne_1 := pow_ew_minus_one_ne_zero ew Hew
  cases x with
  | B754_zero s =>
    unfold split_bits_of_binary_float
    simp; rfl
  | B754_infinity s =>
    unfold split_bits_of_binary_float
    simp [h_pow_ew_ne_1]; rfl
  | B754_nan s pl h_nan =>
    have h_pl_pos : 1 ≤ pl := h_nan.1
    have h_pl_ne_0 : pl ≠ 0 := by linarith
    have h_pl_pos' : 0 < pl := by linarith
    unfold split_bits_of_binary_float
    simp [h_pow_ew_ne_1, h_pl_ne_0, h_pl_pos']; rfl
  | B754_finite s m e h_bd =>
    have h_m_pos : 1 ≤ m := h_bd.1
    -- Use explicit emin form to match what the unfolded function shows.
    unfold split_bits_of_binary_float
    by_cases h_mm : 0 ≤ m - (2 : ℤ) ^ mw.toNat
    · -- Normal branch.
      have h_m_ge : (2 : ℤ) ^ mw.toNat ≤ m := by linarith
      obtain ⟨h_field_ge, h_field_lt⟩ :=
        normal_exp_field_bounds mw ew Hmw Hew Hmax h_bd h_m_ge
      have h_ex_ne_0 :
          e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1 ≠ 0 := by linarith
      have h_ex_ne_max :
          e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1
            ≠ (2 : ℤ) ^ ew.toNat - 1 := by linarith
      have h_m_pos_real : 0 < m := by linarith
      have h_m_eq : m - (2 : ℤ) ^ mw.toNat + (2 : ℤ) ^ mw.toNat = m := by ring
      have h_e_eq :
          e - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1
            + (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) - 1 = e := by ring
      simp only [if_pos h_mm, if_neg h_ex_ne_0, if_neg h_ex_ne_max,
                 h_m_eq, h_e_eq, if_pos h_m_pos_real]
      rfl
    · -- Subnormal branch.
      push_neg at h_mm
      have h_m_lt : m < (2 : ℤ) ^ mw.toNat := by linarith
      have h_not_le : ¬ 0 ≤ m - (2 : ℤ) ^ mw.toNat := not_le.mpr h_mm
      have h_m_ne_0 : m ≠ 0 := by linarith
      have h_m_pos' : 0 < m := by linarith
      have h_e_eq_emin : e = 3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1) :=
        subnormal_exp_eq_emin mw ew Hmw Hew Hmax h_bd h_m_lt
      simp only [if_neg h_not_le, if_pos (rfl : (0 : ℤ) = 0),
                 if_neg h_m_ne_0, if_pos h_m_pos']
      show full_float.F754_finite s m (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1))
            = full_float.F754_finite s m e
      rw [← h_e_eq_emin]

/-- Encoding the decoding of a bit pattern in range recovers the pattern. -/
theorem bits_of_binary_float_of_bits (mw ew : ℤ) (Hmw : 0 < mw) (Hew : 0 < ew)
    (Hmax : mw + 1 < (2 : ℤ) ^ (ew - 1).toNat)
    (x : ℤ) (Hx : 0 ≤ x ∧ x < (2 : ℤ) ^ (mw + ew + 1).toNat) :
    bits_of_binary_float mw ew (binary_float_of_bits mw ew Hmw Hew Hmax x) = x := by
  have hmw_nn : 0 ≤ mw := le_of_lt Hmw
  have hew_nn : 0 ≤ ew := le_of_lt Hew
  have hmw_pos : 0 < (2 : ℤ) ^ mw.toNat := pow_pos (by norm_num) _
  have hew_pos : 0 < (2 : ℤ) ^ ew.toNat := pow_pos (by norm_num) _
  set mx := x % (2 : ℤ) ^ mw.toNat with hmx_def
  set ex := x / (2 : ℤ) ^ mw.toNat % (2 : ℤ) ^ ew.toNat with hex_def
  set sx := decide ((2 : ℤ) ^ mw.toNat * (2 : ℤ) ^ ew.toNat ≤ x) with hsx_def
  have hmx_nn : 0 ≤ mx := Int.emod_nonneg _ (ne_of_gt hmw_pos)
  have hmx_lt : mx < (2 : ℤ) ^ mw.toNat := Int.emod_lt_of_pos _ hmw_pos
  have h_jsb : join_bits mw ew sx mx ex = x := by
    have := join_split_bits mw ew hmw_nn hew_nn x Hx
    simp only [hsx_def, hmx_def, hex_def, split_bits] at this
    exact this
  -- Use bits_of_FF2B to bypass dependent typing.
  show bits_of_binary_float mw ew
        (binary_float.FF2B (binary_float_of_bits_aux mw ew x) _) = x
  rw [bits_of_FF2B]
  -- Now we work with bits_of_full_float, which has no dependent typing.
  unfold binary_float_of_bits_aux
  show bits_of_full_float mw ew
        (if ex = 0 then
          if mx = 0 then full_float.F754_zero sx
          else if 0 < mx then
            full_float.F754_finite sx mx (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1))
          else full_float.F754_nan false 1
        else if ex = (2 : ℤ) ^ ew.toNat - 1 then
          if mx = 0 then full_float.F754_infinity sx
          else if 0 < mx then full_float.F754_nan sx mx
          else full_float.F754_nan false 1
        else
          if 0 < mx + (2 : ℤ) ^ mw.toNat then
            full_float.F754_finite sx (mx + (2 : ℤ) ^ mw.toNat)
              (ex + (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) - 1)
          else full_float.F754_nan false 1) = x
  by_cases h_ex0 : ex = 0
  · rw [if_pos h_ex0]
    by_cases h_mx0 : mx = 0
    · rw [if_pos h_mx0]
      show join_bits mw ew sx 0 0 = x
      rw [h_mx0, h_ex0] at h_jsb; exact h_jsb
    · rw [if_neg h_mx0]
      have h_mx_pos : 0 < mx := lt_of_le_of_ne hmx_nn (Ne.symm h_mx0)
      rw [if_pos h_mx_pos]
      -- F754_finite sx mx emin → bits_of_full_float: subnormal branch (mx < 2^mw).
      have h_mm_neg : ¬ 0 ≤ mx - (2 : ℤ) ^ mw.toNat := by linarith
      show bits_of_full_float mw ew (full_float.F754_finite sx mx _) = x
      unfold bits_of_full_float
      simp only [if_neg h_mm_neg]
      show join_bits mw ew sx mx 0 = x
      rw [h_ex0] at h_jsb; exact h_jsb
  · rw [if_neg h_ex0]
    by_cases h_ex_max : ex = (2 : ℤ) ^ ew.toNat - 1
    · rw [if_pos h_ex_max]
      by_cases h_mx0 : mx = 0
      · rw [if_pos h_mx0]
        show join_bits mw ew sx 0 ((2 : ℤ) ^ ew.toNat - 1) = x
        rw [h_mx0, h_ex_max] at h_jsb; exact h_jsb
      · rw [if_neg h_mx0]
        have h_mx_pos : 0 < mx := lt_of_le_of_ne hmx_nn (Ne.symm h_mx0)
        rw [if_pos h_mx_pos]
        show join_bits mw ew sx mx ((2 : ℤ) ^ ew.toNat - 1) = x
        rw [h_ex_max] at h_jsb; exact h_jsb
    · rw [if_neg h_ex_max]
      -- Normal: m = mx + 2^mw > 0.
      have h_m_pos : 0 < mx + (2 : ℤ) ^ mw.toNat := by linarith
      rw [if_pos h_m_pos]
      -- F754_finite sx m (ex + emin - 1) → bits_of_full_float: normal branch.
      have h_mm_nn : 0 ≤ mx + (2 : ℤ) ^ mw.toNat - (2 : ℤ) ^ mw.toNat := by linarith
      show bits_of_full_float mw ew (full_float.F754_finite sx _ _) = x
      unfold bits_of_full_float
      simp only [if_pos h_mm_nn]
      have h_simp_mx : mx + (2 : ℤ) ^ mw.toNat - (2 : ℤ) ^ mw.toNat = mx := by ring
      have h_simp_ex : ex + (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) - 1
            - (3 - (2 : ℤ) ^ (ew - 1).toNat - (mw + 1)) + 1 = ex := by ring
      rw [h_simp_mx, h_simp_ex]
      exact h_jsb

end LeanFlocq
