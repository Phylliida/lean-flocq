/-
Port of `flocq/src/Calc/Round.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Helper functions for computing the rounded value of a real number.
Bridges the `inbetween_float` predicate from `Bracket` with the `round`
function from `Generic_fmt`, and provides `truncate` for normalizing
floats to canonical exponents.
-/

import LeanFlocq.Calc.Bracket
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FIX

namespace LeanFlocq

open radix (radix2)

/-! ## Bridges between location and rounded value -/

section Fcalc_round_fexp

variable (beta : radix) (fexp : ℤ → ℤ)

/-- When `0 < x` is bracketed by `F2R⟨m, e⟩` and `F2R⟨m+1, e⟩`, the canonical
exponent of `x` is `fexp(Zdigits m + e)`, provided either `e ≤ cexp x` or
`e ≤ fexp(Zdigits m + e)`. -/
theorem cexp_inbetween_float (hValid : Valid_exp fexp) {x : ℝ} {m e : ℤ}
    {l : location} (Px : 0 < x) (Bx : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ e ≤ fexp (Zdigits beta m + e)) :
    cexp beta fexp x = fexp (Zdigits beta m + e) := by
  unfold cexp
  have h_bounds := inbetween_float_bounds (beta := beta) m e x l Bx
  have h_mp1_pos : 0 < F2R (beta := beta) ⟨m + 1, e⟩ := lt_trans Px h_bounds.2
  have h_mp1_pos_int : 0 < m + 1 := gt_0_F2R h_mp1_pos
  have Hm : 0 ≤ m := by linarith
  rcases lt_or_eq_of_le Hm with Hm' | Hm0
  · have h_mag : mag beta x = Zdigits beta m + e :=
      mag_F2R_bounds_Zdigits (beta := beta) m e Hm' h_bounds
    rw [h_mag]
  · have hm0 : m = 0 := Hm0.symm
    -- Rewrite Zdigits 0 in He first.
    have He' : e ≤ cexp beta fexp x ∨ e ≤ fexp e := by
      rcases He with H | H
      · exact Or.inl H
      · right; rw [hm0, Zdigits_zero, zero_add] at H; exact H
    -- Rewrite the goal too.
    rw [hm0, Zdigits_zero, zero_add]
    subst hm0
    -- Bounds: 0 ≤ x < F2R⟨1, e⟩ = bpow e, so mag x ≤ e.
    have h_x_lt_bpow : x < bpow beta e := by
      have h_F2R_one : F2R (beta := beta) ⟨(0 : ℤ) + 1, e⟩ = bpow beta e := by
        simp [F2R_bpow]
      rw [← h_F2R_one]; exact h_bounds.2
    have h_x_ne : x ≠ 0 := ne_of_gt Px
    have h_mag_le : mag beta x ≤ e := by
      apply mag_le_bpow beta h_x_ne
      rw [abs_of_pos Px]; exact h_x_lt_bpow
    rcases He' with He | He
    · -- He : e ≤ cexp x = fexp(mag x). Large regime at mag x: fexp e = fexp(mag x).
      have h_mag_le_fexp : mag beta x ≤ fexp (mag beta x) := le_trans h_mag_le He
      have h_stab := ((hValid (mag beta x)).2 h_mag_le_fexp).2
      exact (h_stab e He).symm
    · -- He : e ≤ fexp e. Large regime at e: fexp(mag x) = fexp e.
      have h_stab := ((hValid e).2 He).2
      exact h_stab (mag beta x) (le_trans h_mag_le He)

/-- The disjunctive form of `cexp_inbetween_float`: when `0 ≤ x`, the
condition `e ≤ cexp x ∨ l = Exact` is equivalent to `e ≤ fexp(Zdigits m + e)
∨ l = Exact`. -/
theorem cexp_inbetween_float_loc_Exact (hValid : Valid_exp fexp)
    {x : ℝ} {m e : ℤ} {l : location} (Px : 0 ≤ x)
    (Bx : inbetween_float beta m e x l) :
    (e ≤ cexp beta fexp x ∨ l = location.Exact) ↔
      (e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) := by
  rcases lt_or_eq_of_le Px with hpx | hpx
  · constructor
    · rintro (h | h)
      · left
        rw [← cexp_inbetween_float beta fexp hValid hpx Bx (Or.inl h)]
        exact h
      · exact Or.inr h
    · rintro (h | h)
      · left
        rw [cexp_inbetween_float beta fexp hValid hpx Bx (Or.inr h)]
        exact h
      · exact Or.inr h
  · have h_x_eq : x = 0 := hpx.symm
    rcases Bx with hExact | ⟨c, h_lo, h_hi, _⟩
    · simp
    · rw [h_x_eq] at h_lo h_hi
      have h_m_lt : m < 0 := lt_0_F2R (m := m) (e := e) h_lo
      have h_mp1_pos : 0 < m + 1 := gt_0_F2R (m := m + 1) (e := e) h_hi
      omega

/-- `cond_incr b m`: `m + 1` if `b`, else `m`. -/
def cond_incr (b : Bool) (m : ℤ) : ℤ := if b then m + 1 else m

@[simp] theorem cond_incr_true (m : ℤ) : cond_incr true m = m + 1 := rfl
@[simp] theorem cond_incr_false (m : ℤ) : cond_incr false m = m := rfl

/-- If a rounding `rnd` agrees with a `choice` function on integer
intervals, then on float intervals `round rnd` agrees with `choice`. -/
theorem inbetween_float_round (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (choice : ℤ → location → ℤ)
    (Hc : ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m x l → rnd x = choice m l)
    {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_float beta m (cexp beta fexp x) x l) :
    round beta fexp rnd x = F2R (beta := beta) ⟨choice m l, cexp beta fexp x⟩ := by
  unfold round
  apply F2R_eq
  apply Hc
  set e := cexp beta fexp x with he
  unfold inbetween_int
  -- Goal: inbetween (m : ℝ) ((m+1 : ℤ) : ℝ) (scaled_mantissa β fexp x) l.
  -- Apply inbetween_mult_reg with s := bpow e to lift to inbetween_float.
  apply inbetween_mult_reg (m : ℝ) ((m + 1 : ℤ) : ℝ) (scaled_mantissa beta fexp x) l
    (bpow beta e) (bpow_gt_0 beta e)
  rw [scaled_mantissa_mult_bpow]
  -- Goal: inbetween ((m:ℝ)*bpow e) (((m+1):ℝ)*bpow e) x l
  -- which is exactly inbetween_float β m e x l unfolded.
  exact Hl

/-- Sign-aware version: when the integer-level `rnd` is `cond_Zopp`-symmetric,
the float-level rounding is too. -/
theorem inbetween_float_round_sign (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (choice : Bool → ℤ → location → ℤ)
    (Hc : ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m |x| l →
      rnd x = cond_Zopp (decide (x < 0)) (choice (decide (x < 0)) m l))
    {x : ℝ} {m : ℤ} {l : location}
    (Hx : inbetween_float beta m (cexp beta fexp x) |x| l) :
    round beta fexp rnd x =
      F2R (beta := beta) ⟨cond_Zopp (decide (x < 0)) (choice (decide (x < 0)) m l),
                          cexp beta fexp x⟩ := by
  unfold round
  apply F2R_eq
  set e := cexp beta fexp x with he
  -- (sm < 0) ↔ (x < 0)
  have h_bp_pos : 0 < bpow beta (-e) := bpow_gt_0 beta _
  have h_sign : decide (scaled_mantissa beta fexp x < 0) = decide (x < 0) := by
    have h_iff : scaled_mantissa beta fexp x < 0 ↔ x < 0 := by
      unfold scaled_mantissa
      constructor
      · intro h
        by_contra hx
        push_neg at hx
        have : 0 ≤ x * bpow beta (-cexp beta fexp x) :=
          mul_nonneg hx (bpow_ge_0 beta _)
        linarith
      · intro hx
        have : x * bpow beta (-cexp beta fexp x) < 0 * bpow beta (-cexp beta fexp x) :=
          (mul_lt_mul_iff_of_pos_right h_bp_pos).mpr hx
        rw [zero_mul] at this; exact this
    by_cases h : x < 0
    · simp [h, h_iff.mpr h]
    · have hsm : ¬ scaled_mantissa beta fexp x < 0 := fun hh => h (h_iff.mp hh)
      simp [h, hsm]
  rw [Hc _ _ _ ?_, h_sign]
  -- Now prove: inbetween_int m |sm| l
  unfold inbetween_int
  apply inbetween_mult_reg (m : ℝ) ((m + 1 : ℤ) : ℝ) |scaled_mantissa beta fexp x| l
    (bpow beta e) (bpow_gt_0 beta e)
  -- (|sm| * bpow e) = |x|, and (m * bpow e), ((m+1) * bpow e) match F2R.
  have h_abs_eq : |scaled_mantissa beta fexp x| * bpow beta e = |x| := by
    unfold scaled_mantissa
    rw [abs_mul, abs_of_nonneg (bpow_ge_0 beta _),
        mul_assoc, ← bpow_plus, neg_add_cancel, bpow_zero, mul_one]
  rw [h_abs_eq]
  exact Hx

/-! ## Round-down (DN) -/

theorem inbetween_int_DN {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m x l) : ⌊x⌋ = m := by
  apply Int.floor_eq_iff.mpr
  rcases Hl with hExact | ⟨c, h_lo, h_hi, _⟩
  · refine ⟨?_, ?_⟩
    · rw [hExact]
    · rw [hExact]; push_cast; linarith
  · refine ⟨le_of_lt h_lo, ?_⟩
    have : x < ((m + 1 : ℤ) : ℝ) := h_hi
    push_cast at this; linarith

theorem inbetween_float_DN {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_float beta m (cexp beta fexp x) x l) :
    round beta fexp Int.floor x = F2R (beta := beta) ⟨m, cexp beta fexp x⟩ :=
  inbetween_float_round beta fexp Int.floor (fun m _ => m)
    (fun _ _ _ h => inbetween_int_DN h) Hl

/-- `round_sign_DN s l`: increment iff `s` (the sign of x) is true and `l ≠ Exact`. -/
def round_sign_DN (s : Bool) (l : location) : Bool :=
  match l with
  | .Exact => false
  | .Inexact _ => s

theorem inbetween_int_DN_sign {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m |x| l) :
    ⌊x⌋ = cond_Zopp (decide (x < 0)) (cond_incr (round_sign_DN (decide (x < 0)) l) m) := by
  rcases lt_or_ge x 0 with hx | hx
  · have h_dec : decide (x < 0) = true := by simp [hx]
    rw [h_dec, cond_Zopp_true]
    have h_abs : |x| = -x := abs_of_neg hx
    rw [h_abs] at Hl
    rcases Hl with hE | ⟨c, h_lo, h_hi, _⟩
    · have hx_eq : x = -((m : ℤ) : ℝ) := by push_cast at hE ⊢; linarith
      have h_cast : -((m : ℤ) : ℝ) = ((-m : ℤ) : ℝ) := by push_cast; rfl
      have : ⌊x⌋ = -m := by rw [hx_eq, h_cast, Int.floor_intCast]
      rw [this]
      simp [cond_incr, round_sign_DN]
    · have h_floor : ⌊x⌋ = -(m + 1) := by
        apply Int.floor_eq_iff.mpr
        push_cast at h_lo h_hi ⊢
        refine ⟨by linarith, by linarith⟩
      rw [h_floor]
      simp [cond_incr, round_sign_DN]
  · have hxn : ¬ x < 0 := not_lt.mpr hx
    have h_dec : decide (x < 0) = false := by simp [hxn]
    rw [h_dec, cond_Zopp_false]
    have h_abs : |x| = x := abs_of_nonneg hx
    rw [h_abs] at Hl
    rcases Hl with hE | ⟨c, h_lo, h_hi, _⟩
    · rw [hE, Int.floor_intCast]
      simp [cond_incr, round_sign_DN]
    · have h_floor : ⌊x⌋ = m := by
        apply Int.floor_eq_iff.mpr
        push_cast at h_lo h_hi ⊢
        exact ⟨le_of_lt h_lo, by linarith⟩
      rw [h_floor]
      simp [cond_incr, round_sign_DN]

theorem inbetween_float_DN_sign {x : ℝ} {m : ℤ} {l : location}
    (Hx : inbetween_float beta m (cexp beta fexp x) |x| l) :
    round beta fexp Int.floor x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (cond_incr (round_sign_DN (decide (x < 0)) l) m),
         cexp beta fexp x⟩ :=
  inbetween_float_round_sign beta fexp Int.floor
    (fun s m l => cond_incr (round_sign_DN s l) m)
    (fun _ _ _ h => inbetween_int_DN_sign h) Hx

/-! ## Round-up (UP) -/

/-- `round_UP l`: true iff `l` is not `Exact`. -/
def round_UP (l : location) : Bool :=
  match l with
  | .Exact => false
  | .Inexact _ => true

theorem inbetween_int_UP {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m x l) : ⌈x⌉ = cond_incr (round_UP l) m := by
  rcases Hl with hE | ⟨c, h_lo, h_hi, _⟩
  · simp [round_UP, cond_incr, hE, Int.ceil_intCast]
  · simp [round_UP, cond_incr]
    apply Int.ceil_eq_iff.mpr
    push_cast at h_lo h_hi ⊢
    exact ⟨by linarith, by linarith [h_hi.le]⟩

theorem inbetween_float_UP {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_float beta m (cexp beta fexp x) x l) :
    round beta fexp Int.ceil x =
      F2R (beta := beta) ⟨cond_incr (round_UP l) m, cexp beta fexp x⟩ :=
  inbetween_float_round beta fexp Int.ceil
    (fun m l => cond_incr (round_UP l) m)
    (fun _ _ _ h => inbetween_int_UP h) Hl

/-- `round_sign_UP s l`: true iff `l ≠ Exact` and `s` is false (i.e. `x ≥ 0`). -/
def round_sign_UP (s : Bool) (l : location) : Bool :=
  match l with
  | .Exact => false
  | .Inexact _ => !s

theorem inbetween_int_UP_sign {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m |x| l) :
    ⌈x⌉ = cond_Zopp (decide (x < 0)) (cond_incr (round_sign_UP (decide (x < 0)) l) m) := by
  rcases lt_or_ge x 0 with hx | hx
  · have h_dec : decide (x < 0) = true := by simp [hx]
    rw [h_dec, cond_Zopp_true]
    have h_abs : |x| = -x := abs_of_neg hx
    rw [h_abs] at Hl
    rcases Hl with hE | ⟨c, h_lo, h_hi, _⟩
    · have hx_eq : x = -((m : ℤ) : ℝ) := by push_cast at hE ⊢; linarith
      have h_cast : -((m : ℤ) : ℝ) = ((-m : ℤ) : ℝ) := by push_cast; rfl
      have : ⌈x⌉ = -m := by rw [hx_eq, h_cast, Int.ceil_intCast]
      rw [this]
      simp [cond_incr, round_sign_UP]
    · have h_ceil : ⌈x⌉ = -m := by
        apply Int.ceil_eq_iff.mpr
        push_cast at h_lo h_hi ⊢
        refine ⟨by linarith, by linarith⟩
      rw [h_ceil]
      simp [cond_incr, round_sign_UP]
  · have hxn : ¬ x < 0 := not_lt.mpr hx
    have h_dec : decide (x < 0) = false := by simp [hxn]
    rw [h_dec, cond_Zopp_false]
    have h_abs : |x| = x := abs_of_nonneg hx
    rw [h_abs] at Hl
    rcases Hl with hE | ⟨c, h_lo, h_hi, _⟩
    · rw [hE, Int.ceil_intCast]
      simp [cond_incr, round_sign_UP]
    · have h_ceil : ⌈x⌉ = m + 1 := by
        apply Int.ceil_eq_iff.mpr
        push_cast at h_lo h_hi ⊢
        refine ⟨by linarith, by linarith [h_hi.le]⟩
      rw [h_ceil]
      simp [cond_incr, round_sign_UP]

theorem inbetween_float_UP_sign {x : ℝ} {m : ℤ} {l : location}
    (Hx : inbetween_float beta m (cexp beta fexp x) |x| l) :
    round beta fexp Int.ceil x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (cond_incr (round_sign_UP (decide (x < 0)) l) m),
         cexp beta fexp x⟩ :=
  inbetween_float_round_sign beta fexp Int.ceil
    (fun s m l => cond_incr (round_sign_UP s l) m)
    (fun _ _ _ h => inbetween_int_UP_sign h) Hx

/-! ## Round-toward-zero (ZR) -/

/-- `round_ZR s l`: true iff `s` and `l ≠ Exact`. -/
def round_ZR (s : Bool) (l : location) : Bool :=
  match l with
  | .Exact => false
  | .Inexact _ => s

theorem inbetween_int_ZR {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m x l) :
    Ztrunc x = cond_incr (round_ZR (decide (m < 0)) l) m := by
  rcases Hl with hE | ⟨c, h_lo, h_hi, _⟩
  · rw [hE, Ztrunc_intCast]
    simp [cond_incr, round_ZR]
  · have h_floor : ⌊x⌋ = m := by
      apply Int.floor_eq_iff.mpr
      push_cast at h_lo h_hi ⊢
      exact ⟨le_of_lt h_lo, by linarith⟩
    have h_ceil : ⌈x⌉ = m + 1 := by
      apply Int.ceil_eq_iff.mpr
      push_cast at h_lo h_hi ⊢
      exact ⟨by linarith, by linarith [h_hi.le]⟩
    by_cases hm : m < 0
    · have hx_le_0 : x ≤ 0 := by
        have : x < ((m + 1 : ℤ) : ℝ) := h_hi
        push_cast at this
        have hm1 : (m + 1 : ℤ) ≤ 0 := by linarith
        have : ((m + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hm1
        linarith
      rw [Ztrunc_ceil hx_le_0, h_ceil]
      simp [cond_incr, round_ZR, hm]
    · push_neg at hm
      have hx_pos : 0 ≤ x := by
        have : ((m : ℤ) : ℝ) ≥ 0 := by exact_mod_cast hm
        linarith
      rw [Ztrunc_floor hx_pos, h_floor]
      have hm_dec : decide (m < 0) = false := by simp [hm]
      simp [cond_incr, round_ZR, hm_dec]

theorem inbetween_float_ZR {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_float beta m (cexp beta fexp x) x l) :
    round beta fexp Ztrunc x = F2R (beta := beta)
      ⟨cond_incr (round_ZR (decide (m < 0)) l) m, cexp beta fexp x⟩ :=
  inbetween_float_round beta fexp Ztrunc
    (fun m l => cond_incr (round_ZR (decide (m < 0)) l) m)
    (fun _ _ _ h => inbetween_int_ZR h) Hl

theorem inbetween_int_ZR_sign {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m |x| l) :
    Ztrunc x = cond_Zopp (decide (x < 0)) m := by
  rcases lt_or_ge x 0 with hx | hx
  · have h_dec : decide (x < 0) = true := by simp [hx]
    rw [h_dec, cond_Zopp_true]
    have h_abs : |x| = -x := abs_of_neg hx
    rw [h_abs] at Hl
    have h_ceil : ⌈x⌉ = -m := by
      apply Int.ceil_eq_iff.mpr
      have h_bounds := inbetween_bounds (Hdu := by push_cast; linarith) Hl
      push_cast at h_bounds ⊢
      refine ⟨by linarith [h_bounds.2], by linarith [h_bounds.1]⟩
    rw [Ztrunc_ceil hx.le, h_ceil]
  · have hxn : ¬ x < 0 := not_lt.mpr hx
    have h_dec : decide (x < 0) = false := by simp [hxn]
    rw [h_dec, cond_Zopp_false]
    have h_abs : |x| = x := abs_of_nonneg hx
    rw [h_abs] at Hl
    rw [Ztrunc_floor hx, inbetween_int_DN Hl]

theorem inbetween_float_ZR_sign {x : ℝ} {m : ℤ} {l : location}
    (Hx : inbetween_float beta m (cexp beta fexp x) |x| l) :
    round beta fexp Ztrunc x =
      F2R (beta := beta) ⟨cond_Zopp (decide (x < 0)) m, cexp beta fexp x⟩ :=
  inbetween_float_round_sign beta fexp Ztrunc (fun _ m _ => m)
    (fun _ _ _ h => inbetween_int_ZR_sign h) Hx

end Fcalc_round_fexp

end LeanFlocq
