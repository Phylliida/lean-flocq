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
import LeanFlocq.Core.Round_NE

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

/-! ## Round-to-nearest (N) -/

/-- `round_N p l`: tells whether to increment when rounding to nearest with
parity `p` (used for tie-breaking).
- `Exact` and `Inexact .lt`: don't increment.
- `Inexact .eq` (tie): increment iff `p`.
- `Inexact .gt`: always increment. -/
def round_N (p : Bool) (l : location) : Bool :=
  match l with
  | .Exact => false
  | .Inexact .lt => false
  | .Inexact .eq => p
  | .Inexact .gt => true

theorem inbetween_int_N (choice : ℤ → Bool) {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m x l) :
    Znearest choice x = cond_incr (round_N (choice m) l) m := by
  rcases Hl with hE | ⟨c, h_lo, h_hi, hc⟩
  · -- Exact: x = m
    rw [hE]
    have := (valid_rnd_N choice).Zrnd_intCast m
    show Znearest choice ((m : ℤ) : ℝ) = cond_incr (round_N (choice m) location.Exact) m
    rw [this]; simp [cond_incr, round_N]
  · -- Inexact: m < x < m+1, c = compare x ((m + m+1)/2)
    have h_floor : ⌊x⌋ = m :=
      inbetween_int_DN (.Inexact c h_lo h_hi hc)
    have h_lo' : (m : ℝ) < x := h_lo
    have h_hi' : x < ((m + 1 : ℤ) : ℝ) := h_hi
    -- Rewrite hc: compare x ((m + (m+1))/2) = compare (x - m) (1/2)
    have h_mid : (((m : ℝ) + ((m + 1 : ℤ) : ℝ)) / 2) = (m : ℝ) + 1/2 := by
      push_cast; ring
    rw [h_mid] at hc
    have h_sub : compare x ((m : ℝ) + 1/2) = compare (x - (m : ℝ)) (1/2) := by
      rcases lt_trichotomy x ((m : ℝ) + 1/2) with h | h | h
      · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by linarith)]
      · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (by linarith)]
      · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by linarith)]
    rw [h_sub] at hc
    -- Now Znearest x. Note ⌈x⌉ = m + 1 (since x > m and x ≠ m+1).
    have h_x_lt_int : x < ((m + 1 : ℤ) : ℝ) := h_hi
    have h_x_lt_real : x < (m : ℝ) + 1 := by push_cast at h_x_lt_int; exact h_x_lt_int
    have h_ceil : ⌈x⌉ = m + 1 := by
      apply Int.ceil_eq_iff.mpr
      push_cast
      exact ⟨by linarith, by linarith [h_x_lt_real.le]⟩
    unfold Znearest
    rw [h_floor]
    -- Case-split on c
    rcases c with _ | _ | _
    · -- c = .lt: compare (x - m) (1/2) = .lt → x - m < 1/2
      have h_lt : x - (m : ℝ) < 1/2 := compare_lt_iff_lt.mp hc
      have h_lt' : x - ((m : ℤ) : ℝ) < 1/2 := by push_cast; exact h_lt
      rw [if_pos h_lt']
      simp [cond_incr, round_N]
    · -- c = .eq: compare (x - m) (1/2) = .eq → x - m = 1/2
      have h_eq : x - (m : ℝ) = 1/2 := compare_eq_iff_eq.mp hc
      have h_eq' : x - ((m : ℤ) : ℝ) = 1/2 := by push_cast; exact h_eq
      rw [if_neg (by linarith : ¬ x - ((m : ℤ) : ℝ) < 1/2),
          if_neg (by linarith : ¬ 1/2 < x - ((m : ℤ) : ℝ))]
      cases hc' : choice m
      · simp [cond_incr, round_N, hc', h_ceil]
      · simp [cond_incr, round_N, hc', h_ceil]
    · -- c = .gt: compare (x - m) (1/2) = .gt → 1/2 < x - m
      have h_gt : 1/2 < x - (m : ℝ) := compare_gt_iff_gt.mp hc
      have h_gt' : 1/2 < x - ((m : ℤ) : ℝ) := by push_cast; exact h_gt
      rw [if_neg (by linarith : ¬ x - ((m : ℤ) : ℝ) < 1/2), if_pos h_gt']
      rw [h_ceil]
      simp [cond_incr, round_N]

theorem inbetween_int_N_sign (choice : ℤ → Bool) {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m |x| l) :
    Znearest choice x =
      cond_Zopp (decide (x < 0))
        (cond_incr (round_N
          (if (decide (x < 0) : Bool) then !(choice (-(m + 1))) else choice m) l) m) := by
  rcases lt_or_ge x 0 with hx | hx
  · have h_dec : decide (x < 0) = true := by simp [hx]
    rw [h_dec, cond_Zopp_true]
    have h_abs : |x| = -x := abs_of_neg hx
    rw [h_abs] at Hl
    -- Use Znearest_opp: Znearest choice x = -(Znearest (fun t => !choice (-(t+1))) (-x))
    have h_x_eq : x = -(-x) := by ring
    rw [h_x_eq, Znearest_opp]
    -- Now apply inbetween_int_N to (-x)
    rw [inbetween_int_N (fun t => !choice (-(t+1))) Hl]
    simp
  · have hxn : ¬ x < 0 := not_lt.mpr hx
    have h_dec : decide (x < 0) = false := by simp [hxn]
    rw [h_dec, cond_Zopp_false]
    have h_abs : |x| = x := abs_of_nonneg hx
    rw [h_abs] at Hl
    rw [inbetween_int_N choice Hl]
    simp

/-! ## Round-to-nearest-even (NE) -/

theorem inbetween_int_NE {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m x l) :
    ZnearestE x = cond_incr (round_N (decide (¬ Even m)) l) m := by
  unfold ZnearestE
  exact inbetween_int_N (fun n => decide (¬ Even n)) Hl

theorem inbetween_float_NE {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_float beta m (cexp beta fexp x) x l) :
    round beta fexp ZnearestE x =
      F2R (beta := beta) ⟨cond_incr (round_N (decide (¬ Even m)) l) m, cexp beta fexp x⟩ :=
  inbetween_float_round beta fexp ZnearestE
    (fun m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE h) Hl

theorem inbetween_int_NE_sign {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m |x| l) :
    ZnearestE x =
      cond_Zopp (decide (x < 0)) (cond_incr (round_N (decide (¬ Even m)) l) m) := by
  unfold ZnearestE
  rw [inbetween_int_N_sign (fun n => decide (¬ Even n)) Hl]
  -- Show inner choices match.
  by_cases h : x < 0
  · have h_inner_eq : (! decide (¬ Even (-(m + 1)))) = decide (¬ Even m) := by
      by_cases hm : Even m
      · have h1 : ¬ Even (-(m + 1)) := by
          rw [even_neg]; simp only [Int.even_iff]
          rcases hm with ⟨k, rfl⟩; omega
        have hd1 : decide (¬ Even (-(m + 1))) = true := decide_eq_true h1
        have hd2 : decide (¬ Even m) = false := decide_eq_false (not_not_intro hm)
        rw [hd1, hd2]; rfl
      · have h1 : Even (-(m + 1)) := by
          rw [even_neg]
          rw [Int.not_even_iff_odd] at hm
          rcases hm with ⟨k, rfl⟩
          exact ⟨k + 1, by ring⟩
        have hd1 : decide (¬ Even (-(m + 1))) = false := decide_eq_false (not_not_intro h1)
        have hd2 : decide (¬ Even m) = true := decide_eq_true hm
        rw [hd1, hd2]; rfl
    simp only [h, decide_true, ↓reduceIte, cond_Zopp_true, h_inner_eq]
  · -- x ≥ 0: outer if false → choose else branch (decide (¬ Even m))
    have hd : decide (x < 0) = false := by simp [h]
    rw [hd]
    simp

theorem inbetween_float_NE_sign {x : ℝ} {m : ℤ} {l : location}
    (Hx : inbetween_float beta m (cexp beta fexp x) |x| l) :
    round beta fexp ZnearestE x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (cond_incr (round_N (decide (¬ Even m)) l) m),
         cexp beta fexp x⟩ :=
  inbetween_float_round_sign beta fexp ZnearestE
    (fun _ m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE_sign h) Hx

/-! ## Round-to-nearest-away (NA) -/

theorem inbetween_int_NA {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m x l) :
    ZnearestA x = cond_incr (round_N (decide (0 ≤ m)) l) m := by
  unfold ZnearestA
  exact inbetween_int_N (fun n => decide (0 ≤ n)) Hl

theorem inbetween_float_NA {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_float beta m (cexp beta fexp x) x l) :
    round beta fexp ZnearestA x = F2R (beta := beta)
      ⟨cond_incr (round_N (decide (0 ≤ m)) l) m, cexp beta fexp x⟩ :=
  inbetween_float_round beta fexp ZnearestA
    (fun m l => cond_incr (round_N (decide (0 ≤ m)) l) m)
    (fun _ _ _ h => inbetween_int_NA h) Hl

theorem inbetween_int_NA_sign {x : ℝ} {m : ℤ} {l : location}
    (Hl : inbetween_int m |x| l) :
    ZnearestA x = cond_Zopp (decide (x < 0)) (cond_incr (round_N true l) m) := by
  unfold ZnearestA
  rw [inbetween_int_N_sign (fun n => decide (0 ≤ n)) Hl]
  -- Show: 0 ≤ m (from |x| < m+1 with |x| ≥ 0).
  have h_bounds := inbetween_bounds (Hdu := by push_cast; linarith) Hl
  have h_mp1_pos : 0 < ((m + 1 : ℤ) : ℝ) := lt_of_le_of_lt (abs_nonneg x) h_bounds.2
  have h_m_nn_int : 0 ≤ m := by
    have : (0 : ℤ) < m + 1 := by exact_mod_cast h_mp1_pos
    omega
  by_cases h : x < 0
  · have h_inner_eq : (! decide (0 ≤ -(m + 1))) = true := by
      have h1 : decide (0 ≤ -(m + 1)) = false := decide_eq_false (by omega)
      rw [h1]; rfl
    simp only [h, decide_true, ↓reduceIte, cond_Zopp_true, h_inner_eq]
  · have hd : decide (x < 0) = false := by simp [h]
    rw [hd]
    have hd2 : decide (0 ≤ m) = true := decide_eq_true h_m_nn_int
    simp [hd2]

theorem inbetween_float_NA_sign {x : ℝ} {m : ℤ} {l : location}
    (Hx : inbetween_float beta m (cexp beta fexp x) |x| l) :
    round beta fexp ZnearestA x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (cond_incr (round_N true l) m),
         cexp beta fexp x⟩ :=
  inbetween_float_round_sign beta fexp ZnearestA
    (fun _ m l => cond_incr (round_N true l) m)
    (fun _ _ _ h => inbetween_int_NA_sign h) Hx

/-! ## truncate: bring (m, e, l) to canonical exponent

Given a triple representing a bracketing `(m, e, l)`, produce a triple with
canonical exponent. -/

/-- Auxiliary: shift the triple `(m, e, l)` by `k` positions of the radix. -/
def truncate_aux (k : ℤ) (t : ℤ × ℤ × location) : ℤ × ℤ × location :=
  (t.1 / beta.val ^ k.toNat, t.2.1 + k,
   new_location (beta.val ^ k.toNat) (t.1 % beta.val ^ k.toNat) t.2.2)

/-- `truncate t = if k = fexp(Zdigits m + e) - e > 0, shift by k, else t`.
This brings the triple to canonical exponent (or leaves it alone). -/
noncomputable def truncate (t : ℤ × ℤ × location) : ℤ × ℤ × location :=
  if 0 < fexp (Zdigits beta t.1 + t.2.1) - t.2.1
    then truncate_aux beta (fexp (Zdigits beta t.1 + t.2.1) - t.2.1) t
    else t

theorem truncate_0 (e : ℤ) (l : location) :
    (truncate beta fexp (0, e, l)).1 = 0 := by
  unfold truncate truncate_aux
  split_ifs with hk
  · simp [Int.zero_ediv]
  · rfl

/-- The shift form is correct: when we shift by `k > 0`, the new triple
brackets `x` at the new exponent. -/
theorem truncate_correct_partial' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 < x)
    (H1 : inbetween_float beta m e x l) (H2 : e ≤ cexp beta fexp x) :
    let t' := truncate beta fexp (m, e, l)
    inbetween_float beta t'.1 t'.2.1 x t'.2.2 ∧ t'.2.1 = cexp beta fexp x := by
  have h_cexp : cexp beta fexp x = fexp (Zdigits beta m + e) :=
    cexp_inbetween_float beta fexp hValid Hx H1 (Or.inl H2)
  show inbetween_float beta (truncate beta fexp (m, e, l)).1
        (truncate beta fexp (m, e, l)).2.1 x (truncate beta fexp (m, e, l)).2.2 ∧
      (truncate beta fexp (m, e, l)).2.1 = cexp beta fexp x
  unfold truncate
  show inbetween_float beta
        (if 0 < fexp (Zdigits beta (m, e, l).1 + (m, e, l).2.1) - (m, e, l).2.1
         then truncate_aux beta _ (m, e, l) else (m, e, l)).1
        _ x _ ∧ _ = _
  rw [show ((m, e, l).1 : ℤ) = m from rfl, show ((m, e, l).2.1 : ℤ) = e from rfl,
      show fexp (Zdigits beta m + e) = cexp beta fexp x from h_cexp.symm]
  by_cases hk : 0 < cexp beta fexp x - e
  · simp only [if_pos hk, truncate_aux]
    refine ⟨?_, ?_⟩
    · show inbetween_float beta _ _ x _
      exact inbetween_float_new_location m e x l _ hk H1
    · show e + (cexp beta fexp x - e) = cexp beta fexp x; ring
  · simp only [if_neg hk]
    have h_e_eq : e = cexp beta fexp x := by
      simp at hk; omega
    exact ⟨H1, h_e_eq⟩

theorem truncate_correct_partial {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 < x)
    (H1 : inbetween_float beta m e x l) (H2 : e ≤ fexp (Zdigits beta m + e)) :
    let t' := truncate beta fexp (m, e, l)
    inbetween_float beta t'.1 t'.2.1 x t'.2.2 ∧ t'.2.1 = cexp beta fexp x := by
  apply truncate_correct_partial' beta fexp hValid Hx H1
  rw [cexp_inbetween_float beta fexp hValid Hx H1 (Or.inr H2)]
  exact H2

/-- The full correctness theorem (positive-cexp case): when `0 ≤ x` is
bracketed by `(m, e, l)` with `e ≤ cexp x ∨ l = Exact`, `truncate` produces
a valid bracketing whose exponent is `cexp x` (or, if exact, `x` is in format). -/
theorem truncate_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (H1 : inbetween_float beta m e x l)
    (H2 : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    let t' := truncate beta fexp (m, e, l)
    inbetween_float beta t'.1 t'.2.1 x t'.2.2 ∧
    (t'.2.1 = cexp beta fexp x ∨ (t'.2.2 = location.Exact ∧ generic_format beta fexp x)) := by
  rcases lt_or_eq_of_le Hx with hpx | hpx
  · rcases le_or_gt e (fexp (Zdigits beta m + e)) with H3 | H3
    · have h := truncate_correct_partial beta fexp hValid hpx H1 H3
      exact ⟨h.1, Or.inl h.2⟩
    · rcases H2 with H2 | H2
      · have h := truncate_correct_partial' beta fexp hValid hpx H1 H2
        exact ⟨h.1, Or.inl h.2⟩
      · -- l = Exact case
        unfold truncate
        have hk : ¬ 0 < fexp (Zdigits beta m + e) - e := by omega
        simp only [if_neg hk]
        refine ⟨H1, Or.inr ⟨H2, ?_⟩⟩
        rcases H1 with hE | _
        · rw [show x = F2R (beta := beta) ⟨m, e⟩ from hE]
          apply generic_format_F2R
          intro Hm
          show fexp (mag beta (F2R (beta := beta) ⟨m, e⟩)) ≤ e
          rw [mag_F2R_Zdigits m e Hm]
          omega
        · -- Inexact contradicts l = Exact
          exact location.noConfusion H2
  · -- x = 0
    have h_x_eq : x = 0 := hpx.symm
    rcases H1 with hE | ⟨c, h_lo, h_hi, _⟩
    · -- l = Exact, x = 0 = F2R⟨m, e⟩, so m = 0
      have h_zero : F2R (beta := beta) ⟨m, e⟩ = 0 := by rw [← hE, h_x_eq]
      have hm0 : m = 0 := by
        have h_m_real : (m : ℝ) = 0 := by
          have h_bpow_pos : 0 < bpow beta e := bpow_gt_0 beta e
          have h := h_zero
          show (m : ℝ) = 0
          have : (m : ℝ) * bpow beta e = 0 := h
          have h_ne : bpow beta e ≠ 0 := ne_of_gt h_bpow_pos
          exact (mul_eq_zero.mp this).resolve_right h_ne
        exact_mod_cast h_m_real
      subst hm0
      unfold truncate
      have hZdig : Zdigits beta 0 = 0 := Zdigits_zero beta
      simp only [hZdig, zero_add]
      have h_new_loc_zero : ∀ (p : ℤ), new_location p 0 location.Exact = location.Exact := by
        intro p
        unfold new_location
        by_cases h_even : p % 2 = 0
        · rw [if_pos h_even]
          show (if (0 : ℤ) = 0
                then match (location.Exact : location) with | .Exact => .Exact | _ => .Inexact .lt
                else _) = location.Exact
          rw [if_pos rfl]
        · rw [if_neg h_even]
          show (if (0 : ℤ) = 0
                then match (location.Exact : location) with | .Exact => .Exact | _ => .Inexact .lt
                else _) = location.Exact
          rw [if_pos rfl]
      by_cases hk : 0 < fexp e - e
      · simp only [if_pos hk, truncate_aux]
        refine ⟨?_, ?_⟩
        · -- Goal: inbetween_float β (0/p) (e+k) x (new_location p (0%p) Exact)
          rw [Int.zero_ediv, Int.zero_emod, h_new_loc_zero]
          exact .Exact (by rw [h_x_eq, F2R_0])
        · right
          refine ⟨?_, ?_⟩
          · -- Goal: new_location p (0%p) Exact = Exact
            rw [Int.zero_emod]; exact h_new_loc_zero _
          · rw [h_x_eq]; exact generic_format_0 beta fexp
      · simp only [if_neg hk]
        refine ⟨?_, ?_⟩
        · exact .Exact hE
        · right
          refine ⟨?_, ?_⟩
          · trivial
          · rw [h_x_eq]; exact generic_format_0 beta fexp
    · -- Inexact with x = 0: contradiction
      rw [h_x_eq] at h_lo h_hi
      have h_m_lt : m < 0 := lt_0_F2R h_lo
      have h_mp1_pos : 0 < m + 1 := gt_0_F2R h_hi
      omega

/-- The full correctness theorem (Zdigits-condition variant). -/
theorem truncate_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (H1 : inbetween_float beta m e x l)
    (H2 : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    let t' := truncate beta fexp (m, e, l)
    inbetween_float beta t'.1 t'.2.1 x t'.2.2 ∧
    (t'.2.1 = cexp beta fexp x ∨ (t'.2.2 = location.Exact ∧ generic_format beta fexp x)) := by
  apply truncate_correct' beta fexp hValid Hx H1
  exact (cexp_inbetween_float_loc_Exact beta fexp hValid Hx H1).mpr H2

/-! ## Generic correctness theorems

Combining `inbetween_float_round` with `truncate_correct` gives generic
correctness theorems that any rounding can plug into. -/

theorem round_any_correct (rnd : ℝ → ℤ) [Valid_rnd rnd] (choice : ℤ → location → ℤ)
    (inbetween_int_valid :
      ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m x l → rnd x = choice m l)
    {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e x l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp rnd x = F2R (beta := beta) ⟨choice m l, e⟩ := by
  rcases He with He | ⟨Hl, Hf⟩
  · subst He
    exact inbetween_float_round beta fexp rnd choice inbetween_int_valid Hin
  · subst Hl
    rcases Hin with hExact | ⟨c, _, _, _⟩
    · rw [show x = F2R (beta := beta) ⟨m, e⟩ from hExact] at Hf ⊢
      have h_choice : choice m location.Exact = m := by
        have := inbetween_int_valid (m : ℝ) m location.Exact (.Exact rfl)
        have h_rnd_m : rnd ((m : ℤ) : ℝ) = m := Valid_rnd.Zrnd_intCast m
        rw [h_rnd_m] at this
        exact this.symm
      rw [h_choice]
      exact round_generic beta fexp rnd Hf

theorem round_trunc_any_correct' (rnd : ℝ → ℤ) [Valid_rnd rnd] (choice : ℤ → location → ℤ)
    (inbetween_int_valid :
      ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m x l → rnd x = choice m l)
    {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp rnd x =
      F2R (beta := beta)
        ⟨choice (truncate beta fexp (m, e, l)).1 (truncate beta fexp (m, e, l)).2.2,
         (truncate beta fexp (m, e, l)).2.1⟩ := by
  have h := truncate_correct' beta fexp hValid Hx Hin He
  exact round_any_correct beta fexp rnd choice inbetween_int_valid h.1
    (h.2.imp_right (fun ⟨h1, h2⟩ => ⟨h1, h2⟩))

theorem round_trunc_any_correct (rnd : ℝ → ℤ) [Valid_rnd rnd] (choice : ℤ → location → ℤ)
    (inbetween_int_valid :
      ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m x l → rnd x = choice m l)
    {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp rnd x =
      F2R (beta := beta)
        ⟨choice (truncate beta fexp (m, e, l)).1 (truncate beta fexp (m, e, l)).2.2,
         (truncate beta fexp (m, e, l)).2.1⟩ := by
  have h := truncate_correct beta fexp hValid Hx Hin He
  exact round_any_correct beta fexp rnd choice inbetween_int_valid h.1
    (h.2.imp_right (fun ⟨h1, h2⟩ => ⟨h1, h2⟩))

/-- Sign-aware generic correctness: when `rnd` is `cond_Zopp`-symmetric over
the integer level, the rounding equals the corresponding signed F2R. -/
theorem round_sign_any_correct (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (choice : Bool → ℤ → location → ℤ)
    (inbetween_int_valid :
      ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m |x| l →
        rnd x = cond_Zopp (decide (x < 0)) (choice (decide (x < 0)) m l))
    {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e |x| l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp rnd x =
      F2R (beta := beta) ⟨cond_Zopp (decide (x < 0)) (choice (decide (x < 0)) m l), e⟩ := by
  rcases He with He | ⟨Hl, Hf⟩
  · subst He
    exact inbetween_float_round_sign beta fexp rnd choice inbetween_int_valid Hin
  · subst Hl
    rcases Hin with hExact | ⟨c, _, _, _⟩
    · -- |x| = F2R ⟨m, e⟩
      have h_round_x : round beta fexp rnd x = x := round_generic beta fexp rnd Hf
      have h_x_abs : |x| = F2R (beta := beta) ⟨m, e⟩ := hExact
      -- m ≥ 0 from |x| ≥ 0 and bpow > 0.
      have h_bpow_pos : 0 < bpow beta e := bpow_gt_0 _ _
      have h_m_nn : 0 ≤ m := by
        have h_abs_nn : 0 ≤ F2R (beta := beta) ⟨m, e⟩ := h_x_abs ▸ abs_nonneg x
        show 0 ≤ m
        have h_m_real_nn : 0 ≤ ((m : ℤ) : ℝ) := by
          have : 0 ≤ ((m : ℤ) : ℝ) * bpow beta e := h_abs_nn
          nlinarith
        exact_mod_cast h_m_real_nn
      -- Helper: choice false m Exact = m.
      have h_choice_false : choice false m location.Exact = m := by
        have h_rnd_m : rnd ((m : ℤ) : ℝ) = m := Valid_rnd.Zrnd_intCast m
        have h_m_real_nn : 0 ≤ ((m : ℤ) : ℝ) := by exact_mod_cast h_m_nn
        have h_abs_m : |((m : ℤ) : ℝ)| = ((m : ℤ) : ℝ) := abs_of_nonneg h_m_real_nn
        have h_in : inbetween_int m |((m : ℤ) : ℝ)| location.Exact := by
          rw [h_abs_m]; exact .Exact rfl
        have h_iv := inbetween_int_valid ((m : ℤ) : ℝ) m location.Exact h_in
        have h_dec : decide (((m : ℤ) : ℝ) < 0) = false := by
          rw [decide_eq_false_iff_not]; push_neg; exact h_m_real_nn
        rw [h_dec, h_rnd_m] at h_iv
        exact h_iv.symm
      by_cases hx_neg : x < 0
      · -- x < 0: x = -|x| = -F2R ⟨m, e⟩.
        have h_x_eq : x = -F2R (beta := beta) ⟨m, e⟩ := by
          rw [← h_x_abs, abs_of_neg hx_neg, neg_neg]
        -- m > 0 since x < 0 implies |x| > 0 implies F2R > 0 implies m > 0.
        have h_x_abs_pos : 0 < F2R (beta := beta) ⟨m, e⟩ := by
          rw [← h_x_abs]; exact abs_pos.mpr (ne_of_lt hx_neg)
        have h_m_pos : 0 < m := by
          have h_m_real_pos : 0 < ((m : ℤ) : ℝ) := by
            have : 0 < ((m : ℤ) : ℝ) * bpow beta e := h_x_abs_pos
            nlinarith
          exact_mod_cast h_m_real_pos
        -- choice true m Exact = m.
        have h_choice_true : choice true m location.Exact = m := by
          have h_m_pos_real : (0 : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast h_m_pos
          have h_neg_m_neg : ((-m : ℤ) : ℝ) < 0 := by push_cast; linarith
          have h_rnd_neg_m : rnd ((-m : ℤ) : ℝ) = (-m : ℤ) := Valid_rnd.Zrnd_intCast (-m)
          have h_abs_neg_m : |((-m : ℤ) : ℝ)| = ((m : ℤ) : ℝ) := by
            rw [abs_of_neg h_neg_m_neg]; push_cast; ring
          have h_in : inbetween_int m |((-m : ℤ) : ℝ)| location.Exact := by
            rw [h_abs_neg_m]; exact .Exact rfl
          have h_iv := inbetween_int_valid ((-m : ℤ) : ℝ) m location.Exact h_in
          have h_dec : decide (((-m : ℤ) : ℝ) < 0) = true := by
            rw [decide_eq_true_iff]; exact h_neg_m_neg
          rw [h_dec, h_rnd_neg_m] at h_iv
          have : -m = -(choice true m location.Exact) := h_iv
          omega
        have h_dec_x : decide (x < 0) = true := by
          rw [decide_eq_true_iff]; exact hx_neg
        rw [h_dec_x, h_choice_true]
        rw [h_round_x, h_x_eq]
        have h_cZ : cond_Zopp true m = -m := rfl
        rw [h_cZ, F2R_Zopp]
      · -- x ≥ 0: x = |x| = F2R ⟨m, e⟩.
        push_neg at hx_neg
        have h_x_eq : x = F2R (beta := beta) ⟨m, e⟩ := by
          rw [← h_x_abs, abs_of_nonneg hx_neg]
        have h_dec_x : decide (x < 0) = false := by
          rw [decide_eq_false_iff_not]; push_neg; exact hx_neg
        rw [h_dec_x, h_choice_false]
        rw [h_round_x, h_x_eq]
        rfl

/-- Truncating then applying the sign-aware rounding gives the same result. -/
theorem round_trunc_sign_any_correct' (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (choice : Bool → ℤ → location → ℤ)
    (inbetween_int_valid :
      ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m |x| l →
        rnd x = cond_Zopp (decide (x < 0)) (choice (decide (x < 0)) m l))
    {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp rnd x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (choice (decide (x < 0)) (truncate beta fexp (m, e, l)).1
            (truncate beta fexp (m, e, l)).2.2),
         (truncate beta fexp (m, e, l)).2.1⟩ := by
  rw [← cexp_abs] at He
  have h := truncate_correct' beta fexp hValid (abs_nonneg _) Hin He
  apply round_sign_any_correct beta fexp rnd choice inbetween_int_valid h.1
  rcases h.2 with h2 | ⟨h2a, h2b⟩
  · left; rwa [← cexp_abs]
  · right; exact ⟨h2a, generic_format_abs_inv beta fexp h2b⟩

/-- The `Zdigits`-shaped variant. -/
theorem round_trunc_sign_any_correct (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (choice : Bool → ℤ → location → ℤ)
    (inbetween_int_valid :
      ∀ (x : ℝ) (m : ℤ) (l : location), inbetween_int m |x| l →
        rnd x = cond_Zopp (decide (x < 0)) (choice (decide (x < 0)) m l))
    {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp rnd x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (choice (decide (x < 0)) (truncate beta fexp (m, e, l)).1
            (truncate beta fexp (m, e, l)).2.2),
         (truncate beta fexp (m, e, l)).2.1⟩ := by
  apply round_trunc_sign_any_correct' beta fexp rnd choice inbetween_int_valid hValid Hin
  rw [← cexp_abs]
  exact (cexp_inbetween_float_loc_Exact beta fexp hValid (abs_nonneg _) Hin).mpr He

/-! ### Per-mode correctness aliases

Specializations of the generic correctness theorems to the standard
rounding modes. Each is a one-line application. -/

/-- Round-down (floor) correctness. -/
theorem round_DN_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e x l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp Int.floor x = F2R (beta := beta) ⟨m, e⟩ :=
  round_any_correct beta fexp Int.floor (fun m _ => m)
    (fun _ _ _ h => inbetween_int_DN h) Hin He

/-- Round-up (ceiling) correctness. -/
theorem round_UP_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e x l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp Int.ceil x =
      F2R (beta := beta) ⟨cond_incr (round_UP l) m, e⟩ :=
  round_any_correct beta fexp Int.ceil (fun m l => cond_incr (round_UP l) m)
    (fun _ _ _ h => inbetween_int_UP h) Hin He

/-- Round-toward-zero (truncation) correctness. -/
theorem round_ZR_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e x l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp Ztrunc x =
      F2R (beta := beta) ⟨cond_incr (round_ZR (decide (m < 0)) l) m, e⟩ :=
  round_any_correct beta fexp Ztrunc (fun m l => cond_incr (round_ZR (decide (m < 0)) l) m)
    (fun _ _ _ h => inbetween_int_ZR h) Hin He

/-- Round-to-nearest-even (IEEE default) correctness. -/
theorem round_NE_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e x l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp ZnearestE x =
      F2R (beta := beta) ⟨cond_incr (round_N (decide (¬ Even m)) l) m, e⟩ :=
  round_any_correct beta fexp ZnearestE
    (fun m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE h) Hin He

/-- Round-to-nearest-away (ties-away-from-zero) correctness. -/
theorem round_NA_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e x l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp ZnearestA x =
      F2R (beta := beta) ⟨cond_incr (round_N (decide (0 ≤ m)) l) m, e⟩ :=
  round_any_correct beta fexp ZnearestA
    (fun m l => cond_incr (round_N (decide (0 ≤ m)) l) m)
    (fun _ _ _ h => inbetween_int_NA h) Hin He

/-! ### Truncate-then-round per-mode aliases (Zdigits form) -/

/-- Round-down via truncate. -/
theorem round_trunc_DN_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp Int.floor x =
      F2R (beta := beta)
        ⟨(truncate beta fexp (m, e, l)).1, (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct beta fexp Int.floor (fun m _ => m)
    (fun _ _ _ h => inbetween_int_DN h) hValid Hx Hin He

/-- Round-up via truncate. -/
theorem round_trunc_UP_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp Int.ceil x =
      F2R (beta := beta)
        ⟨cond_incr (round_UP (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct beta fexp Int.ceil (fun m l => cond_incr (round_UP l) m)
    (fun _ _ _ h => inbetween_int_UP h) hValid Hx Hin He

/-- Round-toward-zero via truncate. -/
theorem round_trunc_ZR_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp Ztrunc x =
      F2R (beta := beta)
        ⟨cond_incr (round_ZR (decide ((truncate beta fexp (m, e, l)).1 < 0))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct beta fexp Ztrunc
    (fun m l => cond_incr (round_ZR (decide (m < 0)) l) m)
    (fun _ _ _ h => inbetween_int_ZR h) hValid Hx Hin He

/-- Round-to-nearest-even via truncate (IEEE default). -/
theorem round_trunc_NE_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp ZnearestE x =
      F2R (beta := beta)
        ⟨cond_incr (round_N (decide (¬ Even (truncate beta fexp (m, e, l)).1))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct beta fexp ZnearestE
    (fun m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE h) hValid Hx Hin He

/-- Round-to-nearest-away via truncate. -/
theorem round_trunc_NA_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp ZnearestA x =
      F2R (beta := beta)
        ⟨cond_incr (round_N (decide (0 ≤ (truncate beta fexp (m, e, l)).1))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct beta fexp ZnearestA
    (fun m l => cond_incr (round_N (decide (0 ≤ m)) l) m)
    (fun _ _ _ h => inbetween_int_NA h) hValid Hx Hin He

/-! ### Truncate-then-round per-mode aliases (cexp form, primed) -/

/-- Round-down via truncate (cexp form). -/
theorem round_trunc_DN_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp Int.floor x =
      F2R (beta := beta)
        ⟨(truncate beta fexp (m, e, l)).1, (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct' beta fexp Int.floor (fun m _ => m)
    (fun _ _ _ h => inbetween_int_DN h) hValid Hx Hin He

/-- Round-up via truncate (cexp form). -/
theorem round_trunc_UP_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp Int.ceil x =
      F2R (beta := beta)
        ⟨cond_incr (round_UP (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct' beta fexp Int.ceil (fun m l => cond_incr (round_UP l) m)
    (fun _ _ _ h => inbetween_int_UP h) hValid Hx Hin He

/-- Round-toward-zero via truncate (cexp form). -/
theorem round_trunc_ZR_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp Ztrunc x =
      F2R (beta := beta)
        ⟨cond_incr (round_ZR (decide ((truncate beta fexp (m, e, l)).1 < 0))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct' beta fexp Ztrunc
    (fun m l => cond_incr (round_ZR (decide (m < 0)) l) m)
    (fun _ _ _ h => inbetween_int_ZR h) hValid Hx Hin He

/-- Round-to-nearest-even via truncate (cexp form). -/
theorem round_trunc_NE_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp ZnearestE x =
      F2R (beta := beta)
        ⟨cond_incr (round_N (decide (¬ Even (truncate beta fexp (m, e, l)).1))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct' beta fexp ZnearestE
    (fun m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE h) hValid Hx Hin He

/-- Round-to-nearest-away via truncate (cexp form). -/
theorem round_trunc_NA_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp) (Hx : 0 ≤ x)
    (Hin : inbetween_float beta m e x l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp ZnearestA x =
      F2R (beta := beta)
        ⟨cond_incr (round_N (decide (0 ≤ (truncate beta fexp (m, e, l)).1))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_any_correct' beta fexp ZnearestA
    (fun m l => cond_incr (round_N (decide (0 ≤ m)) l) m)
    (fun _ _ _ h => inbetween_int_NA h) hValid Hx Hin He

/-! ### Sign-aware per-mode aliases -/

/-- Sign-aware round-down. -/
theorem round_sign_DN_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e |x| l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp Int.floor x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_sign_DN (decide (x < 0)) l) m), e⟩ :=
  round_sign_any_correct beta fexp Int.floor
    (fun s m l => cond_incr (round_sign_DN s l) m)
    (fun _ _ _ h => inbetween_int_DN_sign h) Hin He

/-- Sign-aware round-up. -/
theorem round_sign_UP_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e |x| l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp Int.ceil x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_sign_UP (decide (x < 0)) l) m), e⟩ :=
  round_sign_any_correct beta fexp Int.ceil
    (fun s m l => cond_incr (round_sign_UP s l) m)
    (fun _ _ _ h => inbetween_int_UP_sign h) Hin He

/-- Sign-aware round-toward-zero. -/
theorem round_sign_ZR_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e |x| l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp Ztrunc x =
      F2R (beta := beta) ⟨cond_Zopp (decide (x < 0)) m, e⟩ :=
  round_sign_any_correct beta fexp Ztrunc (fun _ m _ => m)
    (fun _ _ _ h => inbetween_int_ZR_sign h) Hin He

/-- Sign-aware round-to-nearest-even (IEEE default). -/
theorem round_sign_NE_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e |x| l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp ZnearestE x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_N (decide (¬ Even m)) l) m), e⟩ :=
  round_sign_any_correct beta fexp ZnearestE
    (fun _ m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE_sign h) Hin He

/-- Sign-aware round-to-nearest-away. -/
theorem round_sign_NA_correct {x : ℝ} {m e : ℤ} {l : location}
    (Hin : inbetween_float beta m e |x| l)
    (He : e = cexp beta fexp x ∨ (l = location.Exact ∧ generic_format beta fexp x)) :
    round beta fexp ZnearestA x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (cond_incr (round_N true l) m), e⟩ :=
  round_sign_any_correct beta fexp ZnearestA
    (fun _ m l => cond_incr (round_N true l) m)
    (fun _ _ _ h => inbetween_int_NA_sign h) Hin He

/-! ### Truncate + sign per-mode aliases (Zdigits form) -/

/-- Sign-aware round-down via truncate. -/
theorem round_trunc_sign_DN_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp Int.floor x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_sign_DN (decide (x < 0)) (truncate beta fexp (m, e, l)).2.2)
            (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct beta fexp Int.floor
    (fun s m l => cond_incr (round_sign_DN s l) m)
    (fun _ _ _ h => inbetween_int_DN_sign h) hValid Hin He

/-- Sign-aware round-up via truncate. -/
theorem round_trunc_sign_UP_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp Int.ceil x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_sign_UP (decide (x < 0)) (truncate beta fexp (m, e, l)).2.2)
            (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct beta fexp Int.ceil
    (fun s m l => cond_incr (round_sign_UP s l) m)
    (fun _ _ _ h => inbetween_int_UP_sign h) hValid Hin He

/-- Sign-aware round-toward-zero via truncate. -/
theorem round_trunc_sign_ZR_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp Ztrunc x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct beta fexp Ztrunc (fun _ m _ => m)
    (fun _ _ _ h => inbetween_int_ZR_sign h) hValid Hin He

/-- Sign-aware round-to-nearest-even via truncate. -/
theorem round_trunc_sign_NE_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp ZnearestE x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_N (decide (¬ Even (truncate beta fexp (m, e, l)).1))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct beta fexp ZnearestE
    (fun _ m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE_sign h) hValid Hin He

/-- Sign-aware round-to-nearest-away via truncate. -/
theorem round_trunc_sign_NA_correct {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ fexp (Zdigits beta m + e) ∨ l = location.Exact) :
    round beta fexp ZnearestA x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_N true (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct beta fexp ZnearestA
    (fun _ m l => cond_incr (round_N true l) m)
    (fun _ _ _ h => inbetween_int_NA_sign h) hValid Hin He

/-! ### Truncate + sign per-mode aliases (cexp form, primed) -/

/-- Sign-aware round-down via truncate (cexp form). -/
theorem round_trunc_sign_DN_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp Int.floor x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_sign_DN (decide (x < 0)) (truncate beta fexp (m, e, l)).2.2)
            (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct' beta fexp Int.floor
    (fun s m l => cond_incr (round_sign_DN s l) m)
    (fun _ _ _ h => inbetween_int_DN_sign h) hValid Hin He

/-- Sign-aware round-up via truncate (cexp form). -/
theorem round_trunc_sign_UP_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp Int.ceil x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_sign_UP (decide (x < 0)) (truncate beta fexp (m, e, l)).2.2)
            (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct' beta fexp Int.ceil
    (fun s m l => cond_incr (round_sign_UP s l) m)
    (fun _ _ _ h => inbetween_int_UP_sign h) hValid Hin He

/-- Sign-aware round-toward-zero via truncate (cexp form). -/
theorem round_trunc_sign_ZR_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp Ztrunc x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0)) (truncate beta fexp (m, e, l)).1,
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct' beta fexp Ztrunc (fun _ m _ => m)
    (fun _ _ _ h => inbetween_int_ZR_sign h) hValid Hin He

/-- Sign-aware round-to-nearest-even via truncate (cexp form). -/
theorem round_trunc_sign_NE_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp ZnearestE x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_N (decide (¬ Even (truncate beta fexp (m, e, l)).1))
            (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct' beta fexp ZnearestE
    (fun _ m l => cond_incr (round_N (decide (¬ Even m)) l) m)
    (fun _ _ _ h => inbetween_int_NE_sign h) hValid Hin He

/-- Sign-aware round-to-nearest-away via truncate (cexp form). -/
theorem round_trunc_sign_NA_correct' {x : ℝ} {m e : ℤ} {l : location}
    (hValid : Valid_exp fexp)
    (Hin : inbetween_float beta m e |x| l)
    (He : e ≤ cexp beta fexp x ∨ l = location.Exact) :
    round beta fexp ZnearestA x =
      F2R (beta := beta)
        ⟨cond_Zopp (decide (x < 0))
          (cond_incr (round_N true (truncate beta fexp (m, e, l)).2.2)
          (truncate beta fexp (m, e, l)).1),
         (truncate beta fexp (m, e, l)).2.1⟩ :=
  round_trunc_sign_any_correct' beta fexp ZnearestA
    (fun _ m l => cond_incr (round_N true l) m)
    (fun _ _ _ h => inbetween_int_NA_sign h) hValid Hin He

end Fcalc_round_fexp

/-! ## truncate for FIX formats -/

variable (beta : radix)

/-- The FIX-specific truncate: shift to the fixed exponent `emin`. -/
noncomputable def truncate_FIX (emin : ℤ) (t : ℤ × ℤ × location) : ℤ × ℤ × location :=
  if 0 < emin - t.2.1
    then (t.1 / beta.val ^ (emin - t.2.1).toNat, t.2.1 + (emin - t.2.1),
          new_location (beta.val ^ (emin - t.2.1).toNat)
            (t.1 % beta.val ^ (emin - t.2.1).toNat) t.2.2)
    else t

/-- Correctness of `truncate_FIX`: produces a triple bracketing `x` whose
exponent is `cexp_FIX x` (or `x` is in FIX format). -/
theorem truncate_FIX_correct (emin : ℤ) {x : ℝ} {m e : ℤ} {l : location}
    (H1 : inbetween_float beta m e x l)
    (H2 : e ≤ emin ∨ l = location.Exact) :
    let t' := truncate_FIX beta emin (m, e, l)
    inbetween_float beta t'.1 t'.2.1 x t'.2.2 ∧
    (t'.2.1 = cexp beta (FIX_exp emin) x ∨
     (t'.2.2 = location.Exact ∧ generic_format beta (FIX_exp emin) x)) := by
  show inbetween_float beta (truncate_FIX beta emin (m, e, l)).1
        (truncate_FIX beta emin (m, e, l)).2.1 x (truncate_FIX beta emin (m, e, l)).2.2 ∧
      _
  by_cases hk : 0 < emin - e
  · -- shift case
    have h_truncate_eq : truncate_FIX beta emin (m, e, l) =
        (m / beta.val ^ (emin - e).toNat, e + (emin - e),
         new_location (beta.val ^ (emin - e).toNat)
           (m % beta.val ^ (emin - e).toNat) l) := by
      unfold truncate_FIX
      simp only [if_pos hk]
    rw [h_truncate_eq]
    refine ⟨?_, ?_⟩
    · exact inbetween_float_new_location m e x l _ hk H1
    · left
      show e + (emin - e) = cexp beta (FIX_exp emin) x
      unfold cexp FIX_exp; ring
  · -- no shift
    have h_truncate_eq : truncate_FIX beta emin (m, e, l) = (m, e, l) := by
      unfold truncate_FIX
      simp only [if_neg hk]
    rw [h_truncate_eq]
    push_neg at hk
    have h_e_ge_emin : emin ≤ e := by omega
    refine ⟨H1, ?_⟩
    rcases H2 with H2 | H2
    · have h_e_eq : e = emin := by omega
      left
      show e = cexp beta (FIX_exp emin) x
      simp [cexp, FIX_exp, h_e_eq]
    · right
      refine ⟨H2, ?_⟩
      rcases H1 with hExact | _
      · rw [show x = F2R (beta := beta) ⟨m, e⟩ from hExact]
        apply generic_format_FIX
        refine ⟨⟨m * beta.val ^ (e - emin).toNat, emin⟩, ?_, rfl⟩
        exact F2R_change_exp emin m e h_e_ge_emin
      · exact location.noConfusion H2

end LeanFlocq
