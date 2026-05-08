/-
Port of `flocq/src/Core/FLT.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Floating-point format with gradual underflow: every value has a mantissa
bounded by `β^prec` and an exponent at least `emin`. The exponent function
is `max (e - prec) emin` — FLT behaves like FLX for large values and like
FIX (`emin`) for small ones.
-/

import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.FIX
import LeanFlocq.Core.FLX

namespace LeanFlocq

/-- A real `x` is in the FLT format with parameters `(emin, prec)` if
`x = F2R ⟨m, e⟩` for some mantissa `m` with `|m| < β^prec` and exponent
`e ≥ emin`. -/
def FLT_format (beta : radix) (emin prec : ℤ) (x : ℝ) : Prop :=
  ∃ f : float beta,
    x = F2R f ∧ |f.Fnum| < (beta.val : ℤ) ^ prec.toNat ∧ emin ≤ f.Fexp

/-- The FLT exponent function: `max (e - prec) emin`. -/
def FLT_exp (emin prec : ℤ) : ℤ → ℤ := fun e => max (e - prec) emin

/-- `FLT_exp emin prec` is a `Valid_exp` whenever `0 < prec`. -/
theorem FLT_exp_valid (emin prec : ℤ) (hp : 0 < prec) :
    Valid_exp (FLT_exp emin prec) := by
  intro k
  unfold FLT_exp
  refine ⟨?_, ?_⟩
  · -- max (k - prec) emin < k → max (k+1 - prec) emin ≤ k
    intro hlt
    have h1 : k - prec < k := lt_of_le_of_lt (le_max_left _ _) hlt
    have h2 : emin < k := lt_of_le_of_lt (le_max_right _ _) hlt
    have hp' : 1 ≤ prec := hp
    exact max_le (by linarith) (by linarith)
  · -- k ≤ max (k - prec) emin → stabilization
    intro hge
    -- The first disjunct k ≤ k - prec is impossible, so emin ≥ k.
    have h_kle_emin : k ≤ emin := by
      rcases le_max_iff.mp hge with h1 | h2
      · linarith
      · exact h2
    -- max k emin = emin (since k ≤ emin).
    have h_max_eq : max (k - prec) emin = emin := by
      apply max_eq_right
      linarith
    rw [h_max_eq]
    refine ⟨?_, ?_⟩
    · -- max (emin + 1 - prec) emin ≤ emin
      apply max_le
      · linarith
      · exact le_refl _
    · -- For all l ≤ emin, max (l - prec) emin = emin.
      intro l hl
      apply max_eq_right
      linarith

/-- `FLT_exp emin prec` is monotone: it is the maximum of two monotone fns. -/
theorem FLT_exp_monotone (emin prec : ℤ) : Monotone_exp (FLT_exp emin prec) := by
  intro ex ey hxy
  unfold FLT_exp
  exact max_le_max (by linarith) (le_refl _)

/-- Every FLT-format real is in the generic format with `FLT_exp emin prec`. -/
theorem generic_format_FLT (beta : radix) (emin prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : FLT_format beta emin prec x) :
    generic_format beta (FLT_exp emin prec) x := by
  obtain ⟨⟨mx, ex⟩, hx, hb, he⟩ := h
  rw [hx]
  apply generic_format_F2R beta (FLT_exp emin prec) mx ex
  intro hmx_ne
  show FLT_exp emin prec (mag beta (F2R (beta := beta) ⟨mx, ex⟩)) ≤ ex
  unfold FLT_exp
  -- Need: max (mag - prec) emin ≤ ex.
  -- (1) mag - prec ≤ ex via |F2R| < bpow (ex + prec).
  -- (2) emin ≤ ex from the hypothesis.
  have h_F2R_ne : F2R (beta := beta) ⟨mx, ex⟩ ≠ 0 := by
    intro hz; exact hmx_ne (eq_0_F2R (beta := beta) hz)
  have hmx_real : (|(mx : ℝ)|) < bpow beta prec := by
    have hb_real : ((|mx| : ℤ) : ℝ) < ((beta.val ^ prec.toNat : ℤ) : ℝ) := by
      exact_mod_cast hb
    rw [show ((|mx| : ℤ) : ℝ) = |(mx : ℝ)| from by push_cast; rfl] at hb_real
    rwa [IZR_Zpower beta (le_of_lt hp)] at hb_real
  have h_abs_F2R : |F2R (beta := beta) ⟨mx, ex⟩| < bpow beta (ex + prec) := by
    unfold F2R
    show |(mx : ℝ) * bpow beta ex| < bpow beta (ex + prec)
    rw [abs_mul, abs_of_pos (bpow_gt_0 beta ex), bpow_plus, mul_comm (bpow beta ex) _]
    exact (mul_lt_mul_iff_of_pos_right (bpow_gt_0 beta ex)).mpr hmx_real
  have h_mag_le : mag beta (F2R (beta := beta) ⟨mx, ex⟩) ≤ ex + prec :=
    mag_le_bpow beta h_F2R_ne h_abs_F2R
  exact max_le (by linarith) he

/-- Every generic-format-with-`FLT_exp` real is in the FLT format. -/
theorem FLT_format_generic (beta : radix) (emin prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (h : generic_format beta (FLT_exp emin prec) x) :
    FLT_format beta emin prec x := by
  refine ⟨⟨Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x),
           cexp beta (FLT_exp emin prec) x⟩, h, ?_, ?_⟩
  · -- |Ztrunc(scaled_mantissa)| < β^prec
    show |Ztrunc (scaled_mantissa beta (FLT_exp emin prec) x)|
           < (beta.val : ℤ) ^ prec.toNat
    set sm := scaled_mantissa beta (FLT_exp emin prec) x with hsm_def
    -- |sm| < bpow prec via |x| < bpow(mag x) and cexp ≥ mag - prec.
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
        -- cexp ≥ mag - prec because cexp = max (mag - prec) emin.
        have h_cexp_ge : mag beta x - prec ≤ cexp beta (FLT_exp emin prec) x := by
          unfold cexp FLT_exp
          exact le_max_left _ _
        calc |x| * bpow beta (-cexp beta (FLT_exp emin prec) x)
            < bpow beta (mag beta x) * bpow beta (-cexp beta (FLT_exp emin prec) x) := by
              exact (mul_lt_mul_iff_of_pos_right (bpow_gt_0 beta _)).mpr h_mag
          _ = bpow beta (mag beta x + (-cexp beta (FLT_exp emin prec) x)) := by
              rw [← bpow_plus]
          _ ≤ bpow beta prec := by
              apply bpow_le; linarith
    have h_eq_sm : ((Ztrunc sm : ℤ) : ℝ) = sm := by
      have := scaled_mantissa_generic beta (FLT_exp emin prec) h
      rw [← hsm_def] at this
      exact this.symm
    have h_real : ((|Ztrunc sm| : ℤ) : ℝ) < ((beta.val ^ prec.toNat : ℤ) : ℝ) := by
      have h1 : ((|Ztrunc sm| : ℤ) : ℝ) = |((Ztrunc sm : ℤ) : ℝ)| := by push_cast; rfl
      rw [h1, h_eq_sm, IZR_Zpower beta (le_of_lt hp)]
      exact hsm_bound
    exact_mod_cast h_real
  · -- emin ≤ cexp = max (...) emin
    show emin ≤ cexp beta (FLT_exp emin prec) x
    unfold cexp FLT_exp
    exact le_max_right _ _

/-- The FLT format admits all the abstract round predicates from `Round_pred`. -/
theorem FLT_format_satisfies_any (beta : radix) (emin prec : ℤ) (hp : 0 < prec) :
    satisfies_any (FLT_format beta emin prec) := by
  refine satisfies_any_eq (F1 := generic_format beta (FLT_exp emin prec)) ?_
    (generic_format_satisfies_any beta (FLT_exp emin prec)
      (FLT_exp_valid emin prec hp))
  intro x
  exact ⟨FLT_format_generic beta emin prec hp, generic_format_FLT beta emin prec hp⟩

/-- `bpow e` is in the FLT format whenever `emin ≤ e`. -/
theorem FLT_format_bpow (beta : radix) (emin prec : ℤ) (hp : 0 < prec)
    (e : ℤ) (he : emin ≤ e) :
    generic_format beta (FLT_exp emin prec) (bpow beta e) := by
  apply generic_format_bpow beta (FLT_exp emin prec)
  unfold FLT_exp
  exact max_le (by linarith) he

/-! ### Links between FLT and FLX -/

/-- For values above the gradual-underflow threshold, FLT and FLX agree on
the canonical exponent. -/
theorem cexp_FLT_FLX (beta : radix) (emin prec : ℤ) {x : ℝ}
    (hx : bpow beta (emin + prec - 1) ≤ |x|) :
    cexp beta (FLT_exp emin prec) x = cexp beta (FLX_exp prec) x := by
  have hx_ne : x ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hx
    exact absurd hx (not_le.mpr (bpow_gt_0 beta _))
  have h_mag : emin + prec - 1 < mag beta x := mag_gt_bpow beta hx
  unfold cexp FLT_exp FLX_exp
  apply max_eq_left
  linarith

/-- An FLX-format value above the gradual-underflow threshold is FLT. -/
theorem generic_format_FLT_FLX (beta : radix) (emin prec : ℤ) {x : ℝ}
    (hx : bpow beta (emin + prec - 1) ≤ |x|)
    (h : generic_format beta (FLX_exp prec) x) :
    generic_format beta (FLT_exp emin prec) x := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact generic_format_0 beta (FLT_exp emin prec)
  · unfold generic_format scaled_mantissa
    rw [cexp_FLT_FLX beta emin prec hx]
    exact h

/-- An FLT-format value is always FLX (FLT is more restrictive than FLX). -/
theorem generic_format_FLX_FLT (beta : radix) (emin prec : ℤ) {x : ℝ}
    (h : generic_format beta (FLT_exp emin prec) x) :
    generic_format beta (FLX_exp prec) x := by
  rw [h]
  apply generic_format_F2R beta (FLX_exp prec) _ _
  intro _
  rw [← h]
  unfold cexp FLX_exp FLT_exp
  exact le_max_left _ _

/-- Above the gradual-underflow threshold, rounding under FLT and FLX coincide. -/
theorem round_FLT_FLX (beta : radix) (emin prec : ℤ) (rnd : ℝ → ℤ) {x : ℝ}
    (hx : bpow beta (emin + prec - 1) ≤ |x|) :
    round beta (FLT_exp emin prec) rnd x = round beta (FLX_exp prec) rnd x := by
  unfold round scaled_mantissa
  rw [cexp_FLT_FLX beta emin prec hx]

/-! ### Links between FLT and FIX (underflow regime) -/

/-- For nonzero values below the gradual-underflow threshold, FLT and FIX
agree on the canonical exponent. -/
theorem cexp_FLT_FIX (beta : radix) (emin prec : ℤ) {x : ℝ}
    (hx0 : x ≠ 0) (hx : |x| < bpow beta (emin + prec)) :
    cexp beta (FLT_exp emin prec) x = cexp beta (FIX_exp emin) x := by
  have h_mag : mag beta x ≤ emin + prec := mag_le_bpow beta hx0 hx
  unfold cexp FLT_exp FIX_exp
  apply max_eq_right
  linarith

/-- Every FLT-format value is also in the FIX(emin) format. -/
theorem generic_format_FIX_FLT (beta : radix) (emin prec : ℤ) {x : ℝ}
    (h : generic_format beta (FLT_exp emin prec) x) :
    generic_format beta (FIX_exp emin) x := by
  rw [h]
  apply generic_format_F2R beta (FIX_exp emin) _ _
  intro _
  rw [← h]
  unfold cexp FIX_exp FLT_exp
  exact le_max_right _ _

/-- A FIX(emin) value below the gradual-underflow threshold is FLT. -/
theorem generic_format_FLT_FIX (beta : radix) (emin prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (hx : |x| ≤ bpow beta (emin + prec))
    (h : generic_format beta (FIX_exp emin) x) :
    generic_format beta (FLT_exp emin prec) x := by
  refine generic_inclusion_le beta (FIX_exp emin) (FLT_exp emin prec)
    (FIX_exp_valid emin) (FLT_exp_valid emin prec hp) (emin + prec) ?_ hx h
  intro e he
  unfold FIX_exp FLT_exp
  exact max_le (by linarith) (le_refl _)

/-- Below the gradual-underflow threshold, the FLT format has constant ulp
equal to `bpow emin` — it behaves like FIX(emin) there. -/
theorem ulp_FLT_small (beta : radix) (emin prec : ℤ) (hp : 0 < prec) {x : ℝ}
    (hx : |x| < bpow beta (emin + prec)) :
    ulp beta (FLT_exp emin prec) x = bpow beta emin := by
  unfold ulp
  by_cases hx0 : x = 0
  · rw [if_pos hx0]
    rcases h_neg : negligible_exp (FLT_exp emin prec) with _ | n
    · -- `none`: contradiction. emin is in the small regime since
      -- FLT_exp emin = max(emin - prec, emin) = emin (prec > 0).
      exfalso
      have h_self : FLT_exp emin prec emin = emin := by
        unfold FLT_exp; exact max_eq_right (by linarith)
      have := negligible_exp_none h_neg emin
      linarith
    · show bpow beta (FLT_exp emin prec n) = bpow beta emin
      have h_self : FLT_exp emin prec emin = emin := by
        unfold FLT_exp; exact max_eq_right (by linarith)
      have h_n_le : n ≤ FLT_exp emin prec n := negligible_exp_some h_neg
      have h_emin_le : emin ≤ FLT_exp emin prec emin := by rw [h_self]
      have h_eq := fexp_negligible_exp_eq (FLT_exp_valid emin prec hp) h_n_le h_emin_le
      rw [h_eq, h_self]
  · rw [if_neg hx0]
    show bpow beta (cexp beta (FLT_exp emin prec) x) = bpow beta emin
    have h_mag_le : mag beta x ≤ emin + prec := mag_le_bpow beta hx0 hx
    unfold cexp FLT_exp
    show bpow beta (max (mag beta x - prec) emin) = bpow beta emin
    have h_max : max (mag beta x - prec) emin = emin := by
      apply max_eq_right; linarith
    rw [h_max]

/-- Above the gradual-underflow threshold, ulp is bounded above by
`|x| · β^(1 - prec)` — the relative error is at most `β^(1 - prec)`. -/
theorem ulp_FLT_le (beta : radix) (emin prec : ℤ) {x : ℝ}
    (hx : bpow beta (emin + prec - 1) ≤ |x|) :
    ulp beta (FLT_exp emin prec) x ≤ |x| * bpow beta (1 - prec) := by
  have hx_ne : x ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hx
    exact absurd hx (not_le.mpr (bpow_gt_0 _ _))
  rw [ulp_neq_0 beta (FLT_exp emin prec) hx_ne]
  have h_mag_gt : emin + prec - 1 < mag beta x := mag_gt_bpow beta hx
  have h_max : max (mag beta x - prec) emin = mag beta x - prec := by
    apply max_eq_left; linarith
  show bpow beta (cexp beta (FLT_exp emin prec) x) ≤ |x| * bpow beta (1 - prec)
  unfold cexp FLT_exp
  rw [h_max]
  have h_split : bpow beta (mag beta x - prec)
      = bpow beta (mag beta x - 1) * bpow beta (1 - prec) := by
    rw [← bpow_plus]; congr 1; ring
  rw [h_split]
  exact mul_le_mul_of_nonneg_right (bpow_mag_le beta hx_ne) (bpow_ge_0 _ _)

/-- Universal lower bound: `ulp x > |x| · β^(-prec)`. The format always
spaces values at least this finely (in relative terms). -/
theorem ulp_FLT_gt (beta : radix) (emin prec : ℤ) (hp : 0 < prec) (x : ℝ) :
    |x| * bpow beta (-prec) < ulp beta (FLT_exp emin prec) x := by
  by_cases hx : x = 0
  · rw [hx, abs_zero, zero_mul]
    rw [ulp_FLT_small beta emin prec hp (x := 0) (by
      rw [abs_zero]; exact bpow_gt_0 _ _)]
    exact bpow_gt_0 _ _
  · rw [ulp_neq_0 beta (FLT_exp emin prec) hx]
    show |x| * bpow beta (-prec) < bpow beta (cexp beta (FLT_exp emin prec) x)
    have h_mag_gt : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
    have h_step1 : |x| * bpow beta (-prec) < bpow beta (mag beta x - prec) := by
      have h_split : bpow beta (mag beta x) * bpow beta (-prec)
          = bpow beta (mag beta x - prec) := by
        rw [show mag beta x - prec = mag beta x + (-prec) from by ring,
            ← bpow_plus]
      calc |x| * bpow beta (-prec)
          < bpow beta (mag beta x) * bpow beta (-prec) :=
            mul_lt_mul_of_pos_right h_mag_gt (bpow_gt_0 _ _)
        _ = bpow beta (mag beta x - prec) := h_split
    have h_step2 : bpow beta (mag beta x - prec)
        ≤ bpow beta (cexp beta (FLT_exp emin prec) x) := by
      apply bpow_le
      unfold cexp FLT_exp
      exact le_max_left _ _
    linarith

/-- `1` is in the FLT format whenever `emin ≤ 0`. -/
theorem generic_format_FLT_1 (beta : radix) (emin prec : ℤ) (hp : 0 < prec)
    (Hemin : emin ≤ 0) :
    generic_format beta (FLT_exp emin prec) 1 := by
  have h := generic_format_bpow' beta (FLT_exp emin prec)
    (FLT_exp_valid emin prec hp) 0 ?_
  · rwa [bpow_zero] at h
  · unfold FLT_exp
    apply max_le
    · linarith
    · exact Hemin

/-- Above the gradual-underflow threshold, ulp scales exactly by `β^e`
under multiplication by `β^e` in FLT. -/
theorem ulp_FLT_exact_shift (beta : radix) (emin prec : ℤ) {x : ℝ} (hx_ne : x ≠ 0)
    {e : ℤ} (h_mag : emin + prec ≤ mag beta x)
    (h_e : emin + prec - mag beta x ≤ e) :
    ulp beta (FLT_exp emin prec) (x * bpow beta e)
      = ulp beta (FLT_exp emin prec) x * bpow beta e := by
  have h_xb_ne : x * bpow beta e ≠ 0 :=
    mul_ne_zero hx_ne (ne_of_gt (bpow_gt_0 _ _))
  rw [ulp_neq_0 beta (FLT_exp emin prec) h_xb_ne,
      ulp_neq_0 beta (FLT_exp emin prec) hx_ne]
  show bpow beta (cexp beta (FLT_exp emin prec) (x * bpow beta e))
      = bpow beta (cexp beta (FLT_exp emin prec) x) * bpow beta e
  unfold cexp FLT_exp
  rw [mag_mult_bpow beta hx_ne e]
  have h_max1 : max (mag beta x + e - prec) emin = mag beta x + e - prec := by
    apply max_eq_left; linarith
  have h_max2 : max (mag beta x - prec) emin = mag beta x - prec := by
    apply max_eq_left; linarith
  rw [h_max1, h_max2,
      show mag beta x + e - prec = (mag beta x - prec) + e from by ring,
      bpow_plus]

end LeanFlocq
