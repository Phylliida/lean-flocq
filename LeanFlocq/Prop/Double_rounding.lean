/-
Lean port of Coq Flocq's `Prop/Double_rounding.v` — conditions for innocuous
double rounding.

Double rounding occurs when a value is first rounded at one precision, then
rounded again to a coarser target precision. In general this can give a
different answer than rounding directly. This file establishes sufficient
conditions under which double rounding is equivalent to single rounding.

Original Coq is © 2014–2018 Sylvie Boldo, Guillaume Melquiond, and Pierre Roux.
LGPL v3+.

The file is large (~4500 Coq lines). Top-level structure:

- **Core mid-rounding theorems** (~600 Coq lines): `round_round_lt_mid` and
  `round_round_gt_mid` families. Show that double rounding agrees with direct
  rounding when `x` is "far enough" from the midpoint.
- **Multiplication** (~160 lines): `round_round_mult` and format-specific
  instantiations (FLX, FLT, FTZ).
- **Plus/Minus** (~1760 lines, the largest): `round_round_plus`,
  `round_round_minus`, with FLX/FLT/FTZ instantiations and a separate
  `radix_ge_3` track.
- **Square root** (~870 lines): `round_round_sqrt` family.
- **Division** (~1100 lines): `round_round_div` family with a long bridge
  lemma `round_round_eq_mid_beta_even` (~97 lines).

The `round_N_odd` theorem from `Prop/Round_odd.lean` is the primary
underlying tool used throughout.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.Round_NE
import LeanFlocq.Core.Ulp
import LeanFlocq.Core.FLX
import LeanFlocq.Core.FLT
import LeanFlocq.Core.FTZ
import LeanFlocq.Calc.Operations
import LeanFlocq.Prop.Plus_error
import LeanFlocq.Prop.Round_odd

namespace LeanFlocq

/-! ## Definitions -/

/-- The double-rounding agrees with the single-rounding: rounding `x` at the
finer format `fexp2` and then at the target format `fexp1` gives the same
result as rounding directly at `fexp1`. -/
def round_round_eq (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (choice1 choice2 : ℤ → Bool) (x : ℝ) : Prop :=
  round beta fexp1 (Znearest choice1) (round beta fexp2 (Znearest choice2) x)
    = round beta fexp1 (Znearest choice1) x

/-- The midpoint between `round_DN x` and `round_UP x`, expressed via the
round-down witness plus half a ulp. -/
noncomputable def midp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  round beta fexp (fun y : ℝ => ⌊y⌋) x + (1 : ℝ) / 2 * ulp beta fexp x

/-- The midpoint expressed via the round-up witness minus half a ulp.
Equal to `midp` when `x ∉ F`. -/
noncomputable def midp' (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  round beta fexp (fun y : ℝ => ⌈y⌉) x - (1 : ℝ) / 2 * ulp beta fexp x

/-! ## Core mid-rounding theorems

When `x` is sufficiently far below the midpoint between `round_DN(x)` and
`round_UP(x)`, double rounding agrees with single rounding. -/

/-- The first foundational lemma: under a precision gap of at least 1 and
the strong hypothesis that `x` is below `midp1 - ulp2/2` (and also below
the top of its magnitude window by the same margin), double rounding equals
direct rounding. -/
theorem round_round_lt_mid_further_place'
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1)
    (Hx1 : x < bpow beta (mag beta x) - (1/2) * ulp beta fexp2 x)
    (Hx2' : x < midp beta fexp1 x - (1/2) * ulp beta fexp2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  unfold round_round_eq
  have h_x_ne : x ≠ 0 := ne_of_gt Px
  -- Unfold ulps to bpow of fexp ∘ mag
  have h_ulp1 : ulp beta fexp1 x = bpow beta (fexp1 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp1 h_x_ne]; rfl
  have h_ulp2 : ulp beta fexp2 x = bpow beta (fexp2 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp2 h_x_ne]; rfl
  -- Set x' = round_DN x at fexp1
  set x' := round beta fexp1 (fun y : ℝ => ⌊y⌋) x with hx'_def
  -- From Hx2', derive Hx2: x - x' < (1/2) * (bpow(fexp1) - bpow(fexp2))
  have Hx2 : x - x' < (1/2) * (bpow beta (fexp1 (mag beta x))
      - bpow beta (fexp2 (mag beta x))) := by
    unfold midp at Hx2'
    rw [h_ulp1, h_ulp2] at Hx2'
    linarith
  -- Pxx': 0 ≤ x - x' (since x' ≤ x by DN)
  have Pxx' : 0 ≤ x - x' := by
    have h_dn := (round_DN_pt beta fexp1 Vfexp1 x).2.1
    rw [← hx'_def] at h_dn
    linarith
  -- Set x'' = round_N x at fexp2
  set x'' := round beta fexp2 (Znearest choice2) x with hx''_def
  -- Hr1: |x'' - x| ≤ (1/2) * bpow(fexp2(mag x))
  have Hr1 : |x'' - x| ≤ (1/2) * bpow beta (fexp2 (mag beta x)) := by
    have h := error_le_half_ulp beta fexp2 Vfexp2 choice2 x
    rw [h_ulp2] at h
    exact h
  -- Hr2: |x'' - x'| < (1/2) * bpow(fexp1(mag x))
  have Hr2 : |x'' - x'| < (1/2) * bpow beta (fexp1 (mag beta x)) := by
    have h_split : x'' - x' = (x'' - x) + (x - x') := by ring
    rw [h_split]
    have h_tri := abs_add_le (x'' - x) (x - x')
    have h_abs_xx' : |x - x'| = x - x' := abs_of_nonneg Pxx'
    rw [h_abs_xx'] at h_tri
    linarith
  -- bpow positivity facts
  have h_bpow_fexp1_pos : 0 < bpow beta (fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_bpow_neg_fexp1_pos : 0 < bpow beta (-fexp1 (mag beta x)) := bpow_gt_0 _ _
  -- cexp at fexp1 unfolds to fexp1(mag x)
  have h_cexp_x : cexp beta fexp1 x = fexp1 (mag beta x) := rfl
  -- Case split: x'' = 0 vs x'' ≠ 0
  by_cases Zx'' : x'' = 0
  · -- Case x'' = 0
    rw [Zx''] at Hr1
    rw [Zx'', round_0]
    -- Show round_N x at fexp1 = 0 via Znearest_imp with n = 0.
    have h_round_x_zero : round beta fexp1 (Znearest choice1) x = 0 := by
      have h_z : Znearest choice1 (scaled_mantissa beta fexp1 x) = 0 := by
        apply Znearest_imp
        show |scaled_mantissa beta fexp1 x - ((0 : ℤ) : ℝ)| < 1/2
        push_cast
        rw [sub_zero]
        -- |x| ≤ (1/2) * bpow(fexp2) from x'' = 0 in Hr1
        have h_x_abs : |x| ≤ (1/2) * bpow beta (fexp2 (mag beta x)) := by
          have h := Hr1
          rw [zero_sub, abs_neg] at h
          exact h
        -- |sm| = |x| * bpow(-fexp1(mag x))
        show |x * bpow beta (-cexp beta fexp1 x)| < 1/2
        rw [h_cexp_x, abs_mul, abs_of_pos h_bpow_neg_fexp1_pos]
        -- |x| * bpow(-fexp1) ≤ (1/2) * bpow(fexp2) * bpow(-fexp1) = (1/2) * bpow(fexp2 - fexp1)
        -- ≤ (1/2) * bpow(-1) ≤ (1/2) * (1/β) ≤ 1/4 < 1/2 (since β ≥ 2)
        have h_step1 : |x| * bpow beta (-fexp1 (mag beta x))
            ≤ (1/2) * bpow beta (fexp2 (mag beta x))
                * bpow beta (-fexp1 (mag beta x)) :=
          mul_le_mul_of_nonneg_right h_x_abs (le_of_lt h_bpow_neg_fexp1_pos)
        have h_step2 : (1/2) * bpow beta (fexp2 (mag beta x))
            * bpow beta (-fexp1 (mag beta x))
            = (1/2) * bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := by
          rw [mul_assoc, ← bpow_plus]
          rfl
        have h_step3 : bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x))
            ≤ bpow beta (-1 : ℤ) := bpow_le beta (by linarith)
        have h_bpow_neg1 : bpow beta (-1 : ℤ) ≤ 1/2 := by
          show (beta.val : ℝ)^(-1 : ℤ) ≤ 1/2
          rw [zpow_neg, zpow_one, ← one_div]
          apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          exact_mod_cast beta.prop
        calc |x| * bpow beta (-fexp1 (mag beta x))
            ≤ (1/2) * bpow beta (fexp2 (mag beta x))
                * bpow beta (-fexp1 (mag beta x)) := h_step1
          _ = (1/2) * bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := h_step2
          _ ≤ (1/2) * bpow beta (-1 : ℤ) := by
              apply mul_le_mul_of_nonneg_left h_step3 (by linarith)
          _ ≤ (1/2) * (1/2) := by
              apply mul_le_mul_of_nonneg_left h_bpow_neg1 (by linarith)
          _ < 1/2 := by linarith
      show round beta fexp1 (Znearest choice1) x = 0
      unfold round
      rw [h_z]
      show F2R (beta := beta) ⟨0, cexp beta fexp1 x⟩ = 0
      unfold F2R
      push_cast
      ring
    exact h_round_x_zero.symm
  · -- Case x'' ≠ 0
    -- Establish mag x'' = mag x
    have Lx'' : mag beta x'' = mag beta x := by
      apply le_antisymm
      · -- mag x'' ≤ mag x: show |x''| < bpow(mag x)
        apply mag_le_bpow beta Zx''
        have h_split : x'' = (x'' - x) + x := by ring
        rw [h_split]
        have h_tri := abs_add_le (x'' - x) x
        have h_abs_x : |x| = x := abs_of_pos Px
        rw [h_abs_x] at h_tri
        have hHx1_unfolded : x < bpow beta (mag beta x)
            - (1/2) * bpow beta (fexp2 (mag beta x)) := by
          rw [h_ulp2] at Hx1
          exact Hx1
        linarith
      · -- mag x ≤ mag x'' from mag_round_ge
        exact mag_round_ge beta fexp2 Vfexp2 (Znearest choice2) Zx''
    -- Goal: round_N x'' at fexp1 = round_N x at fexp1
    -- Both rounds have same cexp = fexp1(mag x) (by Lx'' for x'')
    -- Both Znearests equal ⌊sm fexp1 x⌋ by Znearest_imp.
    have h_cexp_x'' : cexp beta fexp1 x'' = fexp1 (mag beta x) := by
      show fexp1 (mag beta x'') = fexp1 (mag beta x); rw [Lx'']
    -- ((⌊sm fexp1 x⌋ : ℤ) : ℝ) * bpow(fexp1(mag x)) = x'
    have h_floor_x' : ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
        * bpow beta (fexp1 (mag beta x)) = x' := by
      show ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
          * bpow beta (fexp1 (mag beta x))
        = round beta fexp1 (fun y : ℝ => ⌊y⌋) x
      unfold round
      rfl
    -- Znearest x: scaled mantissa is within 1/2 of its floor.
    have h_zn_x : Znearest choice1 (scaled_mantissa beta fexp1 x)
        = ⌊scaled_mantissa beta fexp1 x⌋ := by
      apply Znearest_imp
      -- |sm - ⌊sm⌋| = (x - x') * bpow(-fexp1)
      -- (x - x') < (1/2) * (bpow(fexp1) - bpow(fexp2)) → result < (1/2)
      have h_eq : scaled_mantissa beta fexp1 x
          - ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
          = (x - x') * bpow beta (-fexp1 (mag beta x)) := by
        show x * bpow beta (-cexp beta fexp1 x)
            - ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
          = (x - x') * bpow beta (-fexp1 (mag beta x))
        rw [h_cexp_x]
        have h_floor_real : ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
            = x' * bpow beta (-fexp1 (mag beta x)) := by
          have h_bpow_inv : bpow beta (-fexp1 (mag beta x))
              = (bpow beta (fexp1 (mag beta x)))⁻¹ := by
            show (beta.val : ℝ)^(-fexp1 (mag beta x))
              = ((beta.val : ℝ)^(fexp1 (mag beta x)))⁻¹
            exact zpow_neg _ _
          rw [h_bpow_inv, ← div_eq_mul_inv,
              eq_div_iff (ne_of_gt h_bpow_fexp1_pos)]
          exact h_floor_x'
        rw [h_floor_real]
        ring
      rw [h_eq]
      have h_abs : |(x - x') * bpow beta (-fexp1 (mag beta x))|
          = (x - x') * bpow beta (-fexp1 (mag beta x)) :=
        abs_of_nonneg (mul_nonneg Pxx' (le_of_lt h_bpow_neg_fexp1_pos))
      rw [h_abs]
      -- (x - x') * bpow(-fexp1) < (1/2) * (bpow(fexp1) - bpow(fexp2)) * bpow(-fexp1)
      --                         = (1/2) * (1 - bpow(fexp2 - fexp1))
      --                         ≤ (1/2)
      have h_step : (x - x') * bpow beta (-fexp1 (mag beta x))
          < (1/2) * (bpow beta (fexp1 (mag beta x))
              - bpow beta (fexp2 (mag beta x)))
            * bpow beta (-fexp1 (mag beta x)) :=
        mul_lt_mul_of_pos_right Hx2 h_bpow_neg_fexp1_pos
      have h_bp1 : bpow beta (fexp1 (mag beta x))
          * bpow beta (-fexp1 (mag beta x)) = 1 := by
        rw [← bpow_plus]
        show bpow beta (fexp1 (mag beta x) + -fexp1 (mag beta x)) = 1
        have h : fexp1 (mag beta x) + -fexp1 (mag beta x) = 0 := by ring
        rw [h]; rfl
      have h_bp2 : bpow beta (fexp2 (mag beta x))
          * bpow beta (-fexp1 (mag beta x))
          = bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := by
        rw [← bpow_plus]
        rfl
      have h_distribute : (1/2) * (bpow beta (fexp1 (mag beta x))
          - bpow beta (fexp2 (mag beta x))) * bpow beta (-fexp1 (mag beta x))
          = (1/2) * (1 - bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x))) := by
        rw [mul_assoc, sub_mul, h_bp1, h_bp2]
      have h_bpow_pos_diff : 0 ≤ bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) :=
        le_of_lt (bpow_gt_0 _ _)
      linarith
    -- Znearest x'': similar argument with x'' - x' < (1/2) * bpow(fexp1)
    have h_zn_x'' : Znearest choice1 (scaled_mantissa beta fexp1 x'')
        = ⌊scaled_mantissa beta fexp1 x⌋ := by
      apply Znearest_imp
      -- sm fexp1 x'' = x'' * bpow(-fexp1(mag x'')) = x'' * bpow(-fexp1(mag x))
      have h_eq : scaled_mantissa beta fexp1 x''
          - ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
          = (x'' - x') * bpow beta (-fexp1 (mag beta x)) := by
        show x'' * bpow beta (-cexp beta fexp1 x'')
            - ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
          = (x'' - x') * bpow beta (-fexp1 (mag beta x))
        rw [show cexp beta fexp1 x'' = fexp1 (mag beta x) from h_cexp_x'']
        have h_floor_real : ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
            = x' * bpow beta (-fexp1 (mag beta x)) := by
          have h_bpow_inv : bpow beta (-fexp1 (mag beta x))
              = (bpow beta (fexp1 (mag beta x)))⁻¹ := by
            show (beta.val : ℝ)^(-fexp1 (mag beta x))
              = ((beta.val : ℝ)^(fexp1 (mag beta x)))⁻¹
            exact zpow_neg _ _
          rw [h_bpow_inv, ← div_eq_mul_inv,
              eq_div_iff (ne_of_gt h_bpow_fexp1_pos)]
          exact h_floor_x'
        rw [h_floor_real]
        ring
      rw [h_eq]
      -- |x'' - x'| * bpow(-fexp1) < (1/2) * bpow(fexp1) * bpow(-fexp1) = 1/2
      rw [abs_mul, abs_of_pos h_bpow_neg_fexp1_pos]
      have h_step : |x'' - x'| * bpow beta (-fexp1 (mag beta x))
          < (1/2) * bpow beta (fexp1 (mag beta x))
            * bpow beta (-fexp1 (mag beta x)) :=
        mul_lt_mul_of_pos_right Hr2 h_bpow_neg_fexp1_pos
      have h_cancel : (1/2) * bpow beta (fexp1 (mag beta x))
          * bpow beta (-fexp1 (mag beta x)) = 1/2 := by
        rw [mul_assoc, ← bpow_plus]
        have h_zero : fexp1 (mag beta x) + -fexp1 (mag beta x) = 0 := by ring
        rw [h_zero]
        show (1/2) * bpow beta 0 = 1/2
        show (1/2) * 1 = 1/2
        ring
      linarith
    -- Conclude: both rounds give the same F2R
    show round beta fexp1 (Znearest choice1) x''
       = round beta fexp1 (Znearest choice1) x
    unfold round
    rw [h_zn_x, h_zn_x'']
    -- After rewriting Znearests to ⌊sm fexp1 x⌋, both sides have the same
    -- mantissa and their exponents are both fexp1(mag x) (one via h_cexp_x''
    -- after rewrite, the other via definitional unfolding of cexp).
    show F2R (beta := beta) ⟨⌊scaled_mantissa beta fexp1 x⌋, cexp beta fexp1 x''⟩
       = F2R (beta := beta) ⟨⌊scaled_mantissa beta fexp1 x⌋, cexp beta fexp1 x⟩
    rw [h_cexp_x'']
    rfl

/-- Refinement of the previous lemma: instead of requiring `x` to be below the
top of its magnitude window by `ulp2/2`, we just need `fexp1(mag x) ≤ mag x`
(equivalent to `x` being in the "large" regime where the format has unit
precision steps). -/
theorem round_round_lt_mid_further_place
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1)
    (Hf1 : fexp1 (mag beta x) ≤ mag beta x)
    (Hx2' : x < midp beta fexp1 x - (1/2) * ulp beta fexp2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  apply round_round_lt_mid_further_place' beta Vfexp1 Vfexp2 choice1 choice2 Px Hf2f1 ?_ Hx2'
  -- Show: x < bpow(mag x) - (1/2) * ulp2.
  have h_x_ne : x ≠ 0 := ne_of_gt Px
  have h_ulp1 : ulp beta fexp1 x = bpow beta (fexp1 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp1 h_x_ne]; rfl
  have h_ulp2 : ulp beta fexp2 x = bpow beta (fexp2 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp2 h_x_ne]; rfl
  -- From Hx2', derive x - x' < (1/2) * (ulp1 - ulp2).
  set x' := round beta fexp1 (fun y : ℝ => ⌊y⌋) x with hx'_def
  have Hx2 : x - x' < (1/2) * (bpow beta (fexp1 (mag beta x))
      - bpow beta (fexp2 (mag beta x))) := by
    unfold midp at Hx2'
    rw [h_ulp1, h_ulp2] at Hx2'
    linarith
  have Pxx' : 0 ≤ x - x' := by
    have h_dn := (round_DN_pt beta fexp1 Vfexp1 x).2.1
    rw [← hx'_def] at h_dn
    linarith
  have h_x_lt_bpow : x < bpow beta (mag beta x) := by
    have := bpow_mag_gt beta x
    rw [abs_of_pos Px] at this
    exact this
  -- Case split: x' = 0 or x' ≠ 0
  by_cases Zx' : x' = 0
  · -- x' = 0: x < (1/2) * (ulp1 - ulp2)
    rw [Zx', sub_zero] at Hx2
    -- Need: x < bpow(mag x) - (1/2) * ulp2.
    -- We have: x < (1/2) * (ulp1 - ulp2)
    -- It suffices that (1/2) * (ulp1 - ulp2) ≤ bpow(mag x) - (1/2) * ulp2
    --   ⟺ (1/2) * ulp1 ≤ bpow(mag x)
    --   ⟺ ulp1 ≤ 2 * bpow(mag x)
    --   ⟸ ulp1 ≤ bpow(mag x), i.e., bpow(fexp1(mag x)) ≤ bpow(mag x) (from Hf1).
    have h_ulp1_le : bpow beta (fexp1 (mag beta x))
        ≤ bpow beta (mag beta x) := bpow_le beta Hf1
    rw [h_ulp2]
    linarith
  · -- x' ≠ 0: 0 < x' (since x' ≥ 0 and x' ≠ 0).
    have Px'_nn : 0 ≤ x' := by
      rw [hx'_def]
      exact round_ge_generic beta fexp1 Vfexp1 _ (generic_format_0 _ _) (le_of_lt Px)
    have Px' : 0 < x' := lt_of_le_of_ne Px'_nn (Ne.symm Zx')
    -- mag x' = mag x (since x' = round_DN x > 0).
    have h_mag_x' : mag beta x' = mag beta x := by
      rw [hx'_def]
      apply mag_DN beta fexp1 Vfexp1
      rw [← hx'_def]
      exact Px'
    -- ulp(x') = ulp(x) since mags agree.
    have h_ulp_x'_eq : ulp beta fexp1 x' = bpow beta (fexp1 (mag beta x)) := by
      rw [ulp_neq_0 beta fexp1 (ne_of_gt Px')]
      show bpow beta (fexp1 (mag beta x')) = bpow beta (fexp1 (mag beta x))
      rw [h_mag_x']
    -- x' + ulp1 ≤ bpow(mag x) via id_p_ulp_le_bpow.
    have h_x'_F : generic_format beta fexp1 x' :=
      generic_format_round beta fexp1 Vfexp1 _ x
    have h_x'_le_x : x' ≤ x := by linarith
    have h_x'_lt_bpow : x' < bpow beta (mag beta x) := lt_of_le_of_lt h_x'_le_x h_x_lt_bpow
    have h_id_ulp := id_p_ulp_le_bpow beta fexp1 Px' h_x'_F h_x'_lt_bpow
    rw [h_ulp_x'_eq] at h_id_ulp
    rw [h_ulp2]
    -- Goal: x < bpow(mag x) - (1/2) * bpow(fexp2).
    -- From Hx2: x < x' + (1/2) * (bpow(fexp1) - bpow(fexp2))
    -- From h_id_ulp: x' + bpow(fexp1) ≤ bpow(mag x), so x' ≤ bpow(mag x) - bpow(fexp1)
    -- Combine: x < bpow(mag x) - bpow(fexp1) + (1/2) * (bpow(fexp1) - bpow(fexp2))
    --        = bpow(mag x) - (1/2) * bpow(fexp1) - (1/2) * bpow(fexp2)
    --        ≤ bpow(mag x) - (1/2) * bpow(fexp2)
    have h_bpow_fexp1_nn : 0 ≤ bpow beta (fexp1 (mag beta x)) :=
      le_of_lt (bpow_gt_0 _ _)
    linarith

/-- When the inner format has the same precision as the target (`fexp2 = fexp1`
at `mag x`) and `x` is strictly below the midpoint, double rounding agrees
with single rounding.

Proof: the condition `x < midp1` means the round-down distance is less than
half a ulp, so both `Znearest` applications give `⌊sm⌋`. -/
theorem round_round_lt_mid_same_place
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) = fexp1 (mag beta x))
    (Hx' : x < midp beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  unfold round_round_eq
  have h_x_ne : x ≠ 0 := ne_of_gt Px
  have h_ulp1 : ulp beta fexp1 x = bpow beta (fexp1 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp1 h_x_ne]; rfl
  -- From x < midp1, derive Hx : x - x' < (1/2) * ulp1
  set x' := round beta fexp1 (fun y : ℝ => ⌊y⌋) x with hx'_def
  have Hx : x - x' < (1/2) * bpow beta (fexp1 (mag beta x)) := by
    unfold midp at Hx'
    rw [h_ulp1] at Hx'
    linarith
  have Pxx' : 0 ≤ x - x' := by
    have h_dn := (round_DN_pt beta fexp1 Vfexp1 x).2.1
    rw [← hx'_def] at h_dn
    linarith
  -- The key Znearest_imp condition: |sm fexp1 x - ⌊sm fexp1 x⌋| < 1/2
  have h_bpow_pos : 0 < bpow beta (fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_bpow_neg_pos : 0 < bpow beta (-fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_floor_x' : ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
      * bpow beta (fexp1 (mag beta x)) = x' := rfl
  have h_floor_real : ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)
      = x' * bpow beta (-fexp1 (mag beta x)) := by
    have h_bpow_inv : bpow beta (-fexp1 (mag beta x))
        = (bpow beta (fexp1 (mag beta x)))⁻¹ := by
      show (beta.val : ℝ)^(-fexp1 (mag beta x))
        = ((beta.val : ℝ)^(fexp1 (mag beta x)))⁻¹
      exact zpow_neg _ _
    rw [h_bpow_inv, ← div_eq_mul_inv,
        eq_div_iff (ne_of_gt h_bpow_pos)]
    exact h_floor_x'
  have H_znear : |scaled_mantissa beta fexp1 x
        - ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)| < 1/2 := by
    show |x * bpow beta (-cexp beta fexp1 x)
        - ((⌊scaled_mantissa beta fexp1 x⌋ : ℤ) : ℝ)| < 1/2
    have h_cexp : cexp beta fexp1 x = fexp1 (mag beta x) := rfl
    rw [h_cexp, h_floor_real]
    have h_eq : x * bpow beta (-fexp1 (mag beta x))
        - x' * bpow beta (-fexp1 (mag beta x))
        = (x - x') * bpow beta (-fexp1 (mag beta x)) := by ring
    rw [h_eq, abs_of_nonneg (mul_nonneg Pxx' (le_of_lt h_bpow_neg_pos))]
    -- (x - x') * bpow(-fexp1) < (1/2) * bpow(fexp1) * bpow(-fexp1) = 1/2
    have h_step : (x - x') * bpow beta (-fexp1 (mag beta x))
        < (1/2) * bpow beta (fexp1 (mag beta x))
          * bpow beta (-fexp1 (mag beta x)) :=
      mul_lt_mul_of_pos_right Hx h_bpow_neg_pos
    have h_cancel : (1/2) * bpow beta (fexp1 (mag beta x))
        * bpow beta (-fexp1 (mag beta x)) = 1/2 := by
      rw [mul_assoc, ← bpow_plus]
      have : fexp1 (mag beta x) + -fexp1 (mag beta x) = 0 := by ring
      rw [this]
      show (1/2) * bpow beta 0 = 1/2
      show (1/2) * 1 = 1/2
      ring
    linarith
  -- Now compute LHS: round_N(round_N x at fexp2) at fexp1.
  -- round_N x at fexp2: unfold round, use Hf2f1, Znearest_imp gives ⌊sm fexp1 x⌋.
  -- So round_N x at fexp2 = ⌊sm fexp1 x⌋ * bpow(fexp1(mag x)) = x'.
  -- Then round_N x' at fexp1 = x' (since x' ∈ F1) via round_generic.
  -- And RHS round_N x at fexp1: Znearest_imp gives ⌊sm fexp1 x⌋, so RHS = x'.
  -- Both equal x'.
  have h_inner : round beta fexp2 (Znearest choice2) x = x' := by
    unfold round
    show F2R (beta := beta) ⟨Znearest choice2 (scaled_mantissa beta fexp2 x),
                              cexp beta fexp2 x⟩ = x'
    -- cexp beta fexp2 x = fexp2 (mag x) = fexp1 (mag x)
    have h_cexp_eq : cexp beta fexp2 x = fexp1 (mag beta x) := by
      show fexp2 (mag beta x) = fexp1 (mag beta x); exact Hf2f1
    -- scaled_mantissa beta fexp2 x = scaled_mantissa beta fexp1 x (since cexps agree)
    have h_sm_eq : scaled_mantissa beta fexp2 x = scaled_mantissa beta fexp1 x := by
      show x * bpow beta (-cexp beta fexp2 x)
        = x * bpow beta (-cexp beta fexp1 x)
      rw [h_cexp_eq]
      rfl
    rw [h_sm_eq, h_cexp_eq]
    have h_zn : Znearest choice2 (scaled_mantissa beta fexp1 x)
        = ⌊scaled_mantissa beta fexp1 x⌋ := Znearest_imp _ H_znear
    rw [h_zn]
    exact h_floor_x'
  rw [h_inner]
  -- Now LHS = round_N x' at fexp1. Show this = x'.
  have h_x'_F : generic_format beta fexp1 x' :=
    generic_format_round beta fexp1 Vfexp1 _ x
  rw [round_generic beta fexp1 (Znearest choice1) h_x'_F]
  -- RHS = round_N x at fexp1 = x' via Znearest_imp.
  symm
  unfold round
  show F2R (beta := beta) ⟨Znearest choice1 (scaled_mantissa beta fexp1 x),
                            cexp beta fexp1 x⟩ = x'
  rw [Znearest_imp _ H_znear]
  exact h_floor_x'

/-- The main mid-rounding theorem for the `<` case: under the precision
hypothesis `fexp2(mag x) ≤ fexp1(mag x)` and the large-regime condition
`fexp1(mag x) ≤ mag x`, double rounding agrees with single rounding when
`x < midp1` (and a further-place margin holds when the precisions are
strictly distinct). -/
theorem round_round_lt_mid
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x))
    (Hf1 : fexp1 (mag beta x) ≤ mag beta x)
    (Hx : x < midp beta fexp1 x)
    (Hx' : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1
         → x < midp beta fexp1 x - (1/2) * ulp beta fexp2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  rcases le_or_gt (fexp1 (mag beta x)) (fexp2 (mag beta x)) with Hf2' | Hf2'
  · -- fexp1(mag x) ≤ fexp2(mag x): combined with Hf2f1, get fexp2 = fexp1
    have Hf2'' : fexp2 (mag beta x) = fexp1 (mag beta x) := le_antisymm Hf2f1 Hf2'
    exact round_round_lt_mid_same_place beta Vfexp1 choice1 choice2 Px Hf2'' Hx
  · -- fexp2(mag x) < fexp1(mag x): apply further_place
    have Hf2'' : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1 := by linarith
    exact round_round_lt_mid_further_place beta Vfexp1 Vfexp2 choice1 choice2 Px
      Hf2'' Hf1 (Hx' Hf2'')

/-! ### Mirror of `_lt_mid` family: above the midpoint -/

/-- The mirror of `round_round_lt_mid_further_place'`: when `x` is sufficiently
above `midp'` (the dual midpoint expressed via round-up) and the inner round
`x''` is below `bpow(mag x)`, double rounding agrees with single rounding. -/
theorem round_round_gt_mid_further_place'
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1)
    (Hx1 : round beta fexp2 (Znearest choice2) x < bpow beta (mag beta x))
    (Hx2' : midp' beta fexp1 x + (1/2) * ulp beta fexp2 x < x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  unfold round_round_eq
  have h_x_ne : x ≠ 0 := ne_of_gt Px
  have h_ulp1 : ulp beta fexp1 x = bpow beta (fexp1 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp1 h_x_ne]; rfl
  have h_ulp2 : ulp beta fexp2 x = bpow beta (fexp2 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp2 h_x_ne]; rfl
  -- Set x' = round_UP x at fexp1.
  set x' := round beta fexp1 (fun y : ℝ => ⌈y⌉) x with hx'_def
  -- From Hx2', derive Hx2: x' - x < (1/2) * (bpow(fexp1) - bpow(fexp2))
  have Hx2 : x' - x < (1/2) * (bpow beta (fexp1 (mag beta x))
      - bpow beta (fexp2 (mag beta x))) := by
    unfold midp' at Hx2'
    rw [h_ulp1, h_ulp2] at Hx2'
    linarith
  -- Px'x: 0 ≤ x' - x (since x' = round_UP x ≥ x)
  have Px'x : 0 ≤ x' - x := by
    have h_up := (round_UP_pt beta fexp1 Vfexp1 x).2.1
    rw [← hx'_def] at h_up
    linarith
  -- Set x'' = round_N x at fexp2
  set x'' := round beta fexp2 (Znearest choice2) x with hx''_def
  -- Hr1: |x'' - x| ≤ (1/2) * bpow(fexp2(mag x))
  have Hr1 : |x'' - x| ≤ (1/2) * bpow beta (fexp2 (mag beta x)) := by
    have h := error_le_half_ulp beta fexp2 Vfexp2 choice2 x
    rw [h_ulp2] at h
    exact h
  -- Hr2: |x'' - x'| < (1/2) * bpow(fexp1(mag x))
  have Hr2 : |x'' - x'| < (1/2) * bpow beta (fexp1 (mag beta x)) := by
    have h_split : x'' - x' = (x'' - x) + (x - x') := by ring
    rw [h_split]
    have h_tri := abs_add_le (x'' - x) (x - x')
    have h_abs_xx' : |x - x'| = x' - x := by
      rw [show x - x' = -(x' - x) from by ring, abs_neg, abs_of_nonneg Px'x]
    rw [h_abs_xx'] at h_tri
    linarith
  -- bpow positivity facts
  have h_bpow_fexp1_pos : 0 < bpow beta (fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_bpow_neg_fexp1_pos : 0 < bpow beta (-fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_cexp_x : cexp beta fexp1 x = fexp1 (mag beta x) := rfl
  -- Case split: x'' = 0 vs x'' ≠ 0
  by_cases Zx'' : x'' = 0
  · -- x'' = 0: same as _lt case via Znearest_imp with n=0
    rw [Zx''] at Hr1
    rw [Zx'', round_0]
    have h_round_x_zero : round beta fexp1 (Znearest choice1) x = 0 := by
      have h_z : Znearest choice1 (scaled_mantissa beta fexp1 x) = 0 := by
        apply Znearest_imp
        show |scaled_mantissa beta fexp1 x - ((0 : ℤ) : ℝ)| < 1/2
        push_cast
        rw [sub_zero]
        have h_x_abs : |x| ≤ (1/2) * bpow beta (fexp2 (mag beta x)) := by
          have h := Hr1
          rw [zero_sub, abs_neg] at h
          exact h
        show |x * bpow beta (-cexp beta fexp1 x)| < 1/2
        rw [h_cexp_x, abs_mul, abs_of_pos h_bpow_neg_fexp1_pos]
        have h_step1 : |x| * bpow beta (-fexp1 (mag beta x))
            ≤ (1/2) * bpow beta (fexp2 (mag beta x))
                * bpow beta (-fexp1 (mag beta x)) :=
          mul_le_mul_of_nonneg_right h_x_abs (le_of_lt h_bpow_neg_fexp1_pos)
        have h_step2 : (1/2) * bpow beta (fexp2 (mag beta x))
            * bpow beta (-fexp1 (mag beta x))
            = (1/2) * bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := by
          rw [mul_assoc, ← bpow_plus]; rfl
        have h_step3 : bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x))
            ≤ bpow beta (-1 : ℤ) := bpow_le beta (by linarith)
        have h_bpow_neg1 : bpow beta (-1 : ℤ) ≤ 1/2 := by
          show (beta.val : ℝ)^(-1 : ℤ) ≤ 1/2
          rw [zpow_neg, zpow_one, ← one_div]
          apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          exact_mod_cast beta.prop
        calc |x| * bpow beta (-fexp1 (mag beta x))
            ≤ (1/2) * bpow beta (fexp2 (mag beta x))
                * bpow beta (-fexp1 (mag beta x)) := h_step1
          _ = (1/2) * bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := h_step2
          _ ≤ (1/2) * bpow beta (-1 : ℤ) := by
              apply mul_le_mul_of_nonneg_left h_step3 (by linarith)
          _ ≤ (1/2) * (1/2) := by
              apply mul_le_mul_of_nonneg_left h_bpow_neg1 (by linarith)
          _ < 1/2 := by linarith
      show round beta fexp1 (Znearest choice1) x = 0
      unfold round
      rw [h_z]
      show F2R (beta := beta) ⟨0, cexp beta fexp1 x⟩ = 0
      unfold F2R
      push_cast
      ring
    exact h_round_x_zero.symm
  · -- x'' ≠ 0
    -- mag x'' = mag x
    have Lx'' : mag beta x'' = mag beta x := by
      apply le_antisymm
      · apply mag_le_bpow beta Zx''
        rw [abs_of_pos]
        · exact Hx1
        · -- 0 < x'': from round_N x at fexp2 < bpow(mag x) > 0 and x > 0
          -- Use round_ge_generic: 0 ≤ x → 0 ≤ x''
          have h_x''_nn : 0 ≤ x'' := by
            rw [hx''_def]
            exact round_ge_generic beta fexp2 Vfexp2 _ (generic_format_0 _ _) (le_of_lt Px)
          exact lt_of_le_of_ne h_x''_nn (Ne.symm Zx'')
      · exact mag_round_ge beta fexp2 Vfexp2 (Znearest choice2) Zx''
    -- Both rounds use cexp = fexp1(mag x) (via Lx'')
    have h_cexp_x'' : cexp beta fexp1 x'' = fexp1 (mag beta x) := by
      show fexp1 (mag beta x'') = fexp1 (mag beta x); rw [Lx'']
    -- ⌈sm fexp1 x⌉ * bpow(fexp1(mag x)) = x'
    have h_ceil_x' : ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
        * bpow beta (fexp1 (mag beta x)) = x' := rfl
    have h_ceil_real : ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
        = x' * bpow beta (-fexp1 (mag beta x)) := by
      have h_bpow_inv : bpow beta (-fexp1 (mag beta x))
          = (bpow beta (fexp1 (mag beta x)))⁻¹ := by
        show (beta.val : ℝ)^(-fexp1 (mag beta x))
          = ((beta.val : ℝ)^(fexp1 (mag beta x)))⁻¹
        exact zpow_neg _ _
      rw [h_bpow_inv, ← div_eq_mul_inv,
          eq_div_iff (ne_of_gt h_bpow_fexp1_pos)]
      exact h_ceil_x'
    -- Both Znearests equal ⌈sm fexp1 x⌉
    have h_zn_x : Znearest choice1 (scaled_mantissa beta fexp1 x)
        = ⌈scaled_mantissa beta fexp1 x⌉ := by
      apply Znearest_imp
      have h_eq : scaled_mantissa beta fexp1 x
          - ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
          = (x - x') * bpow beta (-fexp1 (mag beta x)) := by
        show x * bpow beta (-cexp beta fexp1 x)
            - ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
          = (x - x') * bpow beta (-fexp1 (mag beta x))
        rw [h_cexp_x, h_ceil_real]
        ring
      rw [h_eq]
      -- |sm - ⌈sm⌉| = |(x - x') * bpow(-fexp1)| = (x' - x) * bpow(-fexp1) (since x ≤ x')
      have h_abs : |(x - x') * bpow beta (-fexp1 (mag beta x))|
          = (x' - x) * bpow beta (-fexp1 (mag beta x)) := by
        rw [show (x - x') * bpow beta (-fexp1 (mag beta x))
            = -((x' - x) * bpow beta (-fexp1 (mag beta x))) from by ring,
            abs_neg]
        exact abs_of_nonneg (mul_nonneg Px'x (le_of_lt h_bpow_neg_fexp1_pos))
      rw [h_abs]
      have h_bp1 : bpow beta (fexp1 (mag beta x))
          * bpow beta (-fexp1 (mag beta x)) = 1 := by
        rw [← bpow_plus]
        show bpow beta (fexp1 (mag beta x) + -fexp1 (mag beta x)) = 1
        have h : fexp1 (mag beta x) + -fexp1 (mag beta x) = 0 := by ring
        rw [h]; rfl
      have h_bp2 : bpow beta (fexp2 (mag beta x))
          * bpow beta (-fexp1 (mag beta x))
          = bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := by
        rw [← bpow_plus]; rfl
      have h_step : (x' - x) * bpow beta (-fexp1 (mag beta x))
          < (1/2) * (bpow beta (fexp1 (mag beta x))
              - bpow beta (fexp2 (mag beta x)))
            * bpow beta (-fexp1 (mag beta x)) :=
        mul_lt_mul_of_pos_right Hx2 h_bpow_neg_fexp1_pos
      have h_distribute : (1/2) * (bpow beta (fexp1 (mag beta x))
          - bpow beta (fexp2 (mag beta x))) * bpow beta (-fexp1 (mag beta x))
          = (1/2) * (1 - bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x))) := by
        rw [mul_assoc, sub_mul, h_bp1, h_bp2]
      have h_bpow_pos_diff : 0 ≤ bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) :=
        le_of_lt (bpow_gt_0 _ _)
      linarith
    have h_zn_x'' : Znearest choice1 (scaled_mantissa beta fexp1 x'')
        = ⌈scaled_mantissa beta fexp1 x⌉ := by
      apply Znearest_imp
      have h_eq : scaled_mantissa beta fexp1 x''
          - ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
          = (x'' - x') * bpow beta (-fexp1 (mag beta x)) := by
        show x'' * bpow beta (-cexp beta fexp1 x'')
            - ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
          = (x'' - x') * bpow beta (-fexp1 (mag beta x))
        rw [show cexp beta fexp1 x'' = fexp1 (mag beta x) from h_cexp_x'',
            h_ceil_real]
        ring
      rw [h_eq]
      rw [abs_mul, abs_of_pos h_bpow_neg_fexp1_pos]
      have h_step : |x'' - x'| * bpow beta (-fexp1 (mag beta x))
          < (1/2) * bpow beta (fexp1 (mag beta x))
            * bpow beta (-fexp1 (mag beta x)) :=
        mul_lt_mul_of_pos_right Hr2 h_bpow_neg_fexp1_pos
      have h_cancel : (1/2) * bpow beta (fexp1 (mag beta x))
          * bpow beta (-fexp1 (mag beta x)) = 1/2 := by
        rw [mul_assoc, ← bpow_plus]
        have : fexp1 (mag beta x) + -fexp1 (mag beta x) = 0 := by ring
        rw [this]
        show (1/2) * bpow beta 0 = 1/2
        show (1/2) * 1 = 1/2
        ring
      linarith
    show round beta fexp1 (Znearest choice1) x''
       = round beta fexp1 (Znearest choice1) x
    unfold round
    rw [h_zn_x, h_zn_x'']
    show F2R (beta := beta) ⟨⌈scaled_mantissa beta fexp1 x⌉, cexp beta fexp1 x''⟩
       = F2R (beta := beta) ⟨⌈scaled_mantissa beta fexp1 x⌉, cexp beta fexp1 x⟩
    rw [h_cexp_x'']
    rfl

/-- Mirror of `_lt_mid_same_place`: when `fexp2 = fexp1` at `mag x` and `x` is
strictly above `midp'`, double rounding agrees with single rounding.

Proof: x is above midp1' means x' - x < (1/2) * ulp1, so both Znearests give
⌈sm fexp1 x⌉. -/
theorem round_round_gt_mid_same_place
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) = fexp1 (mag beta x))
    (Hx' : midp' beta fexp1 x < x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  unfold round_round_eq
  have h_x_ne : x ≠ 0 := ne_of_gt Px
  have h_ulp1 : ulp beta fexp1 x = bpow beta (fexp1 (mag beta x)) := by
    rw [ulp_neq_0 beta fexp1 h_x_ne]; rfl
  set x' := round beta fexp1 (fun y : ℝ => ⌈y⌉) x with hx'_def
  have Hx : x' - x < (1/2) * bpow beta (fexp1 (mag beta x)) := by
    unfold midp' at Hx'
    rw [h_ulp1] at Hx'
    linarith
  have Px'x : 0 ≤ x' - x := by
    have h_up := (round_UP_pt beta fexp1 Vfexp1 x).2.1
    rw [← hx'_def] at h_up
    linarith
  have h_bpow_pos : 0 < bpow beta (fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_bpow_neg_pos : 0 < bpow beta (-fexp1 (mag beta x)) := bpow_gt_0 _ _
  have h_ceil_x' : ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
      * bpow beta (fexp1 (mag beta x)) = x' := rfl
  have h_ceil_real : ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)
      = x' * bpow beta (-fexp1 (mag beta x)) := by
    have h_bpow_inv : bpow beta (-fexp1 (mag beta x))
        = (bpow beta (fexp1 (mag beta x)))⁻¹ := by
      show (beta.val : ℝ)^(-fexp1 (mag beta x))
        = ((beta.val : ℝ)^(fexp1 (mag beta x)))⁻¹
      exact zpow_neg _ _
    rw [h_bpow_inv, ← div_eq_mul_inv, eq_div_iff (ne_of_gt h_bpow_pos)]
    exact h_ceil_x'
  have H_znear : |scaled_mantissa beta fexp1 x
        - ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)| < 1/2 := by
    show |x * bpow beta (-cexp beta fexp1 x)
        - ((⌈scaled_mantissa beta fexp1 x⌉ : ℤ) : ℝ)| < 1/2
    have h_cexp : cexp beta fexp1 x = fexp1 (mag beta x) := rfl
    rw [h_cexp, h_ceil_real]
    have h_eq : x * bpow beta (-fexp1 (mag beta x))
        - x' * bpow beta (-fexp1 (mag beta x))
        = -((x' - x) * bpow beta (-fexp1 (mag beta x))) := by ring
    rw [h_eq, abs_neg, abs_of_nonneg (mul_nonneg Px'x (le_of_lt h_bpow_neg_pos))]
    have h_step : (x' - x) * bpow beta (-fexp1 (mag beta x))
        < (1/2) * bpow beta (fexp1 (mag beta x))
          * bpow beta (-fexp1 (mag beta x)) :=
      mul_lt_mul_of_pos_right Hx h_bpow_neg_pos
    have h_cancel : (1/2) * bpow beta (fexp1 (mag beta x))
        * bpow beta (-fexp1 (mag beta x)) = 1/2 := by
      rw [mul_assoc, ← bpow_plus]
      have : fexp1 (mag beta x) + -fexp1 (mag beta x) = 0 := by ring
      rw [this]
      show (1/2) * bpow beta 0 = 1/2
      show (1/2) * 1 = 1/2
      ring
    linarith
  have h_inner : round beta fexp2 (Znearest choice2) x = x' := by
    unfold round
    show F2R (beta := beta) ⟨Znearest choice2 (scaled_mantissa beta fexp2 x),
                              cexp beta fexp2 x⟩ = x'
    have h_cexp_eq : cexp beta fexp2 x = fexp1 (mag beta x) := by
      show fexp2 (mag beta x) = fexp1 (mag beta x); exact Hf2f1
    have h_sm_eq : scaled_mantissa beta fexp2 x = scaled_mantissa beta fexp1 x := by
      show x * bpow beta (-cexp beta fexp2 x)
        = x * bpow beta (-cexp beta fexp1 x)
      rw [h_cexp_eq]; rfl
    rw [h_sm_eq, h_cexp_eq]
    have h_zn : Znearest choice2 (scaled_mantissa beta fexp1 x)
        = ⌈scaled_mantissa beta fexp1 x⌉ := Znearest_imp _ H_znear
    rw [h_zn]
    exact h_ceil_x'
  rw [h_inner]
  have h_x'_F : generic_format beta fexp1 x' :=
    generic_format_round beta fexp1 Vfexp1 _ x
  rw [round_generic beta fexp1 (Znearest choice1) h_x'_F]
  symm
  unfold round
  show F2R (beta := beta) ⟨Znearest choice1 (scaled_mantissa beta fexp1 x),
                            cexp beta fexp1 x⟩ = x'
  rw [Znearest_imp _ H_znear]
  exact h_ceil_x'

/-- The full `_gt_mid_further_place`: weakens the upper bound on `x''` to the
structural hypothesis `fexp1(mag x) ≤ mag x`. Case-splits on whether
`x'' < bpow(mag x)` (defers to `_further_place'`) or `bpow(mag x) ≤ x''`
(the edge case: integer arithmetic forces `x'' = bpow(mag x)`, then both
rounds yield `bpow(mag x)`).

Lean-native route for the edge case: rewrite `x'' = bpow(mag x)`, then use
`round_generic` on the LHS (since `bpow(mag x) ∈ F1`) and `Znearest_imp` on
the RHS with witness `β^(mag x - fexp1(mag x))`. -/
theorem round_round_gt_mid_further_place
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1)
    (Hf1 : fexp1 (mag beta x) ≤ mag beta x)
    (Hx2' : midp' beta fexp1 x + (1/2) * ulp beta fexp2 x < x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  by_cases Hx1 : round beta fexp2 (Znearest choice2) x < bpow beta (mag beta x)
  · -- Easy case: defer to _further_place'.
    exact round_round_gt_mid_further_place' beta Vfexp1 Vfexp2 choice1 choice2 Px Hf2f1 Hx1 Hx2'
  · -- Edge case: bpow(mag x) ≤ x''. We show x'' = bpow(mag x) exactly.
    push_neg at Hx1
    unfold round_round_eq
    have h_x_ne : x ≠ 0 := ne_of_gt Px
    have h_ulp2 : ulp beta fexp2 x = bpow beta (fexp2 (mag beta x)) := by
      rw [ulp_neq_0 beta fexp2 h_x_ne]; rfl
    have h_x_lt_bpow : x < bpow beta (mag beta x) := by
      have := bpow_mag_gt beta x
      rw [abs_of_pos Px] at this; exact this
    have h_bp_f2_pos : 0 < bpow beta (fexp2 (mag beta x)) := bpow_gt_0 _ _
    have h_bp_neg_f1_pos : 0 < bpow beta (-fexp1 (mag beta x)) := bpow_gt_0 _ _
    -- Error bound at fexp2: |x'' - x| ≤ (1/2) * bpow(fexp2(mag x))
    have h_err2 : |round beta fexp2 (Znearest choice2) x - x|
        ≤ (1/2) * bpow beta (fexp2 (mag beta x)) := by
      have h := error_le_half_ulp beta fexp2 Vfexp2 choice2 x
      rw [h_ulp2] at h; exact h
    -- Upper bound: x'' < bpow(mag x) + (1/2) * bpow(fexp2(mag x))
    have h_upper : round beta fexp2 (Znearest choice2) x
        < bpow beta (mag beta x) + (1/2) * bpow beta (fexp2 (mag beta x)) := by
      have h_abs := abs_le.mp h_err2
      linarith
    -- x'' = (Znearest choice2 sm) * bpow(fexp2(mag x))
    set n_m := Znearest choice2 (scaled_mantissa beta fexp2 x) with hn_m_def
    have h_x''_form : round beta fexp2 (Znearest choice2) x
        = (n_m : ℝ) * bpow beta (fexp2 (mag beta x)) := by
      show F2R (beta := beta) ⟨n_m, cexp beta fexp2 x⟩
        = (n_m : ℝ) * bpow beta (fexp2 (mag beta x))
      unfold F2R; rfl
    -- k = mag x - fexp2(mag x); nonneg and bpow(mag x) = bpow(k) * bpow(fexp2)
    have h_k_nn : 0 ≤ mag beta x - fexp2 (mag beta x) := by linarith
    set k := mag beta x - fexp2 (mag beta x) with hk_def
    have h_bp_mag_eq : bpow beta (mag beta x)
        = bpow beta k * bpow beta (fexp2 (mag beta x)) := by
      rw [← bpow_plus]
      have h : k + fexp2 (mag beta x) = mag beta x := by rw [hk_def]; ring
      rw [h]
    have h_pow_eq : ((beta.val ^ k.toNat : ℤ) : ℝ) = bpow beta k :=
      IZR_Zpower beta h_k_nn
    -- Lower: bpow(k) ≤ (n_m : ℝ) from Hx1.
    have h_lower : bpow beta k ≤ (n_m : ℝ) := by
      have h := Hx1
      rw [h_x''_form, h_bp_mag_eq] at h
      exact (mul_le_mul_iff_of_pos_right h_bp_f2_pos).mp h
    -- Upper: (n_m : ℝ) < bpow(k) + 1/2 from h_upper.
    have h_n_m_real_lt : (n_m : ℝ) < bpow beta k + 1/2 := by
      have h := h_upper
      rw [h_x''_form, h_bp_mag_eq] at h
      have h_arith : (n_m : ℝ) * bpow beta (fexp2 (mag beta x))
          < (bpow beta k + 1/2) * bpow beta (fexp2 (mag beta x)) := by
        have : (bpow beta k + 1/2) * bpow beta (fexp2 (mag beta x))
            = bpow beta k * bpow beta (fexp2 (mag beta x))
              + 1/2 * bpow beta (fexp2 (mag beta x)) := by ring
        linarith
      exact (mul_lt_mul_iff_of_pos_right h_bp_f2_pos).mp h_arith
    -- Integer arithmetic: n_m = β^k.toNat.
    have h_n_m_eq : n_m = (beta.val ^ k.toNat : ℤ) := by
      have h_lower_int : (beta.val ^ k.toNat : ℤ) ≤ n_m := by
        have h := h_lower
        rw [← h_pow_eq] at h
        exact_mod_cast h
      have h_upper_int : n_m ≤ (beta.val ^ k.toNat : ℤ) := by
        by_contra h_gt
        push_neg at h_gt
        have h_real : ((beta.val ^ k.toNat : ℤ) : ℝ) + 1 ≤ (n_m : ℝ) := by
          exact_mod_cast h_gt
        rw [h_pow_eq] at h_real
        linarith
      omega
    -- Combine: x'' = bpow(mag x).
    have h_x''_eq : round beta fexp2 (Znearest choice2) x = bpow beta (mag beta x) := by
      rw [h_x''_form, h_bp_mag_eq]
      have h_real : (n_m : ℝ) = bpow beta k := by
        rw [← h_pow_eq]; exact_mod_cast h_n_m_eq
      rw [h_real]
    -- Step 2: bpow(mag x) ∈ F1 via fexp1(mag x + 1) ≤ mag x.
    have h_fexp1_succ : fexp1 (mag beta x + 1) ≤ mag beta x := by
      rcases lt_or_eq_of_le Hf1 with h_lt | h_eq
      · exact (Vfexp1 (mag beta x)).1 h_lt
      · have h_le : mag beta x ≤ fexp1 (mag beta x) := h_eq.ge
        have hsta := (Vfexp1 (mag beta x)).2 h_le
        have h1 : fexp1 (fexp1 (mag beta x) + 1) ≤ fexp1 (mag beta x) := hsta.1
        rw [h_eq] at h1
        exact h1
    have h_bpow_F1 : generic_format beta fexp1 (bpow beta (mag beta x)) :=
      generic_format_bpow beta fexp1 (mag beta x) h_fexp1_succ
    -- Step 3: substitute x'' = bpow(mag x) on LHS; both sides reduce to bpow(mag x).
    rw [h_x''_eq]
    rw [round_generic beta fexp1 _ h_bpow_F1]
    -- Goal: bpow(mag x) = round beta fexp1 (Znearest choice1) x
    -- Use Znearest_imp with n = β^(mag x - fexp1(mag x)).
    have h_k1_nn : 0 ≤ mag beta x - fexp1 (mag beta x) := by linarith
    set k1 := mag beta x - fexp1 (mag beta x) with hk1_def
    have h_pow_k1 : ((beta.val ^ k1.toNat : ℤ) : ℝ) = bpow beta k1 :=
      IZR_Zpower beta h_k1_nn
    have h_bp_mag_eq_1 : bpow beta (mag beta x)
        = bpow beta k1 * bpow beta (fexp1 (mag beta x)) := by
      rw [← bpow_plus]
      have h : k1 + fexp1 (mag beta x) = mag beta x := by rw [hk1_def]; ring
      rw [h]
    have h_zn1 : Znearest choice1 (scaled_mantissa beta fexp1 x)
        = (beta.val ^ k1.toNat : ℤ) := by
      apply Znearest_imp
      have h_cexp : cexp beta fexp1 x = fexp1 (mag beta x) := rfl
      show |x * bpow beta (-cexp beta fexp1 x) - ((beta.val ^ k1.toNat : ℤ) : ℝ)| < 1/2
      rw [h_cexp, h_pow_k1]
      have h_bp_k1_form : bpow beta k1
          = bpow beta (mag beta x) * bpow beta (-fexp1 (mag beta x)) := by
        rw [← bpow_plus]
        have : mag beta x + -fexp1 (mag beta x) = k1 := by rw [hk1_def]; ring
        rw [this]
      rw [h_bp_k1_form]
      have h_eq_split : x * bpow beta (-fexp1 (mag beta x))
          - bpow beta (mag beta x) * bpow beta (-fexp1 (mag beta x))
          = (x - bpow beta (mag beta x)) * bpow beta (-fexp1 (mag beta x)) := by ring
      rw [h_eq_split, abs_mul, abs_of_pos h_bp_neg_f1_pos]
      have h_abs_x : |x - bpow beta (mag beta x)| = bpow beta (mag beta x) - x := by
        rw [show x - bpow beta (mag beta x) = -(bpow beta (mag beta x) - x) from by ring,
            abs_neg, abs_of_nonneg (by linarith)]
      rw [h_abs_x]
      have h_diff_le : bpow beta (mag beta x) - x
          ≤ (1/2) * bpow beta (fexp2 (mag beta x)) := by
        have h_abs := abs_le.mp h_err2
        rw [h_x''_eq] at h_abs
        linarith
      have h_step : (bpow beta (mag beta x) - x) * bpow beta (-fexp1 (mag beta x))
          ≤ (1/2) * bpow beta (fexp2 (mag beta x)) * bpow beta (-fexp1 (mag beta x)) :=
        mul_le_mul_of_nonneg_right h_diff_le (le_of_lt h_bp_neg_f1_pos)
      have h_combine : (1/2) * bpow beta (fexp2 (mag beta x))
            * bpow beta (-fexp1 (mag beta x))
          = (1/2) * bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := by
        rw [mul_assoc, ← bpow_plus]; rfl
      have h_bpow_le : bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x))
          ≤ bpow beta (-1 : ℤ) := bpow_le beta (by linarith)
      have h_bpow_neg1 : bpow beta (-1 : ℤ) ≤ 1/2 := by
        show (beta.val : ℝ)^(-1 : ℤ) ≤ 1/2
        rw [zpow_neg, zpow_one, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast beta.prop
      calc (bpow beta (mag beta x) - x) * bpow beta (-fexp1 (mag beta x))
          ≤ (1/2) * bpow beta (fexp2 (mag beta x)) * bpow beta (-fexp1 (mag beta x)) := h_step
        _ = (1/2) * bpow beta (fexp2 (mag beta x) - fexp1 (mag beta x)) := h_combine
        _ ≤ (1/2) * bpow beta (-1 : ℤ) := by
            apply mul_le_mul_of_nonneg_left h_bpow_le (by linarith)
        _ ≤ (1/2) * (1/2) := by
            apply mul_le_mul_of_nonneg_left h_bpow_neg1 (by linarith)
        _ < 1/2 := by linarith
    -- Compute round_N x at fexp1 = bpow(mag x).
    show bpow beta (mag beta x) = round beta fexp1 (Znearest choice1) x
    unfold round
    rw [h_zn1]
    show bpow beta (mag beta x)
       = F2R (beta := beta) ⟨(beta.val ^ k1.toNat : ℤ), cexp beta fexp1 x⟩
    unfold F2R
    show bpow beta (mag beta x)
       = ((beta.val ^ k1.toNat : ℤ) : ℝ) * bpow beta (fexp1 (mag beta x))
    rw [h_pow_k1, ← h_bp_mag_eq_1]

/-- The mirror of `round_round_lt_mid`: dispatches on whether `fexp2(mag x)`
equals `fexp1(mag x)` (same-place) or is strictly below (further-place). -/
theorem round_round_gt_mid
    (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x))
    (Hf1 : fexp1 (mag beta x) ≤ mag beta x)
    (Hx : midp' beta fexp1 x < x)
    (Hx' : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1
         → midp' beta fexp1 x + (1/2) * ulp beta fexp2 x < x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  rcases le_or_gt (fexp1 (mag beta x)) (fexp2 (mag beta x)) with Hf2' | Hf2'
  · -- fexp1(mag x) ≤ fexp2(mag x): combined with Hf2f1, fexp2 = fexp1
    have Hf2'' : fexp2 (mag beta x) = fexp1 (mag beta x) := le_antisymm Hf2f1 Hf2'
    exact round_round_gt_mid_same_place beta Vfexp1 choice1 choice2 Px Hf2'' Hx
  · -- fexp2(mag x) < fexp1(mag x): apply further_place
    have Hf2'' : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1 := by linarith
    exact round_round_gt_mid_further_place beta Vfexp1 Vfexp2 choice1 choice2 Px
      Hf2'' Hf1 (Hx' Hf2'')

/-! ## Multiplication theorems

When `x` and `y` are in the target format `F1`, the product `x * y` is
representable in `F2` provided `fexp2` is "fine enough" relative to `fexp1`.
This makes double rounding for multiplication innocuous. -/

/-- The hypothesis on `(fexp1, fexp2)` for `round_round_mult`: `fexp2` must
be at most `fexp1(ex) + fexp1(ey)` at both possible magnitudes of `x * y`. -/
def round_round_mult_hyp (fexp1 fexp2 : ℤ → ℤ) : Prop :=
  (∀ ex ey : ℤ, fexp2 (ex + ey) ≤ fexp1 ex + fexp1 ey)
  ∧ (∀ ex ey : ℤ, fexp2 (ex + ey - 1) ≤ fexp1 ex + fexp1 ey)

/-- When `x`, `y ∈ F1` and the multiplication hypothesis holds, the product
`x * y` is in `F2`. -/
theorem round_round_mult_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Hfexp : round_round_mult_hyp fexp1 fexp2) {x y : ℝ}
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x * y) := by
  by_cases Zx : x = 0
  · rw [Zx, zero_mul]; exact generic_format_0 beta fexp2
  · by_cases Zy : y = 0
    · rw [Zy, mul_zero]; exact generic_format_0 beta fexp2
    · -- Write x = mx * bpow(fexp1(mag x)), y = my * bpow(fexp1(mag y))
      set mx := Ztrunc (scaled_mantissa beta fexp1 x) with hmx_def
      set my := Ztrunc (scaled_mantissa beta fexp1 y) with hmy_def
      have h_Fx : x = (mx : ℝ) * bpow beta (fexp1 (mag beta x)) := Fx
      have h_Fy : y = (my : ℝ) * bpow beta (fexp1 (mag beta y)) := Fy
      -- The float representation of x*y at exponent fexp1(mag x) + fexp1(mag y).
      set fxy : float beta := ⟨mx * my, fexp1 (mag beta x) + fexp1 (mag beta y)⟩
        with hfxy_def
      have Hxy : x * y = F2R fxy := by
        show x * y = ((mx * my : ℤ) : ℝ) * bpow beta
            (fexp1 (mag beta x) + fexp1 (mag beta y))
        rw [Int.cast_mul, bpow_plus]
        have h_assoc : (mx : ℝ) * (my : ℝ)
              * (bpow beta (fexp1 (mag beta x)) * bpow beta (fexp1 (mag beta y)))
            = ((mx : ℝ) * bpow beta (fexp1 (mag beta x)))
                * ((my : ℝ) * bpow beta (fexp1 (mag beta y))) := by ring
        rw [h_assoc, ← h_Fx, ← h_Fy]
      apply generic_format_F2R' beta fexp2 fxy Hxy.symm
      intro h_xy_ne
      -- cexp(x*y) = fexp2(mag(x*y)).
      show fexp2 (mag beta (x * y)) ≤ fxy.Fexp
      show fexp2 (mag beta (x * y)) ≤ fexp1 (mag beta x) + fexp1 (mag beta y)
      -- By mag_mult, mag(x*y) is in {mag x + mag y - 1, mag x + mag y}.
      have h_mag := mag_mult beta Zx Zy
      have h_mag_lo : mag beta x + mag beta y - 1 ≤ mag beta (x * y) := h_mag.1
      have h_mag_hi : mag beta (x * y) ≤ mag beta x + mag beta y := h_mag.2
      -- Two cases.
      rcases lt_or_eq_of_le h_mag_lo with h_strict | h_eq
      · -- mag(x*y) = mag x + mag y (the upper case).
        have h_eq2 : mag beta (x * y) = mag beta x + mag beta y := by
          linarith
        rw [h_eq2]; exact Hfexp.1 (mag beta x) (mag beta y)
      · -- mag(x*y) = mag x + mag y - 1 (the lower case).
        rw [← h_eq]; exact Hfexp.2 (mag beta x) (mag beta y)

/-- The keystone: if both `x` and `y` are in `F1` and the multiplication
hypothesis holds, then double rounding (first to `F2`, then to `F1`) of
`x * y` equals direct rounding to `F1`. -/
theorem round_round_mult (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (Hfexp : round_round_mult_hyp fexp1 fexp2) {x y : ℝ}
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round beta fexp1 rnd (round beta fexp2 rnd (x * y))
      = round beta fexp1 rnd (x * y) := by
  have Hxy : round beta fexp2 rnd (x * y) = x * y :=
    round_generic beta fexp2 rnd (round_round_mult_aux beta fexp1 fexp2 Hfexp Fx Fy)
  rw [Hxy]

/-! ### Format-specific multiplication corollaries -/

/-- FLX double-rounding for multiplication: when `2 * prec ≤ prec'`, double
rounding via `FLX prec'` is innocuous for `x * y` with `x, y ∈ FLX prec`. -/
theorem round_round_mult_FLX (beta : radix) (prec prec' : ℤ)
    (hprec : 0 < prec) (_hprec' : 0 < prec')
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (Hprec : 2 * prec ≤ prec') {x y : ℝ}
    (Fx : FLX_format beta prec x) (Fy : FLX_format beta prec y) :
    round beta (FLX_exp prec) rnd
        (round beta (FLX_exp prec') rnd (x * y))
      = round beta (FLX_exp prec) rnd (x * y) := by
  apply round_round_mult beta (FLX_exp prec) (FLX_exp prec') rnd ?_
    (generic_format_FLX beta prec hprec Fx) (generic_format_FLX beta prec hprec Fy)
  refine ⟨?_, ?_⟩ <;> (intro ex ey; unfold FLX_exp; linarith)

/-- FLT double-rounding for multiplication: needs `emin' ≤ 2 * emin` (the
inner format reaches lower exponents) and `2 * prec ≤ prec'` (the inner
format has at least twice the precision). -/
theorem round_round_mult_FLT (beta : radix) (emin prec emin' prec' : ℤ)
    (hprec : 0 < prec) (_hprec' : 0 < prec')
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (Hemin : emin' ≤ 2 * emin) (Hprec : 2 * prec ≤ prec') {x y : ℝ}
    (Fx : FLT_format beta emin prec x) (Fy : FLT_format beta emin prec y) :
    round beta (FLT_exp emin prec) rnd
        (round beta (FLT_exp emin' prec') rnd (x * y))
      = round beta (FLT_exp emin prec) rnd (x * y) := by
  apply round_round_mult beta (FLT_exp emin prec) (FLT_exp emin' prec') rnd ?_
    (generic_format_FLT beta emin prec hprec Fx)
    (generic_format_FLT beta emin prec hprec Fy)
  refine ⟨?_, ?_⟩
  all_goals
    intro ex ey
    unfold FLT_exp
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · have h1 : ex - prec ≤ max (ex - prec) emin := le_max_left _ _
      have h2 : ey - prec ≤ max (ey - prec) emin := le_max_left _ _
      linarith
    · have h1 : emin ≤ max (ex - prec) emin := le_max_right _ _
      have h2 : emin ≤ max (ey - prec) emin := le_max_right _ _
      linarith

/-- FTZ double-rounding for multiplication: needs `emin' + prec' ≤ 2*emin + prec`
and `2 * prec ≤ prec'`. -/
theorem round_round_mult_FTZ (beta : radix) (emin prec emin' prec' : ℤ)
    (hprec : 0 < prec) (_hprec' : 0 < prec')
    (rnd : ℝ → ℤ) [Valid_rnd rnd]
    (Hemin : emin' + prec' ≤ 2 * emin + prec) (Hprec : 2 * prec ≤ prec') {x y : ℝ}
    (Fx : FTZ_format beta emin prec x) (Fy : FTZ_format beta emin prec y) :
    round beta (FTZ_exp emin prec) rnd
        (round beta (FTZ_exp emin' prec') rnd (x * y))
      = round beta (FTZ_exp emin prec) rnd (x * y) := by
  apply round_round_mult beta (FTZ_exp emin prec) (FTZ_exp emin' prec') rnd ?_
    (generic_format_FTZ beta emin prec hprec Fx)
    (generic_format_FTZ beta emin prec hprec Fy)
  refine ⟨?_, ?_⟩
  all_goals
    intro ex ey
    unfold FTZ_exp
    split_ifs <;> omega

/-! ## Bridge: round_round_mid_cases

A wrapper around the `_further_place` family. Dispatches on the position of
`x` relative to the midpoint: far below (uses `_lt_mid_further_place`), far
above (uses `_gt_mid_further_place`), or within `(1/2)*ulp2` of the midpoint
(left to the caller via the `Cmid` callback). Used downstream by
`round_round_sqrt`. -/

theorem round_round_mid_cases (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool) {x : ℝ}
    (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1)
    (Hf1 : fexp1 (mag beta x) ≤ mag beta x)
    (Cmid : |x - midp beta fexp1 x| ≤ (1/2) * ulp beta fexp2 x
         → round_round_eq beta fexp1 fexp2 choice1 choice2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  rcases generic_format_EM beta fexp1 Vfexp1 x with Fx | Nfx
  · -- x ∈ F1: x ∈ F2 too (via fexp2 ≤ fexp1 - 1), so round at fexp2 fixes x.
    unfold round_round_eq
    have h_incl : generic_format beta fexp2 x := by
      apply generic_inclusion_mag beta fexp1 fexp2
      · intro _; linarith
      · exact Fx
    rw [round_generic beta fexp2 _ h_incl]
  · -- x ∉ F1: round_UP x = round_DN x + ulp1.
    have h_x_ne : x ≠ 0 := ne_of_gt Px
    set rd := round beta fexp1 (fun y : ℝ => ⌊y⌋) x with hrd_def
    have h_ceil : round beta fexp1 (fun y : ℝ => ⌈y⌉) x = rd + ulp beta fexp1 x :=
      round_UP_DN_ulp beta fexp1 Nfx
    have Pxx_rd : rd ≤ x := (round_DN_pt beta fexp1 Vfexp1 x).2.1
    rcases lt_or_ge (x - rd) ((1/2) * (ulp beta fexp1 x - ulp beta fexp2 x))
      with h_lt | h_ge
    · -- x - rd < (1/2)*(ulp1 - ulp2): x below midpoint by ulp2/2.
      apply round_round_lt_mid_further_place beta Vfexp1 Vfexp2 choice1 choice2 Px
        Hf2f1 Hf1
      unfold midp
      rw [← hrd_def]
      linarith
    · -- (1/2)*(ulp1 - ulp2) ≤ x - rd.
      rcases lt_or_ge ((1/2) * (ulp beta fexp1 x + ulp beta fexp2 x)) (x - rd)
        with h_lt2 | h_le2
      · -- (1/2)*(ulp1 + ulp2) < x - rd: x above midpoint by ulp2/2.
        apply round_round_gt_mid_further_place beta Vfexp1 Vfexp2 choice1 choice2 Px
          Hf2f1 Hf1
        unfold midp'
        rw [h_ceil]
        linarith
      · -- x - rd ≤ (1/2)*(ulp1 + ulp2): |x - midp| ≤ (1/2)*ulp2.
        apply Cmid
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · unfold midp; rw [← hrd_def]; linarith
        · unfold midp; rw [← hrd_def]; linarith

/-! ## Square root theorems

When `x ∈ F1` and the format pair `(fexp1, fexp2)` is "sqrt-compatible"
(see `round_round_sqrt_hyp`), double-rounding `Real.sqrt x` is innocuous.

The proof structure: `round_round_sqrt_aux` shows that `Real.sqrt x` is more
than `ulp2/2` away from the F1 midpoint, then `round_round_sqrt` dispatches
via `round_round_mid_cases`. -/

/-- The hypothesis on `(fexp1, fexp2)` for `round_round_sqrt`: three
conjuncts ensuring the inner precision is "twice plus 2" the outer. -/
def round_round_sqrt_hyp (fexp1 fexp2 : ℤ → ℤ) : Prop :=
  (∀ ex : ℤ, 2 * fexp1 ex ≤ fexp1 (2 * ex))
  ∧ (∀ ex : ℤ, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1))
  ∧ (∀ ex : ℤ, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 2)

/-- For `0 < x`, the magnitude of `x` is either `2 * mag(√x) - 1` or
`2 * mag(√x)`. -/
theorem mag_sqrt_disj (beta : radix) {x : ℝ} (Px : 0 < x) :
    mag beta x = 2 * mag beta (Real.sqrt x) - 1
    ∨ mag beta x = 2 * mag beta (Real.sqrt x) := by
  rw [mag_sqrt beta Px]
  omega

/-- A radix is at least 2, so `bpow(-2) ≤ 1/4`. Used in the algebraic
chain inside `round_round_sqrt_aux`. -/
private theorem bpow_neg_two_le_quarter (beta : radix) :
    bpow beta (-2) ≤ (1 : ℝ) / 4 := by
  have h2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have h_b2_eq : bpow beta 2 = (beta.val : ℝ) * (beta.val : ℝ) := by
    show (beta.val : ℝ) ^ (2 : ℤ) = (beta.val : ℝ) * (beta.val : ℝ)
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; ring
  have h_b2_ge_4 : (4 : ℝ) ≤ bpow beta 2 := by rw [h_b2_eq]; nlinarith
  have h_b2_pos : 0 < bpow beta 2 := bpow_gt_0 _ _
  have h_inv : bpow beta (-2) = 1 / bpow beta 2 := by
    show (beta.val : ℝ) ^ (-2 : ℤ) = 1 / (beta.val : ℝ) ^ (2 : ℤ)
    rw [zpow_neg]; field_simp
  rw [h_inv]
  exact one_div_le_one_div_of_le (by norm_num) h_b2_ge_4

/-- **The sqrt mid-rounding auxiliary lemma.**

`√x` is more than `(1/2)·ulp2(√x)` away from the F1 midpoint, given the
`round_round_sqrt_hyp` precision condition and a precision gap of at least 1
between fexp2 and fexp1 at `mag(√x)`.

Proof structure (by contradiction):
- Setup: `a := round_DN(√x)` at fexp1, `u1 := ulp1(√x)`, `u2 := ulp2(√x)`,
  `b := (u1 - u2)/2`, `b' := (u1 + u2)/2`.
- Hypothesis gives `a + b ≤ √x ≤ a + b'`. Squaring (both sides ≥ 0):
  `Hsl : a² + u1·a - u2·a + b² ≤ x` and `Hsr : x ≤ a² + u1·a + u2·a + b'²`.
- Derive `Hf1 : 2·fexp1(mag √x) ≤ fexp1(mag x)` (from `mag_sqrt_disj` + Hexp.1/2.1)
  and `Hlx : fexp1(2·mag √x) < 2·mag √x` (from `mag_generic_gt` + `valid_exp_large`).
- Case `a = 0`: `x ≤ b'² < u1² ≤ bpow(fexp1 mag_x)`. Then `Ztrunc(scaled) = 0`,
  so `Fx` gives `x = 0` — contradiction.
- Case `a > 0`: derive `Hl' : 0 < -u2·a + b²` algebraically, and `Hr' : x ≤ a² + u1·a`
  by an integer-multiple-of-`u1²` argument (both `x` and `a² + u1·a` are integer
  multiples of `bpow(2·fexp1 mag_s)`, and the gap `u2·a + b'² < u1²`). Combining
  `Hsl + Hl'` gives `a² + u1·a < x`; with `Hr'` we get a contradiction. -/
theorem round_round_sqrt_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    {x : ℝ} (Px : 0 < x)
    (Hf2 : fexp2 (mag beta (Real.sqrt x)) ≤ fexp1 (mag beta (Real.sqrt x)) - 1)
    (Fx : generic_format beta fexp1 x) :
    (1/2) * ulp beta fexp2 (Real.sqrt x)
      < |Real.sqrt x - midp beta fexp1 (Real.sqrt x)| := by
  by_contra Hcontra
  push_neg at Hcontra
  -- Hcontra : |√x - midp1| ≤ (1/2) * ulp2(√x)
  obtain ⟨Hex1, Hex21, Hex22⟩ := Hexp
  -- Setup: s := √x, basic positivity
  set s := Real.sqrt x with hs_def
  have Ps : 0 < s := Real.sqrt_pos.mpr Px
  have Ps_ne : s ≠ 0 := ne_of_gt Ps
  have Ps_nonneg : 0 ≤ s := le_of_lt Ps
  have h_s_sq : s * s = x := Real.mul_self_sqrt (le_of_lt Px)
  -- Set u1, u2 as bpow values
  set mag_s := mag beta s with hms_def
  set u1 := bpow beta (fexp1 mag_s) with hu1_def
  set u2 := bpow beta (fexp2 mag_s) with hu2_def
  have h_u1_pos : 0 < u1 := bpow_gt_0 _ _
  have h_u2_pos : 0 < u2 := bpow_gt_0 _ _
  have h_u2_lt_u1 : u2 < u1 := bpow_lt beta (by linarith [Hf2])
  -- ulps in terms of u1, u2
  have h_ulp1_s : ulp beta fexp1 s = u1 := by rw [ulp_neq_0 beta fexp1 Ps_ne]; rfl
  have h_ulp2_s : ulp beta fexp2 s = u2 := by rw [ulp_neq_0 beta fexp2 Ps_ne]; rfl
  -- Set a = round_DN(s) at fexp1; basic properties
  set a := round beta fexp1 (fun y : ℝ => ⌊y⌋) s with ha_def
  have h_DN : Rnd_DN_pt (generic_format beta fexp1) s a := round_DN_pt beta fexp1 Vfexp1 s
  have h_a_format : generic_format beta fexp1 a := h_DN.1
  have h_a_le_s : a ≤ s := h_DN.2.1
  have h_a_nonneg : 0 ≤ a := by
    have h_0_F1 : generic_format beta fexp1 0 := generic_format_0 beta fexp1
    exact h_DN.2.2 0 h_0_F1 Ps_nonneg
  -- midp = a + u1/2
  have h_midp : midp beta fexp1 s = a + (1/2) * u1 := by
    unfold midp
    rw [h_ulp1_s]
  -- b, b'
  set b := (u1 - u2) / 2 with hb_def
  set b' := (u1 + u2) / 2 with hb'_def
  have h_b_pos : 0 < b := by show (u1 - u2) / 2 > 0; linarith
  have h_b'_pos : 0 < b' := by show (u1 + u2) / 2 > 0; linarith
  -- Extract Hl/Hr from Hcontra via abs_le
  rw [h_ulp2_s, h_midp] at Hcontra
  -- Hcontra : |s - (a + (1/2) * u1)| ≤ (1/2) * u2
  rw [abs_le] at Hcontra
  obtain ⟨h_Hcl, h_Hcr⟩ := Hcontra
  have Hl : a + b ≤ s := by show a + (u1 - u2)/2 ≤ s; linarith
  have Hr : s ≤ a + b' := by show s ≤ a + (u1 + u2)/2; linarith
  -- Squaring step: Hsl, Hsr
  have h_ab_nonneg : 0 ≤ a + b := by linarith
  have h_ab'_nonneg : 0 ≤ a + b' := by linarith
  have Hsl : a * a + u1 * a - u2 * a + b * b ≤ x := by
    have h1 : (a + b) * (a + b) ≤ s * s :=
      mul_self_le_mul_self h_ab_nonneg Hl
    have h2 : (a + b) * (a + b) = a * a + u1 * a - u2 * a + b * b := by
      show (a + (u1 - u2)/2) * (a + (u1 - u2)/2)
        = a * a + u1 * a - u2 * a + (u1 - u2)/2 * ((u1 - u2)/2)
      ring
    linarith [h1, h2.symm, h_s_sq]
  have Hsr : x ≤ a * a + u1 * a + u2 * a + b' * b' := by
    have h1 : s * s ≤ (a + b') * (a + b') :=
      mul_self_le_mul_self Ps_nonneg Hr
    have h2 : (a + b') * (a + b') = a * a + u1 * a + u2 * a + b' * b' := by
      show (a + (u1 + u2)/2) * (a + (u1 + u2)/2)
        = a * a + u1 * a + u2 * a + (u1 + u2)/2 * ((u1 + u2)/2)
      ring
    linarith [h1, h2, h_s_sq]
  -- Hf1, Hlx
  have h_x_ne : x ≠ 0 := ne_of_gt Px
  have h_mag_lt : fexp1 (mag beta x) < mag beta x :=
    mag_generic_gt beta fexp1 Vfexp1 h_x_ne Fx
  have Hf1 : 2 * fexp1 mag_s ≤ fexp1 (mag beta x) := by
    rcases mag_sqrt_disj beta Px with h | h
    · rw [h]; exact Hex21 mag_s
    · rw [h]; exact Hex1 mag_s
  have Hlx : fexp1 (2 * mag_s) < 2 * mag_s := by
    rcases mag_sqrt_disj beta Px with h | h
    · -- mag x = 2*mag_s - 1, so 2*mag_s = mag x + 1
      have h_mx_le : mag beta x ≤ 2 * mag_s := by linarith
      exact valid_exp_large Vfexp1 h_mag_lt h_mx_le
    · -- mag x = 2*mag_s
      have h_mx_eq : mag beta x = 2 * mag_s := h
      rw [← h_mx_eq]; exact h_mag_lt
  -- Hexp.2.2 applied at mag_s with Hlx
  have h_hexp22 : fexp2 mag_s + mag_s ≤ 2 * fexp1 mag_s - 2 := Hex22 mag_s Hlx
  -- Case split on a = 0
  by_cases Za : a = 0
  · -- a = 0 case
    -- From Hsr: x ≤ b'²
    have Hsr_a0 : x ≤ b' * b' := by
      rw [Za] at Hsr
      have : a * a + u1 * a + u2 * a + b' * b' = b' * b' := by rw [Za]; ring
      linarith [Hsr, this]
    -- b' < u1
    have h_b'_lt_u1 : b' < u1 := by
      show (u1 + u2)/2 < u1
      linarith
    -- b'² < u1²
    have h_b'_sq_lt : b' * b' < u1 * u1 :=
      mul_lt_mul' (le_of_lt h_b'_lt_u1) h_b'_lt_u1 (le_of_lt h_b'_pos) h_u1_pos
    -- u1*u1 = bpow(2*fexp1 mag_s) ≤ bpow(fexp1 mag_x)
    have h_u1_sq_eq : u1 * u1 = bpow beta (2 * fexp1 mag_s) := by
      show bpow beta (fexp1 mag_s) * bpow beta (fexp1 mag_s) = bpow beta (2 * fexp1 mag_s)
      rw [← bpow_plus]; congr 1; ring
    have h_x_lt : x < bpow beta (fexp1 (mag beta x)) := by
      calc x ≤ b' * b' := Hsr_a0
        _ < u1 * u1 := h_b'_sq_lt
        _ = bpow beta (2 * fexp1 mag_s) := h_u1_sq_eq
        _ ≤ bpow beta (fexp1 (mag beta x)) := bpow_le beta Hf1
    -- Scaled mantissa is in (0, 1), so Ztrunc = 0
    have h_bpow_pos : 0 < bpow beta (-fexp1 (mag beta x)) := bpow_gt_0 _ _
    have h_bpow_prod : bpow beta (fexp1 (mag beta x)) * bpow beta (-fexp1 (mag beta x)) = 1 := by
      rw [← bpow_plus]; simp
    have h_sm_pos : 0 < x * bpow beta (-fexp1 (mag beta x)) :=
      mul_pos Px h_bpow_pos
    have h_sm_lt_1 : x * bpow beta (-fexp1 (mag beta x)) < 1 := by
      have := (mul_lt_mul_iff_of_pos_right h_bpow_pos).mpr h_x_lt
      rw [h_bpow_prod] at this
      exact this
    have h_ztrunc_0 : Ztrunc (x * bpow beta (-fexp1 (mag beta x))) = 0 := by
      unfold Ztrunc
      rw [if_neg (not_lt.mpr (le_of_lt h_sm_pos))]
      exact Int.floor_eq_zero_iff.mpr ⟨le_of_lt h_sm_pos, h_sm_lt_1⟩
    -- Derive x = 0
    have h_x_eq_0 : x = 0 := by
      have hFx : x = (Ztrunc (x * bpow beta (-fexp1 (mag beta x))) : ℝ)
          * bpow beta (fexp1 (mag beta x)) := Fx
      rw [h_ztrunc_0] at hFx
      simp at hFx
      exact hFx
    exact absurd h_x_eq_0 h_x_ne
  · -- a > 0 case
    have Pa : 0 < a := lt_of_le_of_ne h_a_nonneg (Ne.symm Za)
    -- mag a = mag s = mag_s
    have h_mag_a : mag beta a = mag_s := by
      show mag beta a = mag beta s
      have h_round_pos : 0 < round beta fexp1 (fun y : ℝ => ⌊y⌋) s := by rw [← ha_def]; exact Pa
      exact mag_DN beta fexp1 Vfexp1 h_round_pos
    -- ulp a = u1
    have h_ulp_a : ulp beta fexp1 a = u1 := by
      rw [ulp_neq_0 beta fexp1 (ne_of_gt Pa)]
      show bpow beta (fexp1 (mag beta a)) = u1
      rw [h_mag_a]
    -- a < bpow(mag s) (since 0 < a ≤ s < bpow(mag s))
    have h_s_lt_bpow_mag_s : s < bpow beta mag_s := by
      have := bpow_mag_gt beta s
      rw [abs_of_nonneg Ps_nonneg] at this
      exact this
    have h_a_lt_bpow_mag_s : a < bpow beta mag_s :=
      lt_of_le_of_lt h_a_le_s h_s_lt_bpow_mag_s
    -- a + u1 ≤ bpow(mag s) (via id_p_ulp_le_bpow on a in F1)
    have h_a_u1_le : a + u1 ≤ bpow beta mag_s := by
      rw [← h_ulp_a]
      exact id_p_ulp_le_bpow beta fexp1 Pa h_a_format h_a_lt_bpow_mag_s
    -- ===== Hl' chain =====
    -- u2 · (a + u1/2) ≤ bpow(-2) · u1² (and < u2 · bpow(mag_s))
    have h_amid_lt_bpow : a + (1/2) * u1 < bpow beta mag_s := by linarith
    have h_amid_u2 : (a + (1/2) * u1) * u2 < bpow beta mag_s * u2 :=
      (mul_lt_mul_iff_of_pos_right h_u2_pos).mpr h_amid_lt_bpow
    have h_bpow_u2_eq : bpow beta mag_s * u2 = bpow beta (fexp2 mag_s + mag_s) := by
      show bpow beta mag_s * bpow beta (fexp2 mag_s) = bpow beta (fexp2 mag_s + mag_s)
      rw [← bpow_plus]; congr 1; ring
    have h_bpow_le : bpow beta (fexp2 mag_s + mag_s) ≤ bpow beta (2 * fexp1 mag_s - 2) :=
      bpow_le beta h_hexp22
    have h_u1_sq_eq : u1 * u1 = bpow beta (2 * fexp1 mag_s) := by
      show bpow beta (fexp1 mag_s) * bpow beta (fexp1 mag_s) = bpow beta (2 * fexp1 mag_s)
      rw [← bpow_plus]; congr 1; ring
    have h_bpow_split : bpow beta (2 * fexp1 mag_s - 2) = bpow beta (-2) * (u1 * u1) := by
      rw [h_u1_sq_eq]
      show bpow beta (2 * fexp1 mag_s - 2) = bpow beta (-2) * bpow beta (2 * fexp1 mag_s)
      rw [← bpow_plus]; congr 1; ring
    have h_u1_sq_nonneg : 0 ≤ u1 * u1 := mul_nonneg (le_of_lt h_u1_pos) (le_of_lt h_u1_pos)
    have h_bpow_neg_2_le : bpow beta (-2) ≤ 1 / 4 := bpow_neg_two_le_quarter beta
    have h_bpow_u1_sq_le : bpow beta (-2) * (u1 * u1) ≤ (1/4) * (u1 * u1) :=
      mul_le_mul_of_nonneg_right h_bpow_neg_2_le h_u1_sq_nonneg
    -- Combine: u2·(a + u1/2) < (1/4) · u1²
    have h_amid_u2_lt_quarter : (a + (1/2) * u1) * u2 < (1/4) * (u1 * u1) := by
      calc (a + (1/2) * u1) * u2
          < bpow beta mag_s * u2 := h_amid_u2
        _ = bpow beta (fexp2 mag_s + mag_s) := h_bpow_u2_eq
        _ ≤ bpow beta (2 * fexp1 mag_s - 2) := h_bpow_le
        _ = bpow beta (-2) * (u1 * u1) := h_bpow_split
        _ ≤ (1/4) * (u1 * u1) := h_bpow_u1_sq_le
    -- Hl' : 0 < -(u2·a) + b²
    have Hl' : 0 < -(u2 * a) + b * b := by
      have h_expand : (a + (1/2) * u1) * u2 = u2 * a + u1 * u2 / 2 := by ring
      have h_combined : u2 * a + u1 * u2 / 2 < (1/4) * (u1 * u1) := by
        rw [← h_expand]; exact h_amid_u2_lt_quarter
      have h_u2_sq_nonneg : 0 ≤ u2 * u2 :=
        mul_nonneg (le_of_lt h_u2_pos) (le_of_lt h_u2_pos)
      have h_b_sq_eq : b * b = (u1 * u1 - 2 * u1 * u2 + u2 * u2) / 4 := by
        show (u1 - u2)/2 * ((u1 - u2)/2) = (u1 * u1 - 2 * u1 * u2 + u2 * u2) / 4
        ring
      linarith [h_combined, h_u2_sq_nonneg, h_b_sq_eq]
    -- ===== Hr' chain =====
    -- Show u2·a + b'² < u1² (the algebraic step for Hr')
    have h_u2_sq_lt : u2 * u2 < u1 * u1 :=
      mul_lt_mul' (le_of_lt h_u2_lt_u1) h_u2_lt_u1 (le_of_lt h_u2_pos) h_u1_pos
    have h_bpow_neg_2_le_half : bpow beta (-2) ≤ 1 / 2 := by
      have h1 : (1 : ℝ) / 4 ≤ 1 / 2 := by norm_num
      linarith [h_bpow_neg_2_le, h1]
    have h_bpow_u1_sq_le_half : bpow beta (-2) * (u1 * u1) ≤ (1/2) * (u1 * u1) :=
      mul_le_mul_of_nonneg_right h_bpow_neg_2_le_half h_u1_sq_nonneg
    have h_amid_u2_lt_half : (a + (1/2) * u1) * u2 ≤ (1/2) * (u1 * u1) := by
      calc (a + (1/2) * u1) * u2
          ≤ bpow beta mag_s * u2 := le_of_lt h_amid_u2
        _ = bpow beta (fexp2 mag_s + mag_s) := h_bpow_u2_eq
        _ ≤ bpow beta (2 * fexp1 mag_s - 2) := h_bpow_le
        _ = bpow beta (-2) * (u1 * u1) := h_bpow_split
        _ ≤ (1/2) * (u1 * u1) := h_bpow_u1_sq_le_half
    have Hr_step : u2 * a + b' * b' < u1 * u1 := by
      have h_expand : (a + (1/2) * u1) * u2 = u2 * a + u1 * u2 / 2 := by ring
      have h_combined : u2 * a + u1 * u2 / 2 ≤ (1/2) * (u1 * u1) := by
        rw [← h_expand]; exact h_amid_u2_lt_half
      have h_b'_sq_eq : b' * b' = (u1 * u1 + 2 * u1 * u2 + u2 * u2) / 4 := by
        show (u1 + u2)/2 * ((u1 + u2)/2) = (u1 * u1 + 2 * u1 * u2 + u2 * u2) / 4
        ring
      linarith [h_combined, h_u2_sq_lt, h_b'_sq_eq]
    -- Now derive Hr' via integer-multiple argument
    -- x and a²+u1·a are both integer multiples of B := bpow(2·fexp1 mag_s) = u1²
    -- Express x = (mx · β^k) · u1² and a²+u1·a = (ma²+ma) · u1²
    set fexp_x := fexp1 (mag beta x) with hfx_def
    have h_k_nonneg : 0 ≤ fexp_x - 2 * fexp1 mag_s := by linarith [Hf1]
    set k_nat := (fexp_x - 2 * fexp1 mag_s).toNat with hkn_def
    have h_k_eq : (k_nat : ℤ) = fexp_x - 2 * fexp1 mag_s :=
      Int.toNat_of_nonneg h_k_nonneg
    -- bpow(fexp_x) = bpow(2·fexp1 mag_s) · β^k_nat
    have h_bpow_fexpx_split : bpow beta fexp_x =
        bpow beta (2 * fexp1 mag_s) * ((beta.val : ℝ) ^ k_nat) := by
      have h1 : fexp_x = 2 * fexp1 mag_s + (k_nat : ℤ) := by linarith [h_k_eq]
      rw [h1, bpow_plus]
      have h2 : bpow beta ((k_nat : ℤ)) = (beta.val : ℝ) ^ k_nat := by
        unfold bpow; exact zpow_natCast _ _
      rw [h2]
    -- x = mx · bpow(fexp_x) from Fx
    set mx := Ztrunc (x * bpow beta (-fexp_x)) with hmx_def
    have hFx' : x = (mx : ℝ) * bpow beta fexp_x := Fx
    -- a = ma · u1 from Fa (using h_mag_a)
    set ma := Ztrunc (a * bpow beta (-fexp1 mag_s)) with hma_def
    have h_ma_eq : a = (ma : ℝ) * u1 := by
      have hFa : a = (Ztrunc (a * bpow beta (-cexp beta fexp1 a)) : ℝ)
          * bpow beta (cexp beta fexp1 a) := h_a_format
      unfold cexp at hFa
      rw [h_mag_a] at hFa
      exact hFa
    -- B := u1*u1
    set B := u1 * u1 with hB_def
    have h_B_pos : 0 < B := mul_pos h_u1_pos h_u1_pos
    have h_B_eq : B = bpow beta (2 * fexp1 mag_s) := h_u1_sq_eq
    -- x = (mx · β^k_nat) · B
    set kx := mx * ((beta.val : ℤ) ^ k_nat) with hkx_def
    have h_x_kxB : x = (kx : ℝ) * B := by
      rw [hFx', h_bpow_fexpx_split, h_B_eq]
      show (mx : ℝ) * (bpow beta (2 * fexp1 mag_s) * ((beta.val : ℝ) ^ k_nat))
        = ((mx * ((beta.val : ℤ) ^ k_nat) : ℤ) : ℝ) * bpow beta (2 * fexp1 mag_s)
      push_cast
      ring
    -- a²+u1·a = (ma²+ma) · B
    set ka := ma * ma + ma with hka_def
    have h_aapua_eq : a * a + u1 * a = (ka : ℝ) * B := by
      rw [h_ma_eq, hB_def]
      show ((ma : ℝ) * u1) * ((ma : ℝ) * u1) + u1 * ((ma : ℝ) * u1) = ((ma * ma + ma : ℤ) : ℝ) * (u1 * u1)
      push_cast
      ring
    -- From Hsr + Hr_step: x < a²+u1·a + u1² = (ka+1) · B
    have h_x_strict : x < a * a + u1 * a + B := by
      have := Hsr
      linarith [Hr_step]
    have h_x_strict' : (kx : ℝ) * B < ((ka : ℝ) + 1) * B := by
      have h_eq1 : x = (kx : ℝ) * B := h_x_kxB
      have h_eq2 : a * a + u1 * a = (ka : ℝ) * B := h_aapua_eq
      have h_add : ((ka : ℝ) + 1) * B = (ka : ℝ) * B + B := by ring
      linarith [h_x_strict, h_eq1, h_eq2, h_add]
    have h_kx_lt : (kx : ℝ) < (ka : ℝ) + 1 :=
      (mul_lt_mul_iff_of_pos_right h_B_pos).mp h_x_strict'
    have h_kx_lt_int : kx < ka + 1 := by exact_mod_cast h_kx_lt
    have h_kx_le_int : kx ≤ ka := Int.lt_add_one_iff.mp h_kx_lt_int
    have h_kx_le : (kx : ℝ) ≤ (ka : ℝ) := by exact_mod_cast h_kx_le_int
    have Hr' : x ≤ a * a + u1 * a := by
      rw [h_x_kxB, h_aapua_eq]
      exact (mul_le_mul_iff_of_pos_right h_B_pos).mpr h_kx_le
    -- Combine: a²+u1·a < x (from Hsl + Hl') and x ≤ a²+u1·a (Hr'). Contradiction.
    have h_chain : a * a + u1 * a < x := by linarith [Hsl, Hl']
    linarith [h_chain, Hr']

/-- **The sqrt double-rounding theorem.**

Given the `round_round_sqrt_hyp` precision condition and `x ∈ F1`,
double-rounding `Real.sqrt x` is innocuous. -/
theorem round_round_sqrt (beta : radix) {fexp1 fexp2 : ℤ → ℤ}
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    {x : ℝ} (Fx : generic_format beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  rcases le_or_gt x 0 with Npx | Px
  · -- x ≤ 0: √x = 0
    have h_sqrt_zero : Real.sqrt x = 0 := by
      rw [Real.sqrt_eq_zero']; exact Npx
    rw [h_sqrt_zero]
    unfold round_round_eq
    rw [round_0, round_0]
  · -- 0 < x
    have h_s_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr Px
    have h_x_ne : x ≠ 0 := ne_of_gt Px
    -- Hfx : fexp1(mag x) < mag x
    have Hfx : fexp1 (mag beta x) < mag beta x :=
      mag_generic_gt beta fexp1 Vfexp1 h_x_ne Fx
    -- Hfsx : fexp1(mag √x) < mag √x
    have Hfsx : fexp1 (mag beta (Real.sqrt x)) < mag beta (Real.sqrt x) := by
      rcases le_or_gt x 1 with hx1 | hx1
      · -- x ≤ 1: √x ≥ x, so mag √x ≥ mag x
        have h_x_le_sqrt : x ≤ Real.sqrt x := by
          have h_eq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (le_of_lt Px)
          have h1 : Real.sqrt x ≤ 1 := by
            rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
            exact Real.sqrt_le_sqrt hx1
          nlinarith [Real.sqrt_nonneg x, h_eq, h1]
        have h_mag : mag beta x ≤ mag beta (Real.sqrt x) := by
          apply mag_le_abs beta h_x_ne
          rw [abs_of_pos Px, abs_of_pos h_s_pos]
          exact h_x_le_sqrt
        exact valid_exp_large Vfexp1 Hfx h_mag
      · -- 1 < x: √x ≥ 1, so mag √x ≥ 1. Derive fexp1 1 < 1 from Hexp.2.1 at ex=1.
        obtain ⟨_, Hex21, _⟩ := Hexp
        have h_fexp1_at_1 : 2 * fexp1 1 ≤ fexp1 (2 * 1 - 1) := Hex21 1
        have h_fexp1_1_lt : fexp1 1 < 1 := by
          have : fexp1 (2 * 1 - 1) = fexp1 1 := by norm_num
          linarith [h_fexp1_at_1, this]
        have h_sqrt_ge_1 : 1 ≤ Real.sqrt x := by
          rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
          exact Real.sqrt_le_sqrt (le_of_lt hx1)
        have h_mag_ge_1 : 1 ≤ mag beta (Real.sqrt x) := by
          apply mag_ge_bpow beta
          show bpow beta (1 - 1) ≤ |Real.sqrt x|
          rw [show (1 : ℤ) - 1 = 0 from by norm_num, bpow_zero,
              abs_of_nonneg (Real.sqrt_nonneg x)]
          exact h_sqrt_ge_1
        exact valid_exp_large Vfexp1 h_fexp1_1_lt h_mag_ge_1
    -- Hf2 : fexp2(mag √x) ≤ fexp1(mag √x) - 1
    have Hf2 : fexp2 (mag beta (Real.sqrt x)) ≤ fexp1 (mag beta (Real.sqrt x)) - 1 := by
      obtain ⟨_, _, Hex22⟩ := Hexp
      have Hlx : fexp1 (2 * mag beta (Real.sqrt x)) < 2 * mag beta (Real.sqrt x) := by
        rcases mag_sqrt_disj beta Px with h | h
        · have h_mx_le : mag beta x ≤ 2 * mag beta (Real.sqrt x) := by linarith
          exact valid_exp_large Vfexp1 Hfx h_mx_le
        · rw [← h]; exact Hfx
      have h := Hex22 (mag beta (Real.sqrt x)) Hlx
      linarith [h, Hfsx]
    -- Dispatch via round_round_mid_cases. The Cmid callback uses _aux for contradiction.
    apply round_round_mid_cases beta Vfexp1 Vfexp2 choice1 choice2 h_s_pos Hf2 (le_of_lt Hfsx)
    intro Hmid
    exfalso
    have h_aux := round_round_sqrt_aux beta fexp1 fexp2 Vfexp1 Vfexp2 Hexp Px Hf2 Fx
    linarith [h_aux, Hmid]

/-- **`round_round_sqrt` for FLX format.** -/
theorem round_round_sqrt_FLX (beta : radix) (prec prec' : ℤ)
    (hprec : 0 < prec) (hprec' : 0 < prec')
    (choice1 choice2 : ℤ → Bool)
    (Hprec : 2 * prec + 2 ≤ prec')
    {x : ℝ} (Fx : FLX_format beta prec x) :
    round_round_eq beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (Real.sqrt x) := by
  apply round_round_sqrt beta (FLX_exp_valid prec hprec) (FLX_exp_valid prec' hprec')
    choice1 choice2
  · -- round_round_sqrt_hyp via FLX
    unfold round_round_sqrt_hyp FLX_exp
    refine ⟨?_, ?_, ?_⟩
    · intro ex; omega
    · intro ex; omega
    · intro ex _; omega
  · exact generic_format_FLX beta prec hprec Fx

/-- **`round_round_sqrt` for FLT format.**
Requires `emin ≤ 0`, `2*prec + 2 ≤ prec'`, and either
`emin' ≤ emin - prec - 2` or `2*emin' ≤ emin - 4*prec - 2`. -/
theorem round_round_sqrt_FLT (beta : radix) (emin prec emin' prec' : ℤ)
    (hprec : 0 < prec) (hprec' : 0 < prec')
    (choice1 choice2 : ℤ → Bool)
    (Hemin : emin ≤ 0)
    (Hemin' : emin' ≤ emin - prec - 2 ∨ 2 * emin' ≤ emin - 4 * prec - 2)
    (Hprec : 2 * prec + 2 ≤ prec')
    {x : ℝ} (Fx : FLT_format beta emin prec x) :
    round_round_eq beta (FLT_exp emin prec) (FLT_exp emin' prec')
      choice1 choice2 (Real.sqrt x) := by
  apply round_round_sqrt beta (FLT_exp_valid emin prec hprec)
    (FLT_exp_valid emin' prec' hprec') choice1 choice2
  · -- round_round_sqrt_hyp via FLT
    unfold round_round_sqrt_hyp FLT_exp
    refine ⟨?_, ?_, ?_⟩
    · intro ex
      rcases le_or_gt (ex - prec) emin with h1 | h1
      · rcases le_or_gt (2 * ex - prec) emin with h2 | h2
        · rw [max_eq_right h1, max_eq_right h2]; omega
        · rw [max_eq_right h1, max_eq_left (le_of_lt h2)]; omega
      · rcases le_or_gt (2 * ex - prec) emin with h2 | h2
        · rw [max_eq_left (le_of_lt h1), max_eq_right h2]; omega
        · rw [max_eq_left (le_of_lt h1), max_eq_left (le_of_lt h2)]; omega
    · intro ex
      rcases le_or_gt (ex - prec) emin with h1 | h1
      · rcases le_or_gt (2 * ex - 1 - prec) emin with h2 | h2
        · rw [max_eq_right h1, max_eq_right h2]; omega
        · rw [max_eq_right h1, max_eq_left (le_of_lt h2)]; omega
      · rcases le_or_gt (2 * ex - 1 - prec) emin with h2 | h2
        · rw [max_eq_left (le_of_lt h1), max_eq_right h2]; omega
        · rw [max_eq_left (le_of_lt h1), max_eq_left (le_of_lt h2)]; omega
    · intro ex Hlx
      -- Extract emin < 2*ex from Hlx (in both branches of the inner max).
      have h_emin_lt : emin < 2 * ex := by
        rcases le_or_gt (2 * ex - prec) emin with h | h
        · rw [max_eq_right h] at Hlx; exact Hlx
        · linarith
      -- Now 4 cases on (ex - prec) vs emin and (ex - prec') vs emin'.
      rcases le_or_gt (ex - prec) emin with h1 | h1
      · rcases le_or_gt (ex - prec') emin' with h2 | h2
        · rw [max_eq_right h2, max_eq_right h1]
          rcases Hemin' with h | h <;> omega
        · rw [max_eq_left (le_of_lt h2), max_eq_right h1]
          rcases Hemin' with h | h <;> omega
      · rcases le_or_gt (ex - prec') emin' with h2 | h2
        · rw [max_eq_right h2, max_eq_left (le_of_lt h1)]
          rcases Hemin' with h | h <;> omega
        · rw [max_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1)]
          rcases Hemin' with h | h <;> omega
  · exact generic_format_FLT beta emin prec hprec Fx

/-- **`round_round_sqrt` for FTZ format.**
Requires `2*(emin' + prec') ≤ emin + prec ≤ 1` and `2*prec + 2 ≤ prec'`. -/
theorem round_round_sqrt_FTZ (beta : radix) (emin prec emin' prec' : ℤ)
    (hprec : 0 < prec) (hprec' : 0 < prec')
    (choice1 choice2 : ℤ → Bool)
    (Hemin_lo : 2 * (emin' + prec') ≤ emin + prec)
    (Hemin_hi : emin + prec ≤ 1)
    (Hprec : 2 * prec + 2 ≤ prec')
    {x : ℝ} (Fx : FTZ_format beta emin prec x) :
    round_round_eq beta (FTZ_exp emin prec) (FTZ_exp emin' prec')
      choice1 choice2 (Real.sqrt x) := by
  apply round_round_sqrt beta (FTZ_exp_valid emin prec hprec)
    (FTZ_exp_valid emin' prec' hprec') choice1 choice2
  · -- round_round_sqrt_hyp via FTZ
    unfold round_round_sqrt_hyp FTZ_exp
    refine ⟨?_, ?_, ?_⟩
    · intro ex
      rcases lt_or_ge (ex - prec) emin with h1 | h1
      · rcases lt_or_ge (2 * ex - prec) emin with h2 | h2
        · rw [if_pos h1, if_pos h2]; omega
        · rw [if_pos h1, if_neg (not_lt.mpr h2)]; omega
      · rcases lt_or_ge (2 * ex - prec) emin with h2 | h2
        · rw [if_neg (not_lt.mpr h1), if_pos h2]; omega
        · rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2)]; omega
    · intro ex
      rcases lt_or_ge (ex - prec) emin with h1 | h1
      · rcases lt_or_ge (2 * ex - 1 - prec) emin with h2 | h2
        · rw [if_pos h1, if_pos h2]; omega
        · rw [if_pos h1, if_neg (not_lt.mpr h2)]; omega
      · rcases lt_or_ge (2 * ex - 1 - prec) emin with h2 | h2
        · rw [if_neg (not_lt.mpr h1), if_pos h2]; omega
        · rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2)]; omega
    · intro ex Hlx
      rcases lt_or_ge (2 * ex - prec) emin with h1 | h1
      · -- 2*ex - prec < emin: inner max is emin+prec-1, Hlx says emin+prec-1 < 2*ex
        rw [if_pos h1] at Hlx
        -- Conclude: FTZ_exp emin' prec' ex + ex ≤ 2 * FTZ_exp emin prec ex - 2
        rcases lt_or_ge (ex - prec) emin with h2 | h2
        · rcases lt_or_ge (ex - prec') emin' with h3 | h3
          · rw [if_pos h3, if_pos h2]; omega
          · rw [if_neg (not_lt.mpr h3), if_pos h2]; omega
        · rcases lt_or_ge (ex - prec') emin' with h3 | h3
          · rw [if_pos h3, if_neg (not_lt.mpr h2)]; omega
          · rw [if_neg (not_lt.mpr h3), if_neg (not_lt.mpr h2)]; omega
      · rw [if_neg (not_lt.mpr h1)] at Hlx
        rcases lt_or_ge (ex - prec) emin with h2 | h2
        · rcases lt_or_ge (ex - prec') emin' with h3 | h3
          · rw [if_pos h3, if_pos h2]; omega
          · rw [if_neg (not_lt.mpr h3), if_pos h2]; omega
        · rcases lt_or_ge (ex - prec') emin' with h3 | h3
          · rw [if_pos h3, if_neg (not_lt.mpr h2)]; omega
          · rw [if_neg (not_lt.mpr h3), if_neg (not_lt.mpr h2)]; omega
  · exact generic_format_FTZ beta emin prec hprec Fx

/-! ## plus/minus arc -/

/-- Hypothesis for `round_round_plus`/`round_round_minus`: four bounds
relating `fexp2` to `fexp1` at related arguments. Compare Coq's
`round_round_plus_hyp`. -/
def round_round_plus_hyp (fexp1 fexp2 : ℤ → ℤ) : Prop :=
  (∀ ex ey : ℤ, fexp1 (ex + 1) - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)
  ∧ (∀ ex ey : ℤ, fexp1 (ex - 1) + 1 ≤ ey → fexp2 ex ≤ fexp1 ey)
  ∧ (∀ ex ey : ℤ, fexp1 ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)
  ∧ (∀ ex ey : ℤ, ex - 1 ≤ ey → fexp2 ex ≤ fexp1 ey)

/-- Core building block: given exponent bounds, `x + y` is in `fexp2`-format.
When both `x` and `y` are nonzero, builds the explicit float
`⟨mx + my * β^(fexp1 (mag y) - fexp1 (mag x)), fexp1 (mag x)⟩`. -/
theorem round_round_plus_aux0_aux_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (x y : ℝ)
    (Oxy : fexp1 (mag beta x) ≤ fexp1 (mag beta y))
    (Hlnx : fexp2 (mag beta (x + y)) ≤ fexp1 (mag beta x))
    (Hlny : fexp2 (mag beta (x + y)) ≤ fexp1 (mag beta y))
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x + y) := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [zero_add] at Hlny ⊢
    exact generic_inclusion_mag beta fexp1 fexp2 (fun _ => Hlny) Fy
  · by_cases hy0 : y = 0
    · subst hy0
      rw [add_zero] at Hlnx ⊢
      exact generic_inclusion_mag beta fexp1 fexp2 (fun _ => Hlnx) Fx
    · -- Both nonzero. Build the explicit float.
      set mx := Ztrunc (scaled_mantissa beta fexp1 x) with hmx
      set my := Ztrunc (scaled_mantissa beta fexp1 y) with hmy
      have hFx : x = (mx : ℝ) * bpow beta (fexp1 (mag beta x)) := Fx
      have hFy : y = (my : ℝ) * bpow beta (fexp1 (mag beta y)) := Fy
      set d : ℤ := fexp1 (mag beta y) - fexp1 (mag beta x) with hd_def
      have hd_nn : 0 ≤ d := sub_nonneg.mpr Oxy
      have hdtn : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd_nn
      set f : float beta :=
        ⟨mx + my * (beta.val : ℤ) ^ d.toNat, fexp1 (mag beta x)⟩ with hf_def
      have h_F2R : F2R f = x + y := by
        show ((mx + my * (beta.val : ℤ) ^ d.toNat : ℤ) : ℝ)
              * bpow beta (fexp1 (mag beta x)) = x + y
        have h_pow_real : ((beta.val : ℝ)) ^ d.toNat = bpow beta d := by
          unfold bpow
          conv_rhs => rw [show d = ((d.toNat : ℕ) : ℤ) from hdtn.symm]
          rw [zpow_natCast]
        have hbpow_combine :
            bpow beta d * bpow beta (fexp1 (mag beta x)) =
              bpow beta (fexp1 (mag beta y)) := by
          rw [← bpow_plus]; congr 1; omega
        push_cast
        rw [h_pow_real, add_mul, mul_assoc, hbpow_combine, ← hFx, ← hFy]
      refine generic_format_F2R' beta fexp2 f h_F2R ?_
      intro _
      show fexp2 (mag beta (x + y)) ≤ fexp1 (mag beta x)
      exact Hlnx

/-- Workhorse for `round_round_plus_aux1`: when `y` is small enough that
`mag y ≤ fexp (mag x) - k` and `mag (x + y) = mag x`, the floor-rounded
`x + y` equals `x` exactly, so the difference is `y`, which lies in
`(0, bpow (fexp (mag x) - k))`. -/
theorem round_round_plus_aux1_aux (beta : radix) {k : ℤ} (Hk : 0 < k)
    (fexp : ℤ → ℤ) {x y : ℝ}
    (Px : 0 < x) (Py : 0 < y)
    (Hln : mag beta y ≤ fexp (mag beta x) - k)
    (Hlxy : mag beta (x + y) = mag beta x)
    (Fx : generic_format beta fexp x) :
    0 < (x + y) - round beta fexp (fun y : ℝ => ⌊y⌋) (x + y)
    ∧ (x + y) - round beta fexp (fun y : ℝ => ⌊y⌋) (x + y)
        < bpow beta (fexp (mag beta x) - k) := by
  set mx : ℤ := Ztrunc (scaled_mantissa beta fexp x) with hmx_def
  set ce : ℤ := fexp (mag beta x) with hce_def
  have hFx : x = (mx : ℝ) * bpow beta ce := Fx
  have hcxy : cexp beta fexp (x + y) = ce := by
    unfold cexp; rw [Hlxy]
  -- x * bpow(-ce) = mx
  have hx_unscale : x * bpow beta (-ce) = (mx : ℝ) := by
    conv_lhs => rw [hFx]
    rw [mul_assoc, ← bpow_plus, show ce + (-ce) = 0 from by ring,
        bpow_zero, mul_one]
  -- sm(x+y) = mx + y * bpow(-ce)
  have h_sm : scaled_mantissa beta fexp (x + y)
      = (mx : ℝ) + y * bpow beta (-ce) := by
    unfold scaled_mantissa; rw [hcxy, add_mul, hx_unscale]
  -- y * bpow(-ce) > 0
  have hbpow_pos : 0 < bpow beta (-ce) := bpow_gt_0 _ _
  have hy_scaled_pos : 0 < y * bpow beta (-ce) := mul_pos Py hbpow_pos
  -- y < bpow(ce - k)
  have hy_lt_pow : y < bpow beta (ce - k) := by
    have hy_high : |y| < bpow beta (mag beta y) := bpow_mag_gt _ _
    rw [abs_of_pos Py] at hy_high
    exact lt_of_lt_of_le hy_high (bpow_le beta Hln)
  -- y * bpow(-ce) < bpow(-k)
  have hy_scaled_lt_pow : y * bpow beta (-ce) < bpow beta (-k) := by
    have h_target : bpow beta (-k) = bpow beta (ce - k) * bpow beta (-ce) := by
      rw [← bpow_plus]; congr 1; ring
    rw [h_target]; exact mul_lt_mul_of_pos_right hy_lt_pow hbpow_pos
  -- bpow(-k) < 1
  have hbpow_neg_k_lt_1 : bpow beta (-k) < 1 := by
    have h := bpow_lt beta (show -k < 0 from by omega)
    rwa [bpow_zero] at h
  have hy_scaled_lt_1 : y * bpow beta (-ce) < 1 :=
    lt_trans hy_scaled_lt_pow hbpow_neg_k_lt_1
  -- ⌊mx + y * bpow(-ce)⌋ = mx
  have h_floor : ⌊(mx : ℝ) + y * bpow beta (-ce)⌋ = mx := by
    apply Int.floor_eq_iff.mpr
    refine ⟨by linarith, by linarith⟩
  -- round_DN(x+y) = x
  have h_round_eq_x : round beta fexp (fun y : ℝ => ⌊y⌋) (x + y) = x := by
    unfold round
    show ((⌊scaled_mantissa beta fexp (x + y)⌋ : ℤ) : ℝ)
          * bpow beta (cexp beta fexp (x + y)) = x
    rw [hcxy, h_sm, h_floor]; exact hFx.symm
  rw [h_round_eq_x]
  exact ⟨by linarith, by linarith⟩

/-- Symmetric wrapper: drop the `fexp1 (mag x) ≤ fexp1 (mag y)` ordering
assumption by case-split and `add_comm`. -/
theorem round_round_plus_aux0_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ) (x y : ℝ)
    (Hlnx : fexp2 (mag beta (x + y)) ≤ fexp1 (mag beta x))
    (Hlny : fexp2 (mag beta (x + y)) ≤ fexp1 (mag beta y))
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x + y) := by
  rcases le_or_gt (fexp1 (mag beta x)) (fexp1 (mag beta y)) with Hle | Hgt
  · exact round_round_plus_aux0_aux_aux beta fexp1 fexp2 x y Hle Hlnx Hlny Fx Fy
  · rw [add_comm] at Hlnx Hlny ⊢
    exact round_round_plus_aux0_aux_aux beta fexp1 fexp2 y x (le_of_lt Hgt)
      Hlny Hlnx Fy Fx

/-! ## mag helpers for the plus/minus arc

Four small lemmas that the plus/minus arc of `Prop/Double_rounding.v` uses
repeatedly. They sit on the shelf labeled *warm-up snack*.
-/

/-- `mag (x + y) ∈ {mag x, mag x + 1}` when `0 < y ≤ x`. -/
theorem mag_plus_disj (beta : radix) {x y : ℝ}
    (Py : 0 < y) (Hxy : y ≤ x) :
    mag beta (x + y) = mag beta x ∨ mag beta (x + y) = mag beta x + 1 := by
  obtain ⟨h1, h2⟩ := mag_plus beta Py Hxy
  omega

/-- Generic-format `x` plus a non-negative `y` with `mag y ≤ fexp (mag x)`
keeps the same `mag`. -/
theorem mag_plus_separated (beta : radix) (fexp : ℤ → ℤ)
    {x y : ℝ} (Px : 0 < x) (Nny : 0 ≤ y)
    (Fx : generic_format beta fexp x)
    (Hsep : mag beta y ≤ fexp (mag beta x)) :
    mag beta (x + y) = mag beta x := by
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]
  · have hy_pos : 0 < y := lt_of_le_of_ne Nny (Ne.symm hy0)
    have h_ulp_eq : ulp beta fexp x = bpow beta (fexp (mag beta x)) := by
      rw [ulp_neq_0 beta fexp (ne_of_gt Px)]; rfl
    have h_y_lt_ulp : y < ulp beta fexp x := by
      rw [h_ulp_eq]
      have h_y_high : |y| < bpow beta (mag beta y) := bpow_mag_gt beta y
      rw [abs_of_pos hy_pos] at h_y_high
      have h_pow_le : bpow beta (mag beta y) ≤ bpow beta (fexp (mag beta x)) :=
        bpow_le beta Hsep
      linarith
    exact mag_plus_eps beta fexp Px Fx Nny h_y_lt_ulp

/-- `mag (x - y) ∈ {mag x, mag x - 1}` when `mag y ≤ mag x - 2`. -/
theorem mag_minus_disj (beta : radix) {x y : ℝ}
    (Px : 0 < x) (Py : 0 < y) (Hln : mag beta y ≤ mag beta x - 2) :
    mag beta (x - y) = mag beta x ∨ mag beta (x - y) = mag beta x - 1 := by
  have Hxy : y < x := lt_mag beta Px (by omega)
  have h_le : mag beta (x - y) ≤ mag beta x := mag_minus beta Py Hxy
  have h_lb : mag beta x - 1 ≤ mag beta (x - y) := mag_minus_lb beta Px Py Hln
  omega

/-- Separation: when `x` is strictly above its lower mag boundary and `y`
is small (`mag y ≤ fexp (mag x)`), subtracting `y` doesn't decrease the mag. -/
theorem mag_minus_separated (beta : radix) (fexp : ℤ → ℤ)
    (Vfexp : Valid_exp fexp)
    {x y : ℝ} (Px : 0 < x) (Py : 0 < y) (Yltx : y < x)
    (Xgtpow : bpow beta (mag beta x - 1) < x)
    (Fx : generic_format beta fexp x)
    (Ly : mag beta y ≤ fexp (mag beta x)) :
    mag beta (x - y) = mag beta x := by
  have h_xy_pos : 0 < x - y := by linarith
  apply mag_unique beta
  · rw [abs_of_pos h_xy_pos]
    -- β^(mag x - 1) ≤ x - y, via succ_le_lt at β^(mag x - 1)
    have h_pow_pos : 0 < bpow beta (mag beta x - 1) := bpow_gt_0 _ _
    have h_fexp_lt : fexp (mag beta x) < mag beta x :=
      mag_generic_gt beta fexp Vfexp (ne_of_gt Px) Fx
    have h_idx_eq : mag beta x - 1 + 1 = mag beta x := by ring
    have h_pow_format : generic_format beta fexp (bpow beta (mag beta x - 1)) := by
      apply generic_format_bpow
      rw [h_idx_eq]; omega
    have h_succ_eq : succ beta fexp (bpow beta (mag beta x - 1)) =
        bpow beta (mag beta x - 1) + ulp beta fexp (bpow beta (mag beta x - 1)) :=
      succ_eq_pos beta fexp (le_of_lt h_pow_pos)
    have h_ulp_bpow : ulp beta fexp (bpow beta (mag beta x - 1)) =
        bpow beta (fexp (mag beta x)) := by
      rw [ulp_bpow, h_idx_eq]
    have h_succ_le : succ beta fexp (bpow beta (mag beta x - 1)) ≤ x :=
      succ_le_lt beta fexp Vfexp h_pow_format Fx Xgtpow
    have h_y_lt : y < bpow beta (fexp (mag beta x)) := by
      have h_y_high : |y| < bpow beta (mag beta y) := bpow_mag_gt beta y
      rw [abs_of_pos Py] at h_y_high
      have h_pow_le : bpow beta (mag beta y) ≤ bpow beta (fexp (mag beta x)) :=
        bpow_le beta Ly
      linarith
    linarith [h_succ_eq, h_ulp_bpow, h_succ_le]
  · rw [abs_of_pos h_xy_pos]
    have h_x_high : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
    rw [abs_of_pos Px] at h_x_high
    linarith

/-- `bpow β (-1) ≤ 1/2`. Sibling of `bpow_neg_two_le_quarter`. -/
private theorem bpow_neg_one_le_half (beta : radix) :
    bpow beta (-1) ≤ (1 : ℝ) / 2 := by
  have h2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  have h_b_pos : 0 < (beta.val : ℝ) := by linarith
  have h_inv : bpow beta (-1) = 1 / (beta.val : ℝ) := by
    show (beta.val : ℝ) ^ (-1 : ℤ) = 1 / (beta.val : ℝ)
    rw [zpow_neg, zpow_one]; field_simp
  rw [h_inv]
  exact one_div_le_one_div_of_le (by norm_num) h2

/-- `round_round_plus_aux1`: when `mag y ≤ fexp1 (mag x) - 2`, double
rounding is innocuous via `round_round_lt_mid` applied at `x + y`. The
key bounds are `bpow(-2) ≤ 1/4` (for the same-place leg) and the
strict subset leg `bpow(-1) ≤ 1/2`. -/
theorem round_round_plus_aux1 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Px : 0 < x) (Py : 0 < y)
    (Hly : mag beta y ≤ fexp1 (mag beta x) - 2)
    (Fx : generic_format beta fexp1 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  -- Setup: mag(x+y) = mag x
  have Lxy : mag beta (x + y) = mag beta x := by
    apply mag_plus_separated beta fexp1 Px (le_of_lt Py) Fx
    omega
  obtain ⟨_, _, _, Hexp4⟩ := Hexp
  have Hf2 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) := Hexp4 _ _ (by omega)
  have Bpow2 : bpow beta (-2) ≤ (1 : ℝ) / 4 := bpow_neg_two_le_quarter beta
  have Bpow1 : bpow beta (-1) ≤ (1 : ℝ) / 2 := bpow_neg_one_le_half beta
  have hxy_pos : 0 < x + y := by linarith
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy_pos
  have hfexp1_lt : fexp1 (mag beta x) < mag beta x :=
    mag_generic_gt beta fexp1 Vfexp1 (ne_of_gt Px) Fx
  -- aux1_aux with k = 2
  obtain ⟨_, h_diff_lt⟩ := round_round_plus_aux1_aux beta (k := 2)
    (by norm_num : (0 : ℤ) < 2) fexp1 Px Py Hly Lxy Fx
  -- Apply round_round_lt_mid
  apply round_round_lt_mid beta Vfexp1 Vfexp2 choice1 choice2 hxy_pos
  · -- Hf2f1: fexp2(mag(x+y)) ≤ fexp1(mag(x+y))
    rw [Lxy]; exact Hf2
  · -- Hf1: fexp1(mag(x+y)) ≤ mag(x+y)
    rw [Lxy]; omega
  · -- Hx: x + y < midp β fexp1 (x + y)
    unfold midp
    have h_ulp_eq : ulp beta fexp1 (x + y) = bpow beta (fexp1 (mag beta x)) := by
      rw [ulp_neq_0 _ _ hxy_ne]
      show bpow beta (fexp1 (mag beta (x + y))) = _
      rw [Lxy]
    rw [h_ulp_eq]
    -- Goal: x + y < round_DN(x+y) + (1/2) * bpow(fexp1(mag x))
    -- We have: (x + y) - round_DN(x+y) < bpow(fexp1(mag x) - 2)
    -- And: bpow(fexp1(mag x) - 2) ≤ (1/2) * bpow(fexp1(mag x))
    have h_pow_bound : bpow beta (fexp1 (mag beta x) - 2)
        ≤ (1 : ℝ) / 2 * bpow beta (fexp1 (mag beta x)) := by
      have h_split : bpow beta (fexp1 (mag beta x) - 2)
          = bpow beta (-2) * bpow beta (fexp1 (mag beta x)) := by
        rw [← bpow_plus]; congr 1; ring
      rw [h_split]
      have h_pos : 0 < bpow beta (fexp1 (mag beta x)) := bpow_gt_0 _ _
      nlinarith
    linarith
  · -- Hx': fexp2(mag(x+y)) ≤ fexp1(mag(x+y)) - 1 → x + y < midp - (1/2) * ulp2
    intro Hf2'
    unfold midp
    have h_ulp1_eq : ulp beta fexp1 (x + y) = bpow beta (fexp1 (mag beta x)) := by
      rw [ulp_neq_0 _ _ hxy_ne]
      show bpow beta (fexp1 (mag beta (x + y))) = _
      rw [Lxy]
    have h_ulp2_eq : ulp beta fexp2 (x + y) = bpow beta (fexp2 (mag beta x)) := by
      rw [ulp_neq_0 _ _ hxy_ne]
      show bpow beta (fexp2 (mag beta (x + y))) = _
      rw [Lxy]
    rw [h_ulp1_eq, h_ulp2_eq] at *
    -- Goal: x + y < round_DN + (1/2) * bpow(fexp1(mag x)) - (1/2) * bpow(fexp2(mag x))
    -- We need: (x + y) - round_DN < (1/2) * (bpow(fexp1(mag x)) - bpow(fexp2(mag x)))
    -- We have: (x + y) - round_DN < bpow(fexp1(mag x) - 2)
    -- Suffices: bpow(fexp1(mag x) - 2) ≤ (1/2) * (bpow(fexp1(mag x)) - bpow(fexp2(mag x)))
    have h_fexp2_le : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1 := by
      have := Hf2'; rw [Lxy] at this; exact this
    have h_b1_pos : 0 < bpow beta (fexp1 (mag beta x)) := bpow_gt_0 _ _
    have h_b2_le_b1m1 : bpow beta (fexp2 (mag beta x))
        ≤ bpow beta (fexp1 (mag beta x) - 1) := bpow_le beta h_fexp2_le
    have h_b1m1_split : bpow beta (fexp1 (mag beta x) - 1)
        = bpow beta (-1) * bpow beta (fexp1 (mag beta x)) := by
      rw [← bpow_plus]; congr 1; ring
    have h_b2_le_half : bpow beta (fexp2 (mag beta x))
        ≤ (1 : ℝ) / 2 * bpow beta (fexp1 (mag beta x)) := by
      rw [h_b1m1_split] at h_b2_le_b1m1
      nlinarith
    have h_pow_bound : bpow beta (fexp1 (mag beta x) - 2)
        ≤ (1 : ℝ) / 2 * (bpow beta (fexp1 (mag beta x))
                          - bpow beta (fexp2 (mag beta x))) := by
      have h_split : bpow beta (fexp1 (mag beta x) - 2)
          = bpow beta (-2) * bpow beta (fexp1 (mag beta x)) := by
        rw [← bpow_plus]; congr 1; ring
      rw [h_split]
      nlinarith
    linarith

/-- `round_round_plus_aux0`: when `fexp1 (mag x) - 1 ≤ mag y`, the addition
`x + y` is in `fexp2`-format (exact in the larger precision). -/
theorem round_round_plus_aux0 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Px : 0 < x) (Py : 0 < y) (Hyx : y ≤ x)
    (Hln : fexp1 (mag beta x) - 1 ≤ mag beta y)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x + y) := by
  obtain ⟨_, Hexp2, Hexp3, Hexp4⟩ := Hexp
  rcases le_or_gt (mag beta y) (fexp1 (mag beta x)) with Hle | Hgt
  · -- mag y ≤ fexp1 (mag x): mag (x+y) = mag x via mag_plus_separated
    have Lxy : mag beta (x + y) = mag beta x :=
      mag_plus_separated beta fexp1 Px (le_of_lt Py) Fx Hle
    refine round_round_plus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
    · rw [Lxy]; exact Hexp4 _ _ (by omega)
    · rw [Lxy]; exact Hexp3 _ _ Hln
  · -- fexp1 (mag x) < mag y: mag (x+y) ∈ {mag x, mag x + 1}
    have hmy_le_mx : mag beta y ≤ mag beta x := by
      have hx_ne : x ≠ 0 := ne_of_gt Px
      have hy_ne : y ≠ 0 := ne_of_gt Py
      apply mag_le_abs beta hy_ne
      rw [abs_of_pos Py, abs_of_pos Px]; exact Hyx
    refine round_round_plus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
    · rcases mag_plus_disj beta Py Hyx with Lxy | Lxy
      · rw [Lxy]; exact Hexp4 _ _ (by omega)
      · rw [Lxy]
        have h_req : fexp1 ((mag beta x + 1) - 1) + 1 ≤ mag beta x := by
          have : fexp1 (mag beta x) + 1 ≤ mag beta x := by omega
          have heq : (mag beta x + 1) - 1 = mag beta x := by ring
          rw [heq]; omega
        exact Hexp2 _ _ h_req
    · rcases mag_plus_disj beta Py Hyx with Lxy | Lxy
      · rw [Lxy]; exact Hexp3 _ _ (by omega)
      · rw [Lxy]
        have h_req : fexp1 ((mag beta x + 1) - 1) + 1 ≤ mag beta y := by
          have heq : (mag beta x + 1) - 1 = mag beta x := by ring
          rw [heq]; omega
        exact Hexp2 _ _ h_req

/-- Combine `aux0` and `aux1` by dispatching on `mag y` vs `fexp1(mag x) - 2`. -/
theorem round_round_plus_aux2 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Px : 0 < x) (Py : 0 < y) (Hyx : y ≤ x)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  rcases le_or_gt (mag beta y) (fexp1 (mag beta x) - 2) with Hly | Hly
  · -- Small y: aux1
    exact round_round_plus_aux1 beta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2
      Hexp Px Py Hly Fx
  · -- Larger y: x + y is in fexp2-format, so the inner round is the identity
    unfold round_round_eq
    have Hxy_fmt : generic_format beta fexp2 (x + y) :=
      round_round_plus_aux0 beta fexp1 fexp2 Vfexp1 Hexp Px Py Hyx
        (by omega) Fx Fy
    rw [round_generic beta fexp2 (Znearest choice2) Hxy_fmt]

/-- Drop the `y ≤ x` assumption to `0 ≤ x` and `0 ≤ y`. -/
theorem round_round_plus_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Nnx : 0 ≤ x) (Nny : 0 ≤ y)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x + y) := by
  have Hexp4 := Hexp.2.2.2
  by_cases hx0 : x = 0
  · subst hx0
    rw [zero_add]
    unfold round_round_eq
    have Hy_fmt2 : generic_format beta fexp2 y :=
      generic_inclusion_mag beta fexp1 fexp2 (fun _ => Hexp4 _ _ (by omega)) Fy
    rw [round_generic beta fexp2 (Znearest choice2) Hy_fmt2]
  · by_cases hy0 : y = 0
    · subst hy0
      rw [add_zero]
      unfold round_round_eq
      have Hx_fmt2 : generic_format beta fexp2 x :=
        generic_inclusion_mag beta fexp1 fexp2 (fun _ => Hexp4 _ _ (by omega)) Fx
      rw [round_generic beta fexp2 (Znearest choice2) Hx_fmt2]
    · have Px : 0 < x := lt_of_le_of_ne Nnx (Ne.symm hx0)
      have Py : 0 < y := lt_of_le_of_ne Nny (Ne.symm hy0)
      rcases lt_or_ge x y with H | H
      · rw [add_comm]
        exact round_round_plus_aux2 beta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2
          Hexp Py Px (le_of_lt H) Fy Fx
      · exact round_round_plus_aux2 beta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2
          Hexp Px Py H Fx Fy

/-! ### Minus arc -/

/-- Mirror of `plus_aux0_aux`: rewrite `x - y` as `x + (-y)` and reuse. -/
theorem round_round_minus_aux0_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ) (x y : ℝ)
    (Hlnx : fexp2 (mag beta (x - y)) ≤ fexp1 (mag beta x))
    (Hlny : fexp2 (mag beta (x - y)) ≤ fexp1 (mag beta y))
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x - y) := by
  have h_eq : x - y = x + (-y) := by ring
  rw [h_eq]
  rw [h_eq] at Hlnx Hlny
  rw [← mag_opp beta y] at Hlny
  exact round_round_plus_aux0_aux beta fexp1 fexp2 x (-y) Hlnx Hlny Fx
    (generic_format_opp beta fexp1 Fy)

/-- Mirror of `plus_aux0`: when `fexp1 (mag x) - 1 ≤ mag y`, `x - y` is in
`fexp2`-format. Dispatches on whether `mag y` is close to `mag x` (using
`mag_minus` upper bound) or far (using `mag_minus_disj`). -/
theorem round_round_minus_aux0 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Py : 0 < y) (Hyx : y < x)
    (Hln : fexp1 (mag beta x) - 1 ≤ mag beta y)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x - y) := by
  have Px : 0 < x := lt_trans Py Hyx
  obtain ⟨Hexp1, _, Hexp3, Hexp4⟩ := Hexp
  have Lyx : mag beta y ≤ mag beta x := by
    apply mag_le_abs beta (ne_of_gt Py)
    rw [abs_of_pos Py, abs_of_pos Px]; exact le_of_lt Hyx
  rcases lt_or_ge (mag beta x - 2) (mag beta y) with Hlt | Hge
  · -- mag x - 2 < mag y ⟹ mag y ∈ {mag x - 1, mag x}
    -- mag (x - y) ≤ mag x (mag_minus)
    have hxy_pos : 0 < x - y := by linarith
    have h_xmy_le : mag beta (x - y) ≤ mag beta x := mag_minus beta Py Hyx
    rcases (by omega : mag beta y = mag beta x ∨ mag beta y = mag beta x - 1)
      with Heq | Heqm1
    · -- mag y = mag x
      refine round_round_minus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
      · exact Hexp4 _ _ (by omega)
      · rw [Heq]; exact Hexp4 _ _ (by omega)
    · -- mag y = mag x - 1
      refine round_round_minus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
      · exact Hexp4 _ _ (by omega)
      · rw [Heqm1]; exact Hexp4 _ _ (by omega)
  · -- mag y ≤ mag x - 2: use mag_minus_disj
    rcases mag_minus_disj beta Px Py Hge with Lxmy | Lxmy
    · -- mag (x - y) = mag x
      refine round_round_minus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
      · rw [Lxmy]; exact Hexp4 _ _ (by omega)
      · rw [Lxmy]; exact Hexp3 _ _ Hln
    · -- mag (x - y) = mag x - 1
      refine round_round_minus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
      · rw [Lxmy]
        have h_req : fexp1 ((mag beta x - 1) + 1) - 1 ≤ mag beta x := by
          have heq : (mag beta x - 1) + 1 = mag beta x := by ring
          rw [heq]; omega
        exact Hexp1 _ _ h_req
      · rw [Lxmy]
        have h_req : fexp1 ((mag beta x - 1) + 1) - 1 ≤ mag beta y := by
          have heq : (mag beta x - 1) + 1 = mag beta x := by ring
          rw [heq]; omega
        exact Hexp1 _ _ h_req

/-- `round_round_minus_aux2_aux`: workhorse for `minus_aux2`. When
`mag y ≤ fexp(mag x) - 1`, the ceiling-rounded `x - y` exceeds `x - y`
by at most `y`. Case-splits on whether `x` is strictly above
`bpow(mag x - 1)` or exactly at the boundary. -/
theorem round_round_minus_aux2_aux (beta : radix) (fexp : ℤ → ℤ)
    (Vfexp : Valid_exp fexp)
    {x y : ℝ} (Py : 0 < y) (Hxy : y < x)
    (Hly : mag beta y ≤ fexp (mag beta x) - 1)
    (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y) :
    round beta fexp (fun y : ℝ => ⌈y⌉) (x - y) - (x - y) ≤ y := by
  have Px : 0 < x := lt_trans Py Hxy
  have hxy_pos : 0 < x - y := by linarith
  have hxy_ne : x - y ≠ 0 := ne_of_gt hxy_pos
  set mx : ℤ := Ztrunc (scaled_mantissa beta fexp x) with hmx_def
  set ce : ℤ := fexp (mag beta x) with hce_def
  have hFx : x = (mx : ℝ) * bpow beta ce := Fx
  have Hfx : fexp (mag beta x) < mag beta x :=
    mag_generic_gt beta fexp Vfexp (ne_of_gt Px) Fx
  have Hfy : fexp (mag beta y) < mag beta y :=
    mag_generic_gt beta fexp Vfexp (ne_of_gt Py) Fy
  have h_bp_neg_ce_pos : 0 < bpow beta (-ce) := bpow_gt_0 _ _
  -- x * bpow(-ce) = mx
  have hx_unscale : x * bpow beta (-ce) = (mx : ℝ) := by
    conv_lhs => rw [hFx]
    rw [mul_assoc, ← bpow_plus, show ce + (-ce) = 0 from by ring,
        bpow_zero, mul_one]
  rcases lt_or_ge (bpow beta (mag beta x - 1)) x with Hx | Hx
  · -- Case 1: bpow(mag x - 1) < x
    have Lxy : mag beta (x - y) = mag beta x := by
      apply mag_minus_separated beta fexp Vfexp Px Py Hxy Hx Fx
      omega
    have h_cxy : cexp beta fexp (x - y) = ce := by unfold cexp; rw [Lxy]
    -- sm(x - y) = mx - y * bpow(-ce)
    have h_sm_xy : scaled_mantissa beta fexp (x - y)
        = (mx : ℝ) - y * bpow beta (-ce) := by
      unfold scaled_mantissa; rw [h_cxy, sub_mul, hx_unscale]
    -- y * bpow(-ce) < 1
    have h_ys_lt_1 : y * bpow beta (-ce) < 1 := by
      have hy_high : |y| < bpow beta (mag beta y) := bpow_mag_gt _ _
      rw [abs_of_pos Py] at hy_high
      have hpow_le : bpow beta (mag beta y) ≤ bpow beta (ce - 1) :=
        bpow_le beta (by omega)
      have hy_lt : y < bpow beta (ce - 1) := lt_of_lt_of_le hy_high hpow_le
      have h_combine : bpow beta (-1)
          = bpow beta (ce - 1) * bpow beta (-ce) := by
        rw [← bpow_plus]; congr 1; ring
      have hys_lt : y * bpow beta (-ce) < bpow beta (-1) := by
        rw [h_combine]
        exact mul_lt_mul_of_pos_right hy_lt h_bp_neg_ce_pos
      have hbp1 : bpow beta (-1) ≤ 1 / 2 := bpow_neg_one_le_half beta
      linarith
    have h_ys_nn : 0 ≤ y * bpow beta (-ce) :=
      le_of_lt (mul_pos Py h_bp_neg_ce_pos)
    -- ⌈mx - y * bpow(-ce)⌉ = mx
    have h_ceil : ⌈(mx : ℝ) - y * bpow beta (-ce)⌉ = mx := by
      apply Int.ceil_eq_iff.mpr
      refine ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    -- round_UP(x-y) = x
    have h_rxy : round beta fexp (fun y : ℝ => ⌈y⌉) (x - y) = x := by
      unfold round
      show ((⌈scaled_mantissa beta fexp (x - y)⌉ : ℤ) : ℝ)
            * bpow beta (cexp beta fexp (x - y)) = x
      rw [h_cxy, h_sm_xy, h_ceil]
      exact hFx.symm
    linarith
  · -- Case 2: x ≤ bpow(mag x - 1), so x = bpow(mag x - 1)
    have hx_low : bpow beta (mag beta x - 1) ≤ x := by
      have := bpow_mag_le beta (ne_of_gt Px)
      rwa [abs_of_pos Px] at this
    set mxg : ℤ := mag beta x with hmxg_def
    have Xpow : x = bpow beta (mxg - 1) := le_antisymm Hx hx_low
    have h_mag_y_le : mag beta y ≤ mxg - 2 := by omega
    have Lxy : mag beta (x - y) = mxg - 1 := by
      apply le_antisymm
      · apply mag_le_bpow beta hxy_ne
        rw [abs_of_pos hxy_pos]
        nth_rewrite 1 [Xpow]; linarith
      · exact mag_minus_lb beta Px Py h_mag_y_le
    have Hfx1 : fexp (mxg - 1) < mxg - 1 :=
      valid_exp_large Vfexp Hfy (by omega : mag beta y ≤ mxg - 1)
    have hnn : 0 ≤ mxg - 1 - fexp (mxg - 1) := by omega
    have h_cxy : cexp beta fexp (x - y) = fexp (mxg - 1) := by
      unfold cexp; rw [Lxy]
    -- x * bpow(-fexp(mxg - 1)) = bpow(mxg - 1 - fexp(mxg - 1))
    have h_x_bpow : x * bpow beta (-fexp (mxg - 1))
        = bpow beta (mxg - 1 - fexp (mxg - 1)) := by
      rw [Xpow, ← bpow_plus]; congr 1
    -- x = bpow(mxg - 1 - fexp(mxg - 1)) * bpow(fexp(mxg - 1))
    have h_x_pow_eq : x = bpow beta (mxg - 1 - fexp (mxg - 1))
                            * bpow beta (fexp (mxg - 1)) := by
      rw [show x = bpow beta (mxg - 1) from Xpow, ← bpow_plus]
      congr 1; ring
    -- round_UP(x-y) ≤ x
    have h_rxy : round beta fexp (fun y : ℝ => ⌈y⌉) (x - y) ≤ x := by
      unfold round
      show ((⌈scaled_mantissa beta fexp (x - y)⌉ : ℤ) : ℝ)
            * bpow beta (cexp beta fexp (x - y)) ≤ x
      rw [h_cxy]
      conv_rhs => rw [h_x_pow_eq]
      apply mul_le_mul_of_nonneg_right _ (bpow_ge_0 _ _)
      rw [← IZR_Zpower beta hnn]
      exact_mod_cast Int.ceil_le.mpr (by
        unfold scaled_mantissa; rw [h_cxy]
        rw [IZR_Zpower beta hnn]
        have h_xy_le_x : x - y ≤ x := by linarith
        calc (x - y) * bpow beta (-fexp (mxg - 1))
            ≤ x * bpow beta (-fexp (mxg - 1)) :=
              mul_le_mul_of_nonneg_right h_xy_le_x (bpow_ge_0 _ _)
          _ = bpow beta (mxg - 1 - fexp (mxg - 1)) := h_x_bpow)
    linarith

/-- `round_round_minus_aux1`: when `mag y ≤ fexp1(mag x) - 2` AND
`fexp1(mag(x-y)) - 1 ≤ mag y`, the subtraction is exact in `fexp2`-format. -/
theorem round_round_minus_aux1 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Py : 0 < y) (Hyx : y < x)
    (Hln : mag beta y ≤ fexp1 (mag beta x) - 2)
    (Hln' : fexp1 (mag beta (x - y)) - 1 ≤ mag beta y)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    generic_format beta fexp2 (x - y) := by
  obtain ⟨_, _, Hexp3, Hexp4⟩ := Hexp
  refine round_round_minus_aux0_aux beta fexp1 fexp2 x y ?_ ?_ Fx Fy
  · -- fexp2(mag(x-y)) ≤ fexp1(mag(x-y)) ≤ fexp1(mag x) (the second via Hln + Hln')
    have h1 : fexp2 (mag beta (x - y)) ≤ fexp1 (mag beta (x - y)) :=
      Hexp4 _ _ (by omega)
    omega
  · exact Hexp3 _ _ Hln'

/-- `round_round_minus_aux2`: mirror of `plus_aux1` for subtraction. When
`mag y ≤ fexp1(mag x) - 2` AND `mag y ≤ fexp1(mag(x-y)) - 2`, double
rounding of `x - y` is innocuous via `round_round_gt_mid`. -/
theorem round_round_minus_aux2 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Py : 0 < y) (Hxy : y < x)
    (Hly : mag beta y ≤ fexp1 (mag beta x) - 2)
    (Hly' : mag beta y ≤ fexp1 (mag beta (x - y)) - 2)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  have Px : 0 < x := lt_trans Py Hxy
  obtain ⟨_, _, _, Hexp4⟩ := Hexp
  have hxy_pos : 0 < x - y := by linarith
  have hxy_ne : x - y ≠ 0 := ne_of_gt hxy_pos
  have Bpow2 : bpow beta (-2) ≤ (1 : ℝ) / 4 := bpow_neg_two_le_quarter beta
  have Bpow1 : bpow beta (-1) ≤ (1 : ℝ) / 2 := bpow_neg_one_le_half beta
  -- y < bpow(mag y)
  have Ly_abs : y < bpow beta (mag beta y) := by
    have := bpow_mag_gt beta y; rw [abs_of_pos Py] at this; exact this
  -- The bound from aux2_aux: round_UP(x-y) - (x-y) ≤ y
  have h_aux : round beta fexp1 (fun y : ℝ => ⌈y⌉) (x - y) - (x - y) ≤ y :=
    round_round_minus_aux2_aux beta fexp1 Vfexp1 Py Hxy (by omega) Fx Fy
  -- fexp1(mag(x-y)) < mag(x-y) via valid_exp_large twice
  have Hfx : fexp1 (mag beta x) < mag beta x :=
    mag_generic_gt beta fexp1 Vfexp1 (ne_of_gt Px) Fx
  have Hfy : fexp1 (mag beta y) < mag beta y :=
    mag_generic_gt beta fexp1 Vfexp1 (ne_of_gt Py) Fy
  have h_fexp_mxm1_lt : fexp1 (mag beta x - 1) < mag beta x - 1 :=
    valid_exp_large Vfexp1 Hfy (by omega : mag beta y ≤ mag beta x - 1)
  have h_mag_minus_lb : mag beta x - 1 ≤ mag beta (x - y) :=
    mag_minus_lb beta Px Py (by omega)
  have h_fexp_mxy_lt : fexp1 (mag beta (x - y)) < mag beta (x - y) :=
    valid_exp_large Vfexp1 h_fexp_mxm1_lt h_mag_minus_lb
  -- bpow(mag y) ≤ bpow(fexp1(mag(x-y)) - 2)
  have h_pow_le : bpow beta (mag beta y) ≤ bpow beta (fexp1 (mag beta (x - y)) - 2) :=
    bpow_le beta Hly'
  -- ulp1 and ulp2 of x - y
  have h_ulp1 : ulp beta fexp1 (x - y) = bpow beta (fexp1 (mag beta (x - y))) := by
    rw [ulp_neq_0 _ _ hxy_ne]; rfl
  have h_ulp2 : ulp beta fexp2 (x - y) = bpow beta (fexp2 (mag beta (x - y))) := by
    rw [ulp_neq_0 _ _ hxy_ne]; rfl
  -- The key arithmetic: bpow(fexp - 2) ≤ (1/2) * bpow(fexp)
  have h_b1_pos : 0 < bpow beta (fexp1 (mag beta (x - y))) := bpow_gt_0 _ _
  have h_pow_bound1 : bpow beta (fexp1 (mag beta (x - y)) - 2)
      ≤ (1 : ℝ) / 2 * bpow beta (fexp1 (mag beta (x - y))) := by
    have h_split : bpow beta (fexp1 (mag beta (x - y)) - 2)
        = bpow beta (-2) * bpow beta (fexp1 (mag beta (x - y))) := by
      rw [← bpow_plus]; congr 1; ring
    rw [h_split]; nlinarith
  -- Apply round_round_gt_mid
  apply round_round_gt_mid beta Vfexp1 Vfexp2 choice1 choice2 hxy_pos
  · exact Hexp4 _ _ (by omega)
  · omega
  · -- midp' (x - y) < x - y
    unfold midp'
    rw [h_ulp1]
    -- Goal: round_UP(x-y) - (1/2) * bpow(fexp1(mag(x-y))) < x - y
    -- Equivalent: round_UP(x-y) - (x-y) < (1/2) * bpow(fexp1(mag(x-y)))
    -- Chain: round_UP - (x-y) ≤ y < bpow(mag y) ≤ bpow(fexp1(mag(x-y)) - 2)
    --        ≤ (1/2) * bpow(fexp1(mag(x-y)))
    linarith
  · -- Hf2' → midp' + (1/2) * ulp2 < x - y
    intro Hf2'
    unfold midp'
    rw [h_ulp1, h_ulp2]
    -- Goal: round_UP - (1/2) * bpow(fexp1) + (1/2) * bpow(fexp2) < x - y
    -- Equivalent: round_UP - (x-y) < (1/2) * (bpow(fexp1) - bpow(fexp2))
    have h_fexp2_le : fexp2 (mag beta (x - y)) ≤ fexp1 (mag beta (x - y)) - 1 := Hf2'
    have h_b2_pos : 0 < bpow beta (fexp2 (mag beta (x - y))) := bpow_gt_0 _ _
    have h_b2_le_b1m1 : bpow beta (fexp2 (mag beta (x - y)))
        ≤ bpow beta (fexp1 (mag beta (x - y)) - 1) := bpow_le beta h_fexp2_le
    have h_b1m1_split : bpow beta (fexp1 (mag beta (x - y)) - 1)
        = bpow beta (-1) * bpow beta (fexp1 (mag beta (x - y))) := by
      rw [← bpow_plus]; congr 1; ring
    have h_b2_le_half : bpow beta (fexp2 (mag beta (x - y)))
        ≤ (1 : ℝ) / 2 * bpow beta (fexp1 (mag beta (x - y))) := by
      rw [h_b1m1_split] at h_b2_le_b1m1; nlinarith
    have h_pow_bound2 : bpow beta (fexp1 (mag beta (x - y)) - 2)
        ≤ (1 : ℝ) / 2 * (bpow beta (fexp1 (mag beta (x - y)))
                          - bpow beta (fexp2 (mag beta (x - y)))) := by
      have h_split : bpow beta (fexp1 (mag beta (x - y)) - 2)
          = bpow beta (-2) * bpow beta (fexp1 (mag beta (x - y))) := by
        rw [← bpow_plus]; congr 1; ring
      rw [h_split]; nlinarith
    linarith

/-- Combine `minus_aux0`, `minus_aux1`, `minus_aux2` into one statement
under `0 < y ≤ x`. -/
theorem round_round_minus_aux3 (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Py : 0 < y) (Hyx : y ≤ x)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  by_cases hy_eq : y = x
  · rw [hy_eq]
    unfold round_round_eq
    rw [show x - x = 0 from by ring, round_0, round_0]
  · have Hyx' : y < x := lt_of_le_of_ne Hyx hy_eq
    rcases le_or_gt (mag beta y) (fexp1 (mag beta x) - 2) with Hly | Hly
    · -- mag y ≤ fexp1 (mag x) - 2
      rcases le_or_gt (mag beta y) (fexp1 (mag beta (x - y)) - 2) with Hly' | Hly'
      · -- mag y ≤ fexp1 (mag (x - y)) - 2: aux2
        exact round_round_minus_aux2 beta fexp1 fexp2 Vfexp1 Vfexp2
          choice1 choice2 Hexp Py Hyx' Hly Hly' Fx Fy
      · -- mag y > fexp1 (mag (x - y)) - 2: subtraction exact via aux1
        unfold round_round_eq
        have Hxy_fmt : generic_format beta fexp2 (x - y) :=
          round_round_minus_aux1 beta fexp1 fexp2 Hexp Py Hyx'
            Hly (by omega) Fx Fy
        rw [round_generic beta fexp2 (Znearest choice2) Hxy_fmt]
    · -- mag y > fexp1 (mag x) - 2: subtraction exact via aux0
      unfold round_round_eq
      have Hxy_fmt : generic_format beta fexp2 (x - y) :=
        round_round_minus_aux0 beta fexp1 fexp2 Hexp Py Hyx'
          (by omega) Fx Fy
      rw [round_generic beta fexp2 (Znearest choice2) Hxy_fmt]

/-- Drop the `y ≤ x` assumption: `0 ≤ x ∧ 0 ≤ y`. When `x < y`, rewrite
`x - y` as `-(y - x)` and use `round_N_opp` to flip signs, then apply
`minus_aux3` with the transformed choice functions. -/
theorem round_round_minus_aux (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (Vfexp1 : Valid_exp fexp1) (Vfexp2 : Valid_exp fexp2)
    (choice1 choice2 : ℤ → Bool)
    (Hexp : round_round_plus_hyp fexp1 fexp2)
    {x y : ℝ} (Nnx : 0 ≤ x) (Nny : 0 ≤ y)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 (x - y) := by
  have Hexp4 := Hexp.2.2.2
  by_cases hx0 : x = 0
  · subst hx0
    -- x - y = 0 - y = -y; y is in fexp2-format
    have Hy_fmt2 : generic_format beta fexp2 y :=
      generic_inclusion_mag beta fexp1 fexp2 (fun _ => Hexp4 _ _ (by omega)) Fy
    have Hny_fmt2 : generic_format beta fexp2 (0 - y) := by
      rw [zero_sub]; exact generic_format_opp beta fexp2 Hy_fmt2
    unfold round_round_eq
    rw [round_generic beta fexp2 (Znearest choice2) Hny_fmt2]
  · by_cases hy0 : y = 0
    · subst hy0
      have Hx_fmt2 : generic_format beta fexp2 (x - 0) := by
        rw [sub_zero]
        exact generic_inclusion_mag beta fexp1 fexp2
          (fun _ => Hexp4 _ _ (by omega)) Fx
      unfold round_round_eq
      rw [round_generic beta fexp2 (Znearest choice2) Hx_fmt2]
    · have Px : 0 < x := lt_of_le_of_ne Nnx (Ne.symm hx0)
      have Py : 0 < y := lt_of_le_of_ne Nny (Ne.symm hy0)
      rcases lt_or_ge x y with H | H
      · -- x < y: rewrite x - y = -(y - x), apply round_N_opp three times
        unfold round_round_eq
        rw [show x - y = -(y - x) from by ring]
        rw [round_N_opp beta fexp2 choice2]
        rw [round_N_opp beta fexp1 choice1]
        rw [round_N_opp beta fexp1 choice1 (y - x)]
        congr 1
        exact round_round_minus_aux3 beta fexp1 fexp2 Vfexp1 Vfexp2 _ _
          Hexp Px (le_of_lt H) Fy Fx
      · exact round_round_minus_aux3 beta fexp1 fexp2 Vfexp1 Vfexp2 choice1 choice2
          Hexp Py H Fx Fy

end LeanFlocq
