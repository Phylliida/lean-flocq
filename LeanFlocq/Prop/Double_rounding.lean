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

end LeanFlocq
