/-
# The difference of two roundings of nearby sums is exact (FLX, radix 2)

The reusable engine behind ErrFMA's crux lemma L1. Given two floats `a, b` and a
perturbation `e` no larger than half a ulp of *each* of `a` and `b`, the two
rounded sums

    x = round(a + b)        y = round(a + b + e)

are within a factor of two of each other (same sign), so by Sterbenz their
difference `x − y` is exactly representable.

This is the Flocq-native form of Pff's `Subexact` (the `GenericA`/`GenericB`
sections of `Pff.v`'s `FmaErr`). At FLX every normality / non-underflow side
condition of the Pff development vanishes: a nonzero sum of two floats has
`|a + b| ≥ β^min(cexp a, cexp b)`, and `|e|` is at most half of that, so the
perturbed sum keeps the sign and stays within `[½, 3⁄2]·|a+b|` — no separate
subnormal analysis is needed.

Setting: radix 2, FLX, round-to-nearest, `prec ≥ 3`.
-/
import LeanFlocq.Core.FLX
import LeanFlocq.Prop.Sterbenz
import LeanFlocq.Prop.Relative

namespace LeanFlocq

open radix (radix2)
open Classical

/-! ### Output-form relative error bound

The error of round-to-nearest is at most `u_ro` times the *rounded value*
(rather than the input). This is the form Pff calls `ClosestRoundeLeNormal`
/ `ClosestRoundeGeNormal`, and it is what drives the factor-of-two argument. -/

/-- `|round z − z| ≤ u_ro · |round z|` at FLX. -/
theorem err_le_uro_round_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) (z : ℝ) :
    |round beta (FLX_exp prec) (Znearest choice) z - z|
      ≤ u_ro beta prec * |round beta (FLX_exp prec) (Znearest choice) z| := by
  set r := round beta (FLX_exp prec) (Znearest choice) z with hr
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNotFTZ := monotone_exp_not_FTZ hValid hMon
  have h1 : |r - z| ≤ (1 / 2) * ulp beta (FLX_exp prec) r :=
    error_le_half_ulp_round beta (FLX_exp prec) hValid hNotFTZ hMon choice z
  have h2 : ulp beta (FLX_exp prec) r ≤ |r| * bpow beta (1 - prec) :=
    ulp_FLX_le beta prec hp r
  have hupos : (0 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  calc |r - z| ≤ (1 / 2) * ulp beta (FLX_exp prec) r := h1
    _ ≤ (1 / 2) * (|r| * bpow beta (1 - prec)) := by
          exact mul_le_mul_of_nonneg_left h2 hupos
    _ = u_ro beta prec * |r| := by
          unfold u_ro; rw [show (1 - prec) = (-prec + 1) from by ring]; ring

/-! ### A nonzero sum of two floats sits on the common grid -/

/-- For `a, b ∈ F(FLX)` with `a + b ≠ 0`, the sum is a *nonzero integer* multiple
of `β^m`, where `m = min(cexp a, cexp b)`. -/
theorem add_int_mul_bpow_min (beta : radix) (prec : ℤ) {a b : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (hne : a + b ≠ 0) :
    ∃ K : ℤ, K ≠ 0 ∧
      a + b = (K : ℝ)
        * bpow beta (min (cexp beta (FLX_exp prec) a) (cexp beta (FLX_exp prec) b)) := by
  set ea := cexp beta (FLX_exp prec) a with hea
  set eb := cexp beta (FLX_exp prec) b with heb
  set m := min ea eb with hm
  set Ma := Ztrunc (scaled_mantissa beta (FLX_exp prec) a) with hMa
  set Mb := Ztrunc (scaled_mantissa beta (FLX_exp prec) b) with hMb
  have ha : a = F2R (beta := beta) ⟨Ma, ea⟩ := Fa
  have hb : b = F2R (beta := beta) ⟨Mb, eb⟩ := Fb
  have hma : m ≤ ea := min_le_left _ _
  have hmb : m ≤ eb := min_le_right _ _
  have ha' : a = F2R (beta := beta) ⟨Ma * (beta.val : ℤ) ^ (ea - m).toNat, m⟩ := by
    rw [ha]; exact F2R_change_exp m Ma ea hma
  have hb' : b = F2R (beta := beta) ⟨Mb * (beta.val : ℤ) ^ (eb - m).toNat, m⟩ := by
    rw [hb]; exact F2R_change_exp m Mb eb hmb
  set Ka := Ma * (beta.val : ℤ) ^ (ea - m).toNat with hKa
  set Kb := Mb * (beta.val : ℤ) ^ (eb - m).toNat with hKb
  have hab : a + b = F2R (beta := beta) ⟨Ka + Kb, m⟩ := by
    rw [ha', hb', ← F2R_plus, Fplus_same_exp]
  refine ⟨Ka + Kb, ?_, ?_⟩
  · intro h0
    apply hne
    rw [hab, h0]
    show F2R (beta := beta) ⟨(0 : ℤ), m⟩ = 0
    rw [F2R_0]
  · rw [hab]; rfl

/-- The absolute value of a nonzero float-sum is `≥ β^m`, and either `= β^m`
(boundary) or `≥ 2·β^m` (bulk), where `m = min(cexp a, cexp b)`. -/
theorem abs_add_eq_or_ge_two_bpow_min (beta : radix) (prec : ℤ) {a b : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (hne : a + b ≠ 0) :
    bpow beta (min (cexp beta (FLX_exp prec) a) (cexp beta (FLX_exp prec) b)) ≤ |a + b|
      ∧ (|a + b| = bpow beta (min (cexp beta (FLX_exp prec) a) (cexp beta (FLX_exp prec) b))
          ∨ 2 * bpow beta (min (cexp beta (FLX_exp prec) a) (cexp beta (FLX_exp prec) b))
              ≤ |a + b|) := by
  obtain ⟨K, hK, hKeq⟩ := add_int_mul_bpow_min beta prec Fa Fb hne
  set m := min (cexp beta (FLX_exp prec) a) (cexp beta (FLX_exp prec) b) with hm
  have hbp : (0 : ℝ) < bpow beta m := bpow_gt_0 beta m
  have habs : |a + b| = |(K : ℝ)| * bpow beta m := by
    rw [hKeq, abs_mul, abs_of_pos hbp]
  have hK1 : (1 : ℤ) ≤ |K| := Int.one_le_abs hK
  have h1K : (1 : ℝ) ≤ |(K : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hK1
  have hge : bpow beta m ≤ |a + b| := by
    rw [habs]; nlinarith [hbp, h1K]
  refine ⟨hge, ?_⟩
  rcases eq_or_lt_of_le hK1 with h1 | h2
  · left; rw [habs]
    have : |(K : ℝ)| = 1 := by rw [← Int.cast_abs, ← h1]; norm_num
    rw [this, one_mul]
  · right
    have h2K : (2 : ℝ) ≤ |(K : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h2
    rw [habs]; nlinarith [hbp, h2K]

/-! ### Signed Sterbenz: difference is exact under same sign + factor of two -/

/-- Sterbenz in absolute-value form: if `x, y` have the same sign and each has
magnitude within a factor of two of the other, then `x − y` is exact. -/
theorem sterbenz_abs (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) (hMon : Monotone_exp fexp)
    {x y : ℝ} (Fx : generic_format beta fexp x) (Fy : generic_format beta fexp y)
    (Hsign : (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0))
    (Hxy : |x| ≤ 2 * |y|) (Hyx : |y| ≤ 2 * |x|) :
    generic_format beta fexp (x - y) := by
  rcases Hsign with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [abs_of_nonneg hx, abs_of_nonneg hy] at Hxy Hyx
    exact sterbenz beta fexp hValid hMon Fx Fy ⟨by linarith, by linarith⟩
  · rw [abs_of_nonpos hx, abs_of_nonpos hy] at Hxy Hyx
    have hst := sterbenz beta fexp hValid hMon
      (generic_format_opp beta fexp Fx) (generic_format_opp beta fexp Fy)
      ⟨by linarith, by linarith⟩
    rw [show -x - -y = -(x - y) from by ring] at hst
    have := generic_format_opp beta fexp hst
    rwa [neg_neg] at this

/-! ### The engine: difference of two roundings of nearby sums is exact -/

/-- **Round-minus-round exactness (FLX, radix 2).** For `a, b ∈ F` and a
perturbation `e` no larger than half a ulp of *each* of `a` and `b`,

    round(a + b) − round(a + b + e) ∈ F.

The Flocq-native form of Pff's `Subexact`. The two roundings stay within a
factor of two of each other (and keep the same sign), so Sterbenz applies. -/
theorem round_minus_round_nearby_exact_FLX (prec : ℤ) (hp : 3 ≤ prec)
    (choice : ℤ → Bool) {a b e : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hea : |e| ≤ 1/2 * ulp radix2 (FLX_exp prec) a)
    (Heb : |e| ≤ 1/2 * ulp radix2 (FLX_exp prec) b) :
    generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a + b)
        - round radix2 (FLX_exp prec) (Znearest choice) (a + b + e)) := by
  have hp0 : 0 < prec := by omega
  have hValid := FLX_exp_valid prec hp0
  have hMon := FLX_exp_monotone prec
  set x := round radix2 (FLX_exp prec) (Znearest choice) (a + b) with hx_def
  set y := round radix2 (FLX_exp prec) (Znearest choice) (a + b + e) with hy_def
  have Fx : generic_format radix2 (FLX_exp prec) x := generic_format_round _ _ hValid _ _
  have Fy : generic_format radix2 (FLX_exp prec) y := generic_format_round _ _ hValid _ _
  -- Collapse case: e = 0 makes x = y (covers a = 0, b = 0 via ulp 0 = 0).
  by_cases he0 : e = 0
  · have hxy : x = y := by rw [hx_def, hy_def, he0, add_zero]
    rw [show x - y = 0 from by rw [hxy]; ring]
    exact generic_format_0 _ _
  · have ha0 : a ≠ 0 := by
      intro h; apply he0
      rw [h, ulp_FLX_0 radix2 prec hp0, mul_zero] at Hea
      exact abs_eq_zero.mp (le_antisymm Hea (abs_nonneg e))
    have hb0 : b ≠ 0 := by
      intro h; apply he0
      rw [h, ulp_FLX_0 radix2 prec hp0, mul_zero] at Heb
      exact abs_eq_zero.mp (le_antisymm Heb (abs_nonneg e))
    -- a + b = 0 case: x = 0, so x − y = −y ∈ F.
    by_cases hs0 : a + b = 0
    · have hx0 : x = 0 := by
        rw [hx_def, hs0]; exact round_0 radix2 (FLX_exp prec) (Znearest choice)
      rw [hx0, zero_sub]; exact generic_format_opp _ _ Fy
    · -- Main case: a, b, a+b all nonzero.
      set ea := cexp radix2 (FLX_exp prec) a with hea
      set eb := cexp radix2 (FLX_exp prec) b with heb
      set m := min ea eb with hm
      have hbp : (0 : ℝ) < bpow radix2 m := bpow_gt_0 radix2 m
      -- e bound against β^m
      have Hea' : |e| ≤ 1/2 * bpow radix2 ea := by
        rwa [ulp_neq_0 radix2 (FLX_exp prec) ha0] at Hea
      have Heb' : |e| ≤ 1/2 * bpow radix2 eb := by
        rwa [ulp_neq_0 radix2 (FLX_exp prec) hb0] at Heb
      have Hem : |e| ≤ 1/2 * bpow radix2 m := by
        rcases le_total ea eb with h | h
        · rw [hm, min_eq_left h]; exact Hea'
        · rw [hm, min_eq_right h]; exact Heb'
      -- structural bounds on |a+b|
      obtain ⟨hge, hdich⟩ := abs_add_eq_or_ge_two_bpow_min radix2 prec Fa Fb hs0
      rw [← hea, ← heb, ← hm] at hge hdich
      -- relative error bounds in output form
      have hxe : |x - (a + b)| ≤ u_ro radix2 prec * |x| := by
        have := err_le_uro_round_FLX radix2 prec hp0 choice (a + b); rwa [← hx_def] at this
      have hye : |y - (a + b + e)| ≤ u_ro radix2 prec * |y| := by
        have := err_le_uro_round_FLX radix2 prec hp0 choice (a + b + e); rwa [← hy_def] at this
      -- u_ro ≤ 1/8
      have huro : u_ro radix2 prec ≤ 1/8 := by
        unfold u_ro
        have hb2 : bpow radix2 (-prec + 1) ≤ bpow radix2 (-2 : ℤ) := bpow_le radix2 (by omega)
        have h14 : bpow radix2 (-2 : ℤ) = 1/4 := by
          show ((radix2.val : ℝ)) ^ (-2 : ℤ) = 1/4
          have : (radix2.val : ℝ) = 2 := by norm_cast
          rw [this]; norm_num
        rw [h14] at hb2; linarith
      have huro0 : 0 ≤ u_ro radix2 prec := u_ro_pos radix2 prec
      have hX : (0 : ℝ) ≤ |x| := abs_nonneg x
      have hY : (0 : ℝ) ≤ |y| := abs_nonneg y
      -- triangle facts relating |x|,|y| to S = |a+b|, S' = |a+b+e|
      have hSx : |a + b| - |x| ≤ u_ro radix2 prec * |x| := by
        have h := abs_sub_abs_le_abs_sub (a + b) x
        rw [show (a + b) - x = -(x - (a + b)) from by ring, abs_neg] at h
        linarith [hxe]
      have hSx2 : |x| - |a + b| ≤ u_ro radix2 prec * |x| := by
        have h := abs_sub_abs_le_abs_sub x (a + b); linarith [hxe]
      have hSy : |y| - |a + b + e| ≤ u_ro radix2 prec * |y| := by
        have h := abs_sub_abs_le_abs_sub y (a + b + e); linarith [hye]
      have hSy2 : |a + b + e| - |y| ≤ u_ro radix2 prec * |y| := by
        have h := abs_sub_abs_le_abs_sub (a + b + e) y
        rw [show (a + b + e) - y = -(y - (a + b + e)) from by ring, abs_neg] at h
        linarith [hye]
      -- S' ≤ S + |e| and S' ≥ S − |e|
      have hStri1 : |a + b + e| ≤ |a + b| + |e| := by
        have := abs_add_le (a + b) e; linarith
      have hStri2 : |a + b| - |e| ≤ |a + b + e| := by
        have := abs_sub_abs_le_abs_sub (a + b) (a + b + e)
        rw [show (a + b) - (a + b + e) = -e from by ring, abs_neg] at this
        linarith
      -- sign consistency
      have hsign : (0 ≤ x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ y ≤ 0) := by
        have hab_pos_or_neg := lt_or_gt_of_ne hs0
        rcases hab_pos_or_neg with hneg | hpos
        · right
          have habs : |a + b| = -(a + b) := abs_of_neg hneg
          have hse : a + b + e ≤ 0 := by
            have := le_abs_self e; linarith [Hem, hge, habs]
          refine ⟨?_, ?_⟩
          · rw [hx_def]
            exact round_le_generic radix2 (FLX_exp prec) hValid _ (generic_format_0 _ _)
              (le_of_lt hneg)
          · rw [hy_def]
            exact round_le_generic radix2 (FLX_exp prec) hValid _ (generic_format_0 _ _) hse
        · left
          have habs : |a + b| = a + b := abs_of_pos hpos
          have hse : 0 ≤ a + b + e := by
            have := neg_abs_le e; linarith [Hem, hge, habs]
          refine ⟨?_, ?_⟩
          · rw [hx_def]
            exact round_ge_generic radix2 (FLX_exp prec) hValid _ (generic_format_0 _ _)
              (le_of_lt hpos)
          · rw [hy_def]
            exact round_ge_generic radix2 (FLX_exp prec) hValid _ (generic_format_0 _ _) hse
      -- factor-of-two bound: |y| ≤ 2|x| (no boundary split needed)
      have hYleX : |y| ≤ 2 * |x| := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1/8 - u_ro radix2 prec) hX,
          mul_nonneg (by linarith : (0:ℝ) ≤ 1/8 - u_ro radix2 prec) hY,
          hSy, hSx2, hStri1, Hem, hge]
      -- factor-of-two bound: |x| ≤ 2|y| (needs boundary/bulk dichotomy)
      have hXleY : |x| ≤ 2 * |y| := by
        rcases hdich with hbdry | hbulk
        · -- boundary: |a+b| = β^m, so a+b ∈ F and x = a+b.
          have hF_bpow : generic_format radix2 (FLX_exp prec) (bpow radix2 m) :=
            generic_format_bpow radix2 (FLX_exp prec) m (by unfold FLX_exp; omega)
          have hF_ab : generic_format radix2 (FLX_exp prec) (a + b) := by
            rcases (abs_eq (le_of_lt hbp)).mp hbdry with hpos | hneg
            · rw [hpos]; exact hF_bpow
            · rw [hneg]; exact generic_format_opp _ _ hF_bpow
          have hx_eq : x = a + b := by
            rw [hx_def]; exact round_generic radix2 (FLX_exp prec) (Znearest choice) hF_ab
          have hXval : |x| = bpow radix2 m := by rw [hx_eq, hbdry]
          -- β^(m-1) = ½β^m ∈ F and ≤ |a+b+e|, so ≤ |y|
          have hbpm1 : bpow radix2 (m - 1) = 1/2 * bpow radix2 m := by
            rw [show m - 1 = m + (-1) from by ring, bpow_plus]
            have : bpow radix2 (-1 : ℤ) = 1/2 := by
              show ((radix2.val : ℝ)) ^ (-1 : ℤ) = 1/2
              have : (radix2.val : ℝ) = 2 := by norm_cast
              rw [this]; norm_num
            rw [this]; ring
          have hF_half : generic_format radix2 (FLX_exp prec) (bpow radix2 (m - 1)) :=
            generic_format_bpow radix2 (FLX_exp prec) (m - 1) (by unfold FLX_exp; omega)
          have hhalf_le : bpow radix2 (m - 1) ≤ |a + b + e| := by
            rw [hbpm1]; linarith [hStri2, Hem, hbdry]
          have hYge : bpow radix2 (m - 1) ≤ |y| := by
            rw [hy_def]
            exact abs_round_ge_generic radix2 (FLX_exp prec) hValid (Znearest choice)
              hF_half hhalf_le
          rw [hXval]; rw [hbpm1] at hYge; linarith
        · -- bulk: 2β^m ≤ |a+b|, so |e| ≤ ¼|a+b|, S ≤ (4/3)S'.
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1/8 - u_ro radix2 prec) hX,
            mul_nonneg (by linarith : (0:ℝ) ≤ 1/8 - u_ro radix2 prec) hY,
            hSy2, hSx, hStri2, Hem, hbulk]
      exact sterbenz_abs radix2 (FLX_exp prec) hValid hMon Fx Fy hsign hXleY hYleX

end LeanFlocq
