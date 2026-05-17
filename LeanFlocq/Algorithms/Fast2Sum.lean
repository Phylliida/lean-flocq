/-
Fast2Sum: the error-free transformation for floating-point addition under
the precondition |b| ≤ |a|.

Not part of Coq Flocq's main library — Flocq's version lives in the older
Pff theory (`Pff.v`'s Dekker_FTS). We prove it directly on top of Flocq's
Lean port, following the classical Boldo-Daumas-Muller structure.

Setting: radix 2, FLX format, round-to-nearest. The radix-2 assumption is
used because the proof relies on `a/2 ∈ format`.

The algorithm:
  s := round(a + b)
  z := round(s - a)   -- claim: z = s - a (exact)
  e := round(b - z)   -- claim: e = a + b - s (exact)
Then `a + b = s + e` exactly.
-/
import LeanFlocq.Core.FLX
import LeanFlocq.Core.FLT
import LeanFlocq.Prop.Sterbenz
import LeanFlocq.Prop.Mult_error
import LeanFlocq.Prop.Plus_error

namespace LeanFlocq

open radix (radix2)

/-! ### Helper rewrites for `radix2` -/

/-- `(radix2.val : ℝ) = 2`. -/
private theorem radix2_val_cast : (radix2.val : ℝ) = 2 := by norm_cast

/-- `bpow radix2 (-1) = 1/2`. -/
private theorem bpow_radix2_neg_one : bpow radix2 (-1) = 1 / 2 := by
  unfold bpow
  show ((radix2.val : ℝ) ^ (-1 : ℤ)) = 1 / 2
  rw [radix2_val_cast]; norm_num

/-- `a / 2 = a * bpow radix2 (-1)`. -/
private theorem div_two_eq_mul_bpow (a : ℝ) : a / 2 = a * bpow radix2 (-1) := by
  rw [bpow_radix2_neg_one]; ring

/-- `2 * a = a * bpow radix2 1`. -/
private theorem two_mul_eq_mul_bpow (a : ℝ) : 2 * a = a * bpow radix2 1 := by
  rw [bpow_one, radix2_val_cast]; ring

/-! ### FLT helpers (radix 2) -/

/-- For `a ∈ FLT_exp emin prec (radix 2)`, the value `2 * a` is also in FLT.

Direct construction via `generic_format_F2R'`; unlike `mult_bpow_exact_FLT`,
no precondition on `mag a` is needed because the shift exponent is non-negative
(so `cexp(2a) ≤ cexp(a) + 1` falls out of `max` monotonicity without
constraining the small-denormal case). -/
private theorem two_mul_in_FLT_radix2 (emin prec : ℤ)
    {a : ℝ} (Fa : generic_format radix2 (FLT_exp emin prec) a) :
    generic_format radix2 (FLT_exp emin prec) (2 * a) := by
  by_cases Ha : a = 0
  · rw [Ha, mul_zero]; exact generic_format_0 _ _
  set ma := Ztrunc (scaled_mantissa radix2 (FLT_exp emin prec) a) with hma_def
  set ea := cexp radix2 (FLT_exp emin prec) a with hea_def
  have ha_eq : a = (ma : ℝ) * bpow radix2 ea := Fa
  refine generic_format_F2R' radix2 (FLT_exp emin prec)
    (⟨ma, ea + 1⟩ : float radix2) ?_ ?_
  · -- F2R ⟨ma, ea + 1⟩ = 2 * a.
    show (ma : ℝ) * bpow radix2 (ea + 1) = 2 * a
    rw [two_mul_eq_mul_bpow, ha_eq, bpow_plus]
    ring
  · -- cexp(2a) ≤ ea + 1.
    intro _
    show cexp radix2 (FLT_exp emin prec) (2 * a) ≤ ea + 1
    rw [two_mul_eq_mul_bpow a]
    unfold cexp
    rw [mag_mult_bpow radix2 Ha 1]
    show FLT_exp emin prec (mag radix2 a + 1) ≤ ea + 1
    have hea_eq : ea = max (mag radix2 a - prec) emin := by
      show cexp radix2 (FLT_exp emin prec) a = _
      unfold cexp FLT_exp; rfl
    unfold FLT_exp
    rw [hea_eq]
    omega

/-- For `d` with `0 ≤ d < bpow(emin + prec)` (i.e., in the subnormal regime),
the next F-value above `d` is `d + bpow(emin)`. -/
private theorem succ_FLT_subnormal_step (emin prec : ℤ) (hp : 0 < prec) {d : ℝ}
    (hd_nn : 0 ≤ d) (hd_bound : d < bpow radix2 (emin + prec)) :
    succ radix2 (FLT_exp emin prec) d = d + bpow radix2 emin := by
  rw [succ_eq_pos radix2 (FLT_exp emin prec) hd_nn]
  congr 1
  exact ulp_FLT_small radix2 emin prec hp
    (by rw [abs_of_nonneg hd_nn]; exact hd_bound)

/-- For `a ∈ FLT (radix 2), 0 < a, a/2 < v` (strict), `a/2 ≤ round_N(v)`.

The "strict" precondition is essential — the weak version is false when
`a/2 ∉ F` and tie-breaking picks the floor of the two F-neighbors of `a/2`.
With strict `a/2 < v`, round-to-nearest is forced to pick the ceiling.

Proof strategy: case split on whether `a/2 ∈ F`. If yes, direct via
`round_ge_generic`. If no, then `cexp(a) = emin` and the mantissa `ma` of
`a` is odd. Define `d := k · bpow(emin)` and `u := (k+1) · bpow(emin)`
where `ma = 2k + 1`. These are consecutive F-values with `a/2` exactly
at their midpoint (radix-2 symmetry). Apply `round_N_ge_midp`. -/
private theorem round_N_gt_half_FLT_radix2 (emin prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {a v : ℝ}
    (Fa : generic_format radix2 (FLT_exp emin prec) a)
    (Ha : 0 < a) (Hv : a / 2 < v) :
    a / 2 ≤ round radix2 (FLT_exp emin prec) (Znearest choice) v := by
  have hValid := FLT_exp_valid emin prec hp
  -- Case A: a/2 ∈ F. Direct.
  by_cases Fhalf : generic_format radix2 (FLT_exp emin prec) (a / 2)
  · exact round_ge_generic radix2 (FLT_exp emin prec) hValid (Znearest choice)
      Fhalf (le_of_lt Hv)
  -- Case B: a/2 ∉ F.
  set ma := Ztrunc (scaled_mantissa radix2 (FLT_exp emin prec) a) with hma_def
  set ea := cexp radix2 (FLT_exp emin prec) a with hea_def
  have ha_F2R : a = (ma : ℝ) * bpow radix2 ea := Fa
  have ha_ne : a ≠ 0 := ne_of_gt Ha
  have hea_form : ea = max (mag radix2 a - prec) emin := by
    rw [hea_def]; show cexp radix2 (FLT_exp emin prec) a = _
    unfold cexp FLT_exp; rfl
  -- Step 1: ea = emin (else a/2 ∈ F at exponent ea - 1).
  have hea_emin : ea = emin := by
    have hea_ge : emin ≤ ea := by rw [hea_form]; exact le_max_right _ _
    by_contra hne
    have hea_gt : emin < ea := lt_of_le_of_ne hea_ge (Ne.symm hne)
    apply Fhalf
    -- a/2 = ma * bpow(ea - 1).
    have ha_half_eq : a / 2 = (ma : ℝ) * bpow radix2 (ea - 1) := by
      rw [ha_F2R]
      have hbpow : bpow radix2 ea = bpow radix2 (ea - 1) * 2 := by
        have h_split : bpow radix2 ea = bpow radix2 ((ea - 1) + 1) := by
          congr 1; ring
        rw [h_split, bpow_plus, bpow_one, radix2_val_cast]
      rw [hbpow]; ring
    rw [ha_half_eq]
    refine generic_format_F2R radix2 (FLT_exp emin prec) ma (ea - 1) ?_
    intro _
    show FLT_exp emin prec (mag radix2 (F2R (⟨ma, ea - 1⟩ : float radix2))) ≤ ea - 1
    have h_F2R : F2R (⟨ma, ea - 1⟩ : float radix2) = a / 2 := by
      show (ma : ℝ) * bpow radix2 (ea - 1) = a / 2
      rw [← ha_half_eq]
    rw [h_F2R]
    have h_mag_half : mag radix2 (a / 2) = mag radix2 a - 1 := by
      rw [div_two_eq_mul_bpow a, mag_mult_bpow radix2 ha_ne (-1)]; ring
    rw [h_mag_half]
    -- ea = mag a - prec since ea > emin.
    have h_ea_normal : ea = mag radix2 a - prec := by
      rw [hea_form]
      apply max_eq_left
      by_contra hlt
      push_neg at hlt
      have : ea = emin := by rw [hea_form]; exact max_eq_right (le_of_lt hlt)
      linarith
    unfold FLT_exp
    have h_lhs : mag radix2 a - 1 - prec = ea - 1 := by linarith
    rw [h_lhs]
    exact max_le (le_refl _) (by linarith)
  -- Step 2: ma > 0.
  have hma_pos : 0 < ma := by
    have h_bpow_pos : (0 : ℝ) < bpow radix2 ea := bpow_gt_0 _ _
    have h_ma_pos_R : 0 < (ma : ℝ) := by
      have h := ha_F2R ▸ Ha
      exact (mul_pos_iff_of_pos_right h_bpow_pos).mp h
    exact_mod_cast h_ma_pos_R
  -- Step 3: ma is odd (else a/2 = (ma/2) * bpow(emin) ∈ F).
  have h_mag_a_le : mag radix2 a ≤ emin + prec := by
    rw [hea_form] at hea_emin
    rcases le_or_gt (mag radix2 a - prec) emin with h | h
    · linarith
    · rw [max_eq_left (le_of_lt h)] at hea_emin; linarith
  have h_a_lt : a < bpow radix2 (emin + prec) := by
    have h_a_lt_mag : a < bpow radix2 (mag radix2 a) := by
      have h_abs := bpow_mag_gt radix2 a
      rwa [abs_of_pos Ha] at h_abs
    have h_mag_le : bpow radix2 (mag radix2 a) ≤ bpow radix2 (emin + prec) :=
      bpow_le radix2 h_mag_a_le
    linarith
  have hma_odd : Odd ma := by
    rcases Int.even_or_odd ma with hma_ev | hma_od
    · exfalso
      apply Fhalf
      obtain ⟨j, hj⟩ := hma_ev
      have ha_half_eq : a / 2 = (j : ℝ) * bpow radix2 emin := by
        rw [ha_F2R, hea_emin, hj]
        push_cast; ring
      rw [ha_half_eq]
      refine generic_format_F2R radix2 (FLT_exp emin prec) j emin ?_
      intro _
      show FLT_exp emin prec (mag radix2 (F2R (⟨j, emin⟩ : float radix2))) ≤ emin
      have h_F2R : F2R (⟨j, emin⟩ : float radix2) = a / 2 := by
        show (j : ℝ) * bpow radix2 emin = a / 2
        rw [← ha_half_eq]
      rw [h_F2R]
      unfold FLT_exp
      apply max_le _ (le_refl _)
      have h_mag_half : mag radix2 (a / 2) = mag radix2 a - 1 := by
        rw [div_two_eq_mul_bpow a, mag_mult_bpow radix2 ha_ne (-1)]; ring
      rw [h_mag_half]; linarith
    · exact hma_od
  -- Step 4: extract k from ma = 2 * k + 1.
  obtain ⟨k, hk_eq⟩ := hma_odd
  have hk_nn : 0 ≤ k := by linarith
  -- Step 5: define d, u and show in F.
  set d := (k : ℝ) * bpow radix2 emin with hd_def
  set u := ((k + 1 : ℤ) : ℝ) * bpow radix2 emin with hu_def
  have h_d_nn : 0 ≤ d := by
    rw [hd_def]; exact mul_nonneg (by exact_mod_cast hk_nn) (bpow_ge_0 _ _)
  have h_u_eq_a_sub_d : u = a - d := by
    rw [hu_def, hd_def, ha_F2R, hea_emin]
    have h_ma_cast : ((ma : ℤ) : ℝ) = (2 * k + 1 : ℤ) := by exact_mod_cast hk_eq
    rw [h_ma_cast]
    push_cast; ring
  have h_u_pos : 0 < u := by
    rw [hu_def]
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℤ) : ℝ) := by
      have : (0 : ℤ) < k + 1 := by linarith
      exact_mod_cast this
    exact mul_pos hk1_pos (bpow_gt_0 _ _)
  have h_d_lt_u : d < u := by
    rw [h_u_eq_a_sub_d, hd_def]
    -- a > 2 * k * bpow(emin) since a = (2k+1) * bpow(emin).
    rw [ha_F2R, hea_emin]
    have h_ma_cast : ((ma : ℤ) : ℝ) = (2 * k + 1 : ℤ) := by exact_mod_cast hk_eq
    rw [h_ma_cast]
    have h_bpow_pos : (0 : ℝ) < bpow radix2 emin := bpow_gt_0 _ _
    push_cast; linarith
  have h_d_lt : d < bpow radix2 (emin + prec) := by
    have : d < a := by rw [← sub_pos]; linarith [h_u_eq_a_sub_d ▸ h_u_pos]
    linarith
  have h_u_le_a : u ≤ a := by rw [h_u_eq_a_sub_d]; linarith
  have h_u_lt : u < bpow radix2 (emin + prec) := by linarith
  have Fd : generic_format radix2 (FLT_exp emin prec) d := by
    rw [hd_def]
    refine generic_format_F2R radix2 (FLT_exp emin prec) k emin ?_
    intro hk_ne
    show FLT_exp emin prec (mag radix2 (F2R (⟨k, emin⟩ : float radix2))) ≤ emin
    have h_F2R_d : F2R (⟨k, emin⟩ : float radix2) = d := by
      show (k : ℝ) * bpow radix2 emin = d
      rw [hd_def]
    rw [h_F2R_d]
    unfold FLT_exp
    apply max_le _ (le_refl _)
    have h_d_pos : 0 < d := by
      have h_k_pos : 0 < (k : ℝ) := by
        have : (0 : ℤ) < k := lt_of_le_of_ne hk_nn (Ne.symm hk_ne)
        exact_mod_cast this
      rw [hd_def]; exact mul_pos h_k_pos (bpow_gt_0 _ _)
    have h_d_ne : d ≠ 0 := ne_of_gt h_d_pos
    have h_mag_d : mag radix2 d ≤ emin + prec :=
      mag_le_bpow radix2 h_d_ne (by rw [abs_of_pos h_d_pos]; exact h_d_lt)
    linarith
  have Fu : generic_format radix2 (FLT_exp emin prec) u := by
    rw [hu_def]
    refine generic_format_F2R radix2 (FLT_exp emin prec) (k + 1) emin ?_
    intro _
    show FLT_exp emin prec (mag radix2 (F2R (⟨k + 1, emin⟩ : float radix2))) ≤ emin
    have h_F2R_u : F2R (⟨k + 1, emin⟩ : float radix2) = u := by
      show ((k + 1 : ℤ) : ℝ) * bpow radix2 emin = u
      rw [hu_def]
    rw [h_F2R_u]
    unfold FLT_exp
    apply max_le _ (le_refl _)
    have h_u_ne : u ≠ 0 := ne_of_gt h_u_pos
    have h_mag_u : mag radix2 u ≤ emin + prec :=
      mag_le_bpow radix2 h_u_ne (by rw [abs_of_pos h_u_pos]; exact h_u_lt)
    linarith
  -- Step 6: succ d = u.
  have h_succ_d : succ radix2 (FLT_exp emin prec) d = u := by
    rw [succ_FLT_subnormal_step emin prec hp h_d_nn h_d_lt]
    rw [hd_def, hu_def]
    push_cast; ring
  -- Step 7: pred u = d.
  have h_pred_u : pred radix2 (FLT_exp emin prec) u = d := by
    rw [← h_succ_d]
    exact pred_succ radix2 (FLT_exp emin prec) hValid Fd
  -- Step 8: midpoint = a/2.
  have h_midpoint : (u + pred radix2 (FLT_exp emin prec) u) / 2 = a / 2 := by
    rw [h_pred_u, h_u_eq_a_sub_d]; ring
  -- Step 9: a/2 < u (strict, since midpoint < u and a/2 = midpoint).
  have h_half_lt_u : a / 2 < u := by
    have h_mid_lt : (u + d) / 2 < u := by linarith
    have h_eq : (u + d) / 2 = a / 2 := by rw [h_u_eq_a_sub_d]; ring
    linarith
  -- Step 10: apply round_N_ge_midp.
  have h_round_ge_u : u ≤ round radix2 (FLT_exp emin prec) (Znearest choice) v :=
    round_N_ge_midp radix2 (FLT_exp emin prec) hValid choice Fu
      (by rw [h_midpoint]; exact Hv)
  linarith

/-! ### The Sterbenz step (positive case) -/

/-- Step 1, positive case: under `0 < a` and `|b| ≤ a`, the second
subtraction in Fast2Sum is exact — `round(a + b) - a ∈ FLX_format`. -/
private theorem Fast2Sum_step1_pos
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ} (Ha : 0 < a)
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ a) :
    generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by
  set s := round radix2 (FLX_exp prec) (Znearest choice) (a + b) with hs_def
  have hValid := FLX_exp_valid prec Hp
  have hMon := FLX_exp_monotone prec
  -- a/2 ∈ format and 2a ∈ format (closure under multiplication by bpow).
  have hFa_half : generic_format radix2 (FLX_exp prec) (a / 2) := by
    rw [div_two_eq_mul_bpow]
    exact mult_bpow_exact_FLX radix2 prec (-1) Fa
  have hFa_two : generic_format radix2 (FLX_exp prec) (2 * a) := by
    rw [two_mul_eq_mul_bpow]
    exact mult_bpow_exact_FLX radix2 prec 1 Fa
  -- The two-case argument: either b is large-negative (|b| > a/2) or not.
  rcases lt_or_ge b (-(a/2)) with Hcase2 | Hcase1
  · -- Case 2: b < -a/2. Then a + b ∈ F by Sterbenz on (a, -b).
    have h_b_neg : b < 0 := by linarith
    have h_b_abs : |b| = -b := abs_of_neg h_b_neg
    have h_neg_b_le_a : -b ≤ a := by rw [← h_b_abs]; exact Hab
    -- Sterbenz needs (-b)/2 ≤ a ≤ 2(-b).
    have h_ab_in_F : generic_format radix2 (FLX_exp prec) (a + b) := by
      have h_sub_eq : a - (-b) = a + b := by ring
      have h_sterbenz : generic_format radix2 (FLX_exp prec) (a - (-b)) :=
        sterbenz radix2 (FLX_exp prec) hValid hMon Fa
          (generic_format_opp radix2 (FLX_exp prec) Fb)
          ⟨by linarith, by linarith⟩
      rwa [h_sub_eq] at h_sterbenz
    -- s = round(a + b) = a + b, so s - a = b ∈ F.
    have hs_eq : s = a + b := by
      rw [hs_def]
      exact round_generic radix2 (FLX_exp prec) (Znearest choice) h_ab_in_F
    rw [hs_eq, show a + b - a = b from by ring]
    exact Fb
  · -- Case 1: -a/2 ≤ b. Then a/2 ≤ a + b ≤ 2a, so a/2 ≤ s ≤ 2a, Sterbenz on (s, a).
    have h_lower : a / 2 ≤ a + b := by linarith
    have h_upper_b : b ≤ a := le_trans (le_abs_self b) Hab
    have h_upper : a + b ≤ 2 * a := by linarith
    have hs_lower : a / 2 ≤ s :=
      round_ge_generic radix2 (FLX_exp prec) hValid (Znearest choice) hFa_half h_lower
    have hs_upper : s ≤ 2 * a :=
      round_le_generic radix2 (FLX_exp prec) hValid (Znearest choice) hFa_two h_upper
    have h_s_format : generic_format radix2 (FLX_exp prec) s := by
      rw [hs_def]; exact generic_format_round _ _ hValid _ _
    exact sterbenz radix2 (FLX_exp prec) hValid hMon h_s_format Fa ⟨hs_lower, hs_upper⟩

/-- Step 1 (general): under `|b| ≤ |a|` in radix 2 FLX with round-to-nearest,
the difference `round(a + b) - a` is exactly representable. -/
theorem Fast2Sum_step1
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ |a|) :
    generic_format radix2 (FLX_exp prec)
      (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by
  rcases lt_trichotomy a 0 with Ha_neg | Ha_zero | Ha_pos
  · -- a < 0: use negation symmetry.
    -- Let a' := -a > 0 and b' := -b. Then |b'| ≤ a'.
    -- round(a + b) with Znearest choice = -round(-(a+b)) with flipped choice
    --                                   = -round(a' + b') with flipped choice
    -- So round(a + b) - a = -(round(a' + b') with flipped choice) - a
    --                     = -(round(a' + b') with flipped choice - a').
    -- Apply Fast2Sum_step1_pos to the negated picture, then use opp closure.
    set choice' : ℤ → Bool := fun t => !choice (-(t + 1)) with hchoice'_def
    have Fa' : generic_format radix2 (FLX_exp prec) (-a) :=
      generic_format_opp radix2 (FLX_exp prec) Fa
    have Fb' : generic_format radix2 (FLX_exp prec) (-b) :=
      generic_format_opp radix2 (FLX_exp prec) Fb
    have Hab' : |-b| ≤ -a := by
      rw [abs_neg]
      have h : |a| = -a := abs_of_neg Ha_neg
      rw [← h]; exact Hab
    have h_pos := Fast2Sum_step1_pos prec Hp choice' (by linarith : (0 : ℝ) < -a) Fa' Fb' Hab'
    -- h_pos : round_{choice'}((-a) + (-b)) - (-a) ∈ F
    -- Rewrite: (-a) + (-b) = -(a+b), so round_{choice'}(-(a+b)) - (-a)
    --                                 = round_{choice'}(-(a+b)) + a
    -- And round_{choice'}(-(a+b)) = -round_{choice}(a+b) (by round_N_opp applied "in reverse").
    have h_sum_neg : -a + -b = -(a + b) := by ring
    rw [h_sum_neg] at h_pos
    -- round_N_opp: round (Znearest choice) (-x) = -(round (Znearest choice') x) when
    -- choice' is the flipped one. We want to rewrite round (Znearest choice') (-(a+b))
    -- in terms of round (Znearest choice) (a+b).
    -- round_N_opp says: round (choice) (-x) = -round (flipped choice) x.
    -- Applied with x := a+b: round choice (-(a+b)) = -round choice' (a+b),
    -- so round choice' (a+b) = -round choice (-(a+b)).
    -- We have round choice' (-(a+b)) — apply round_N_opp with choice = choice', x = a+b:
    -- round choice' (-(a+b)) = -round (fun t => !choice' (-(t+1))) (a+b)
    --                        = -round choice (a+b)  -- since !!c = c and -(-(t+1)+1) = t.
    have h_choice_double : (fun t : ℤ => !choice' (-(t + 1))) = choice := by
      funext t
      show (!choice' (-(t + 1))) = choice t
      rw [hchoice'_def]
      show (!(!choice (-(-(t + 1) + 1)))) = choice t
      simp
    rw [round_N_opp radix2 (FLX_exp prec) choice' (a + b), h_choice_double] at h_pos
    -- h_pos : -round choice (a + b) - (-a) ∈ F
    -- i.e. -(round choice (a+b) - a) ∈ F. Apply opp closure to get round choice (a+b) - a ∈ F.
    have h_eq : -round radix2 (FLX_exp prec) (Znearest choice) (a + b) - (-a)
              = -(round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a) := by ring
    rw [h_eq] at h_pos
    have h_target := generic_format_opp radix2 (FLX_exp prec) h_pos
    rw [neg_neg] at h_target
    exact h_target
  · -- a = 0: then |b| ≤ 0 forces b = 0, hence a + b = 0 and the difference is 0.
    have h_b_zero : b = 0 := by
      have h_abs_b_nonneg : 0 ≤ |b| := abs_nonneg b
      have h_abs_b_zero : |b| = 0 := by
        rw [Ha_zero, abs_zero] at Hab
        linarith
      exact abs_eq_zero.mp h_abs_b_zero
    rw [Ha_zero, h_b_zero, add_zero, sub_zero,
      round_0 radix2 (FLX_exp prec) (Znearest choice)]
    exact generic_format_0 _ _
  · -- a > 0: directly apply the positive lemma.
    have hab_pos : |b| ≤ a := by rwa [abs_of_pos Ha_pos] at Hab
    exact Fast2Sum_step1_pos prec Hp choice Ha_pos Fa Fb hab_pos

/-! ### The `plus_error` step -/

/-- Step 2: the residual `b - (round(a+b) - a)` equals `(a+b) - round(a+b)`,
which is the rounding error and is itself representable. -/
theorem Fast2Sum_step2
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b) :
    generic_format radix2 (FLX_exp prec)
      (b - (round radix2 (FLX_exp prec) (Znearest choice) (a + b) - a)) := by
  set s := round radix2 (FLX_exp prec) (Znearest choice) (a + b) with hs_def
  -- b - (s - a) = (a + b) - s = -(s - (a + b)).
  have h_rewrite : b - (s - a) = -(s - (a + b)) := by ring
  rw [h_rewrite]
  apply generic_format_opp
  rw [hs_def]
  exact plus_error radix2 (FLX_exp prec) (FLX_exp_valid prec Hp)
    (FLX_exp_monotone prec) choice Fa Fb

/-! ### Fast2Sum keystone -/

/-- **Fast2Sum correctness** — the error-free transformation.

Given `a, b ∈ F` (radix 2, FLX, round-to-nearest) with `|b| ≤ |a|`, define
  s := round(a + b)
  z := round(s - a)
  e := round(b - z)
Then `z = s - a`, `e = (a + b) - s`, and `a + b = s + e` exactly. -/
theorem Fast2Sum_correct
    (prec : ℤ) (Hp : 0 < prec)
    (choice : ℤ → Bool)
    {a b : ℝ}
    (Fa : generic_format radix2 (FLX_exp prec) a)
    (Fb : generic_format radix2 (FLX_exp prec) b)
    (Hab : |b| ≤ |a|) :
    let s := round radix2 (FLX_exp prec) (Znearest choice) (a + b)
    let z := round radix2 (FLX_exp prec) (Znearest choice) (s - a)
    let e := round radix2 (FLX_exp prec) (Znearest choice) (b - z)
    z = s - a ∧ e = (a + b) - s ∧ a + b = s + e := by
  intro s z e
  -- Step 1: s - a is in format, so z = round(s - a) = s - a.
  have h_step1 : generic_format radix2 (FLX_exp prec) (s - a) :=
    Fast2Sum_step1 prec Hp choice Fa Fb Hab
  have h_z : z = s - a :=
    round_generic radix2 (FLX_exp prec) (Znearest choice) h_step1
  -- Step 2: b - (s - a) is in format (it equals (a+b) - s), so e = b - z = (a+b) - s.
  have h_step2 : generic_format radix2 (FLX_exp prec) (b - (s - a)) :=
    Fast2Sum_step2 prec Hp choice Fa Fb
  have h_e : e = b - z := by
    show round radix2 (FLX_exp prec) (Znearest choice) (b - z) = b - z
    rw [h_z]
    exact round_generic radix2 (FLX_exp prec) (Znearest choice) h_step2
  refine ⟨h_z, ?_, ?_⟩
  · rw [h_e, h_z]; ring
  · rw [h_e, h_z]; ring

end LeanFlocq
