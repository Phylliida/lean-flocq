/-
# Dekker's TwoProduct (error-free transformation for multiplication)

Given floats `x, y`, computes `r = round(x·y)` and an exact error term `e`
with `x · y = r + e`. The FMA-free construction (Dekker) splits each input
into high/low halves via Veltkamp, forms the four sub-products, and
reconstructs the error through a short summation chain.

This file is built incrementally, in chunks:
- **Chunk 1** (here): `generic_format_FLX_mult` — the product of a `p1`-digit
  and a `p2`-digit value is exact at precision `p1 + p2`. This makes three
  of the four Veltkamp sub-products exact unconditionally, and the fourth
  (`tx · ty`) exact when `prec` is even.

Reference: Pff `Pff2Flocq.v` `Dekker` section (682–976), `Pff.v`
`Dekker_aux`/`DekkerN` (17677–17910).
-/
import LeanFlocq.Algorithms.Veltkamp

namespace LeanFlocq

/-- **Product of low-precision values is exact.**

If `x` is representable with `p1` significant digits and `y` with `p2`, and
`p1 + p2 ≤ prec`, then `x · y` is representable with `prec` digits — the
rounding of the product is exact.

This is the core fact behind Dekker's TwoProduct: each sub-product of the
Veltkamp half-splits fits in the working precision.

Proof: write `x = Mx · β^cx`, `y = My · β^cy` canonically, so
`x · y = (Mx · My) · β^(cx+cy)`. Since `mag(x·y) ≤ mag(x) + mag(y)` and
`cexp = mag − prec`, we get `cexp(x·y) ≤ (mag x − p1) + (mag y − p2) +
(p1 + p2 − prec) ≤ cx + cy`, which is exactly the hypothesis of
`generic_format_F2R`. -/
theorem generic_format_FLX_mult (beta : radix) (p1 p2 prec : ℤ)
    (h_budget : p1 + p2 ≤ prec)
    {x y : ℝ}
    (Fx : generic_format beta (FLX_exp p1) x)
    (Fy : generic_format beta (FLX_exp p2) y) :
    generic_format beta (FLX_exp prec) (x * y) := by
  by_cases hxy : x * y = 0
  · rw [hxy]; exact generic_format_0 _ _
  have hx0 : x ≠ 0 := fun h => hxy (by rw [h, zero_mul])
  have hy0 : y ≠ 0 := fun h => hxy (by rw [h, mul_zero])
  -- Canonical exponents and mantissas.
  set cx := cexp beta (FLX_exp p1) x with hcx_def
  set cy := cexp beta (FLX_exp p2) y with hcy_def
  set Mx := Ztrunc (scaled_mantissa beta (FLX_exp p1) x) with hMx_def
  set My := Ztrunc (scaled_mantissa beta (FLX_exp p2) y) with hMy_def
  have hx_eq : x = (Mx : ℝ) * bpow beta cx := Fx
  have hy_eq : y = (My : ℝ) * bpow beta cy := Fy
  -- Product as a single F2R at exponent cx + cy.
  have hxy_F2R : x * y = F2R (beta := beta) ⟨Mx * My, cx + cy⟩ := by
    show x * y = ((Mx * My : ℤ) : ℝ) * bpow beta (cx + cy)
    rw [hx_eq, hy_eq, bpow_plus]; push_cast; ring
  -- cexp as mag − prec for each.
  have hcx_eq : cx = mag beta x - p1 := by rw [hcx_def]; unfold cexp FLX_exp; rfl
  have hcy_eq : cy = mag beta y - p2 := by rw [hcy_def]; unfold cexp FLX_exp; rfl
  -- mag(x·y) ≤ mag(x) + mag(y).
  have h_mag_le : mag beta (x * y) ≤ mag beta x + mag beta y :=
    (mag_mult beta hx0 hy0).2
  -- cexp_prec(x·y) ≤ cx + cy.
  have h_cexp_le : cexp beta (FLX_exp prec) (x * y) ≤ cx + cy := by
    have : cexp beta (FLX_exp prec) (x * y) = mag beta (x * y) - prec := by
      unfold cexp FLX_exp; rfl
    rw [this, hcx_eq, hcy_eq]; omega
  -- Conclude via generic_format_F2R.
  rw [hxy_F2R]
  apply generic_format_F2R
  intro _
  rw [← hxy_F2R]
  exact h_cexp_le

/-! ## Chunk 3: general-sign Veltkamp split

`Veltkamp_tail_FLX` and `Veltkamp_hx_format_FLX` are proved for `0 < x`. For
TwoProduct we need the split for arbitrary inputs (any sign, and zero).

The reduction is via `round_N_opp`: rounding-to-nearest of `−v` equals the
negation of rounding `v` under the *flipped* tie-breaker
`flip c := fun t => !c(−(t+1))`. Hence each Veltkamp step on `−x` (with
choice `c`) equals the negation of the same step on `x` (with choice
`flip c`). Below, four step-commutation lemmas, then the bundled theorem. -/

/-- Step 1 commutes with negation (flipping the tie-breaker). -/
private theorem Veltkamp_p_FLX_neg (beta : radix) (prec : ℤ)
    (c : ℤ → Bool) (s : ℤ) (x : ℝ) :
    Veltkamp_p_FLX beta prec c s (-x)
      = -Veltkamp_p_FLX beta prec (fun t => !c (-(t+1))) s x := by
  unfold Veltkamp_p_FLX
  rw [neg_mul, round_N_opp]

/-- Step 2 commutes with negation. -/
private theorem Veltkamp_q_FLX_neg (beta : radix) (prec : ℤ)
    (c : ℤ → Bool) (s : ℤ) (x : ℝ) :
    Veltkamp_q_FLX beta prec c s (-x)
      = -Veltkamp_q_FLX beta prec (fun t => !c (-(t+1))) s x := by
  unfold Veltkamp_q_FLX
  rw [Veltkamp_p_FLX_neg,
    show (-x) - -Veltkamp_p_FLX beta prec (fun t => !c (-(t+1))) s x
        = -(x - Veltkamp_p_FLX beta prec (fun t => !c (-(t+1))) s x) from by ring,
    round_N_opp]

/-- Step 3 commutes with negation. -/
private theorem Veltkamp_hx_FLX_neg (beta : radix) (prec : ℤ)
    (c : ℤ → Bool) (s : ℤ) (x : ℝ) :
    Veltkamp_hx_FLX beta prec c s (-x)
      = -Veltkamp_hx_FLX beta prec (fun t => !c (-(t+1))) s x := by
  unfold Veltkamp_hx_FLX
  rw [Veltkamp_q_FLX_neg, Veltkamp_p_FLX_neg,
    show -Veltkamp_q_FLX beta prec (fun t => !c (-(t+1))) s x
          + -Veltkamp_p_FLX beta prec (fun t => !c (-(t+1))) s x
        = -(Veltkamp_q_FLX beta prec (fun t => !c (-(t+1))) s x
            + Veltkamp_p_FLX beta prec (fun t => !c (-(t+1))) s x) from by ring,
    round_N_opp]

/-- Step 4 commutes with negation. -/
private theorem Veltkamp_tx_FLX_neg (beta : radix) (prec : ℤ)
    (c : ℤ → Bool) (s : ℤ) (x : ℝ) :
    Veltkamp_tx_FLX beta prec c s (-x)
      = -Veltkamp_tx_FLX beta prec (fun t => !c (-(t+1))) s x := by
  unfold Veltkamp_tx_FLX
  rw [Veltkamp_hx_FLX_neg,
    show (-x) - -Veltkamp_hx_FLX beta prec (fun t => !c (-(t+1))) s x
        = -(x - Veltkamp_hx_FLX beta prec (fun t => !c (-(t+1))) s x) from by ring,
    round_N_opp]

/-- **Veltkamp split at FLX, all signs.** For arbitrary `x` in `F(FLX, prec)`
and `2 ≤ s ≤ prec − 2`, the algorithm outputs satisfy `x = hx + tx` exactly,
with `tx ∈ F(s)` and `hx ∈ F(prec − s)`. This bundles `Veltkamp_tail_FLX` and
`Veltkamp_hx_format_FLX` and removes the positivity restriction, so TwoProduct
can split arbitrary inputs. -/
theorem Veltkamp_split_FLX_general (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    x = Veltkamp_hx_FLX beta prec choice s x + Veltkamp_tx_FLX beta prec choice s x
    ∧ generic_format beta (FLX_exp s) (Veltkamp_tx_FLX beta prec choice s x)
    ∧ generic_format beta (FLX_exp (prec - s))
        (Veltkamp_hx_FLX beta prec choice s x) := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · -- x < 0: reduce to -x > 0 with the flipped tie-breaker.
    have hx'_pos : 0 < -x := by linarith
    have Fx' : generic_format beta (FLX_exp prec) (-x) :=
      generic_format_opp beta _ Fx
    obtain ⟨h_sum', h_tx'⟩ :=
      Veltkamp_tail_FLX beta prec hp (fun t => !choice (-(t+1))) Fx' hx'_pos hs_lo hs_hi
    have h_hx' :=
      Veltkamp_hx_format_FLX beta prec hp (fun t => !choice (-(t+1))) Fx' hx'_pos hs_lo hs_hi
    -- Commutation: each output on x equals the negation of the output on -x.
    have e_hx : Veltkamp_hx_FLX beta prec choice s x
        = -Veltkamp_hx_FLX beta prec (fun t => !choice (-(t+1))) s (-x) := by
      have h := Veltkamp_hx_FLX_neg beta prec choice s (-x); rwa [neg_neg] at h
    have e_tx : Veltkamp_tx_FLX beta prec choice s x
        = -Veltkamp_tx_FLX beta prec (fun t => !choice (-(t+1))) s (-x) := by
      have h := Veltkamp_tx_FLX_neg beta prec choice s (-x); rwa [neg_neg] at h
    refine ⟨?_, ?_, ?_⟩
    · rw [e_hx, e_tx]; linarith [h_sum']
    · rw [e_tx]; exact generic_format_opp beta _ h_tx'
    · rw [e_hx]; exact generic_format_opp beta _ h_hx'
  · -- x = 0: every output is 0.
    subst hzero
    have hp0 : Veltkamp_p_FLX beta prec choice s 0 = 0 := by
      unfold Veltkamp_p_FLX; rw [zero_mul, round_0]
    have hq0 : Veltkamp_q_FLX beta prec choice s 0 = 0 := by
      unfold Veltkamp_q_FLX; rw [hp0, sub_zero, round_0]
    have hhx0 : Veltkamp_hx_FLX beta prec choice s 0 = 0 := by
      unfold Veltkamp_hx_FLX; rw [hp0, hq0, add_zero, round_0]
    have htx0 : Veltkamp_tx_FLX beta prec choice s 0 = 0 := by
      unfold Veltkamp_tx_FLX; rw [hhx0, sub_zero, round_0]
    rw [hhx0, htx0]
    exact ⟨by ring, generic_format_0 _ _, generic_format_0 _ _⟩
  · -- x > 0: the existing positive theorems.
    obtain ⟨h_sum, h_tx⟩ := Veltkamp_tail_FLX beta prec hp choice Fx hpos hs_lo hs_hi
    exact ⟨h_sum, h_tx,
      Veltkamp_hx_format_FLX beta prec hp choice Fx hpos hs_lo hs_hi⟩

/-! ## Chunk 4: summation spine

The reconstruction `t1..t4` of the product error. The engine for the two
middle steps is a single "grid + magnitude ⟹ representable" lemma. -/

/-- **Grid lemma.** A value `v = M · β^E` that fits in magnitude under
`β^(prec+E)` is representable at precision `prec`. This is the workhorse for
proving each summation step rounds exactly: every partial sum lives on a
common grid `β^E`, and being small enough forces `cexp(v) ≤ E`. -/
theorem generic_format_FLX_of_mult_bpow (beta : radix) (prec : ℤ)
    (M E : ℤ) {v : ℝ} (hv : v = (M : ℝ) * bpow beta E)
    (hbound : |v| < bpow beta (prec + E)) :
    generic_format beta (FLX_exp prec) v := by
  by_cases hM : M = 0
  · rw [hv, hM]; push_cast; rw [zero_mul]; exact generic_format_0 _ _
  have hvF2R : v = F2R (beta := beta) ⟨M, E⟩ := hv
  have hvne : v ≠ 0 := by
    rw [hv]; exact mul_ne_zero (by exact_mod_cast hM) (ne_of_gt (bpow_gt_0 beta E))
  have h_mag : mag beta v ≤ prec + E := mag_le_bpow beta hvne hbound
  rw [hvF2R]
  apply generic_format_F2R
  intro _
  rw [← hvF2R]
  show cexp beta (FLX_exp prec) v ≤ E
  have : cexp beta (FLX_exp prec) v = mag beta v - prec := by unfold cexp FLX_exp; rfl
  rw [this]; omega

/-- **Structural decomposition, all nonzero signs.** Lifts `Veltkamp_struct_FLX`
to arbitrary nonzero `x`: gives integer mantissas `M_x`, `M_h` with
`x = M_x·β^cx`, `hx = M_h·β^(s+cx)`, `|M_h| ≤ β^(prec−s)`, and the tail bound
`|M_x − M_h·β^s| ≤ β^s/2`. Negative `x` negates both mantissas (via the Chunk-3
commutation `Veltkamp_hx_FLX_neg` and `cexp_opp`). -/
theorem Veltkamp_struct_FLX_general (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hx_ne : x ≠ 0) (hs_lo : 2 ≤ s) (hs_hi : s + 2 ≤ prec) :
    ∃ M_x M_h : ℤ,
      x = (M_x : ℝ) * bpow beta (cexp beta (FLX_exp prec) x) ∧
      Veltkamp_hx_FLX beta prec choice s x
        = (M_h : ℝ) * bpow beta (s + cexp beta (FLX_exp prec) x) ∧
      (|M_h| : ℝ) ≤ bpow beta (prec - s) ∧
      |(M_x : ℝ) - (M_h : ℝ) * bpow beta s| ≤ bpow beta s / 2 := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · -- x < 0: reduce to -x > 0 with flipped tie-breaker; negate both mantissas.
    have hx'_pos : 0 < -x := by linarith
    have Fx' : generic_format beta (FLX_exp prec) (-x) := generic_format_opp beta _ Fx
    obtain ⟨M_x', M_h', hx'_form, hhx'_form, hMh'_bound, hclose'⟩ :=
      Veltkamp_struct_FLX beta prec hp (fun t => !choice (-(t+1))) Fx' hx'_pos hs_lo hs_hi
    have hcexp : cexp beta (FLX_exp prec) (-x) = cexp beta (FLX_exp prec) x :=
      cexp_opp beta _ x
    have e_hx : Veltkamp_hx_FLX beta prec choice s x
        = -Veltkamp_hx_FLX beta prec (fun t => !choice (-(t+1))) s (-x) := by
      have h := Veltkamp_hx_FLX_neg beta prec choice s (-x); rwa [neg_neg] at h
    rw [hcexp] at hx'_form hhx'_form
    refine ⟨-M_x', -M_h', ?_, ?_, ?_, ?_⟩
    · push_cast; linear_combination -hx'_form
    · rw [e_hx, hhx'_form]; push_cast; ring
    · simpa using hMh'_bound
    · have h_rw : ((-M_x' : ℤ) : ℝ) - ((-M_h' : ℤ) : ℝ) * bpow beta s
          = -(((M_x' : ℤ) : ℝ) - ((M_h' : ℤ) : ℝ) * bpow beta s) := by push_cast; ring
      rw [h_rw, abs_neg]; exact hclose'
  · exact absurd hzero hx_ne
  · -- x > 0: directly.
    exact Veltkamp_struct_FLX beta prec hp choice Fx hpos hs_lo hs_hi

end LeanFlocq
