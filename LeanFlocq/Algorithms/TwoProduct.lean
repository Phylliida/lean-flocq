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

/-- With `2s = prec`, the product of two `F(s)` values rounds exactly. This
covers all four Veltkamp sub-products uniformly in the even-precision case:
each half-part lies in `F(s)`, and `F(s)·F(s) ⊆ F(2s) = F(prec)`. -/
theorem round_mul_Fs_exact (beta : radix) (prec : ℤ) (choice : ℤ → Bool)
    {s : ℤ} {a b : ℝ} (hs : 2 * s = prec)
    (Fa : generic_format beta (FLX_exp s) a)
    (Fb : generic_format beta (FLX_exp s) b) :
    round beta (FLX_exp prec) (Znearest choice) (a * b) = a * b :=
  round_generic beta (FLX_exp prec) (Znearest choice)
    (generic_format_FLX_mult beta s s prec (by omega) Fa Fb)

/-- **Grid step.** If `u = Mu·β^E` and `w = Mw·β^E` both lie on the grid `β^E`
and their sum fits under `β^(prec+E)`, then `round(u+w) = u+w`. Each step of the
Dekker summation chain is an instance: the running partial sum and the next
sub-product share a common grid, and the sum stays small enough. -/
theorem round_add_grid_exact (beta : radix) (prec : ℤ) (choice : ℤ → Bool)
    (E Mu Mw : ℤ) {u w : ℝ}
    (hu : u = (Mu : ℝ) * bpow beta E) (hw : w = (Mw : ℝ) * bpow beta E)
    (hb : |u + w| < bpow beta (prec + E)) :
    round beta (FLX_exp prec) (Znearest choice) (u + w) = u + w :=
  round_generic beta (FLX_exp prec) (Znearest choice)
    (generic_format_FLX_of_mult_bpow beta prec (Mu + Mw) E
      (by rw [hu, hw]; push_cast; ring) hb)

/-- **Expansion + sub-product exactness.** For `2s = prec`, splitting `x` and
`y` by Veltkamp gives the exact bilinear expansion
`x·y = hx·hy + hx·ty + tx·hy + tx·ty`, and each of the four sub-products rounds
exactly (each factor is in `F(s)`, so each product is in `F(2s) = F(prec)`).
This is the algebraic bedrock of the Dekker summation chain. -/
theorem twoproduct_expand_exact (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y)
    (hs : 2 * s = prec) (hs_lo : 2 ≤ s) :
    x * y
      = Veltkamp_hx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y
      + Veltkamp_hx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y
      + Veltkamp_tx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y
      + Veltkamp_tx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y
    ∧ round beta (FLX_exp prec) (Znearest choice)
        (Veltkamp_hx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y)
        = Veltkamp_hx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y
    ∧ round beta (FLX_exp prec) (Znearest choice)
        (Veltkamp_hx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y)
        = Veltkamp_hx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y
    ∧ round beta (FLX_exp prec) (Znearest choice)
        (Veltkamp_tx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y)
        = Veltkamp_tx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y
    ∧ round beta (FLX_exp prec) (Znearest choice)
        (Veltkamp_tx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y)
        = Veltkamp_tx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y := by
  have hs_hi : s + 2 ≤ prec := by omega
  set hx := Veltkamp_hx_FLX beta prec choice s x with hhx_def
  set tx := Veltkamp_tx_FLX beta prec choice s x with htx_def
  set hy := Veltkamp_hx_FLX beta prec choice s y with hhy_def
  set ty := Veltkamp_tx_FLX beta prec choice s y with hty_def
  obtain ⟨hsplit_x, Ftx, Fhx⟩ :=
    Veltkamp_split_FLX_general beta prec hp choice Fx hs_lo hs_hi
  obtain ⟨hsplit_y, Fty, Fhy⟩ :=
    Veltkamp_split_FLX_general beta prec hp choice Fy hs_lo hs_hi
  rw [show prec - s = s from by omega] at Fhx Fhy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (hy + ty) * hsplit_x + x * hsplit_y
  · exact round_mul_Fs_exact beta prec choice hs Fhx Fhy
  · exact round_mul_Fs_exact beta prec choice hs Fhx Fty
  · exact round_mul_Fs_exact beta prec choice hs Ftx Fhy
  · exact round_mul_Fs_exact beta prec choice hs Ftx Fty

/-! ### Magnitude bookkeeping helpers -/

/-- **Grid coarsening.** A value `M·β^E_big` on a fine exponent equals an integer
multiple of the coarser `β^E_small` (when `E_small ≤ E_big`): the integer is
`M · β^(E_big − E_small)`. Centralizes the `toNat`/`IZR_Zpower` bookkeeping that
every summation step needs to put its summands on a common grid. -/
theorem bpow_coarsen (beta : radix) (M : ℤ) (E_small E_big : ℤ)
    (h : E_small ≤ E_big) :
    (M : ℝ) * bpow beta E_big
      = ((M * beta.val ^ (E_big - E_small).toNat : ℤ) : ℝ) * bpow beta E_small := by
  have hd : 0 ≤ E_big - E_small := by omega
  have hsplit : bpow beta E_big = bpow beta (E_big - E_small) * bpow beta E_small := by
    rw [← bpow_plus]; congr 1; omega
  rw [hsplit, ← IZR_Zpower beta hd]
  push_cast; ring

/-- **Product magnitude bound.** If `|Ma| ≤ Ca` and `|Mb| ≤ Cb` (with `Ca ≥ 0`),
the product `(Ma·β^Ea)·(Mb·β^Eb)` is bounded by `(Ca·Cb)·β^(Ea+Eb)`. The driver
behind each sub-product magnitude estimate. -/
theorem abs_prod_bpow_le (beta : radix) (Ma Mb : ℝ) (Ea Eb : ℤ) (Ca Cb : ℝ)
    (hCa : 0 ≤ Ca) (ha : |Ma| ≤ Ca) (hb : |Mb| ≤ Cb) :
    |(Ma * bpow beta Ea) * (Mb * bpow beta Eb)| ≤ (Ca * Cb) * bpow beta (Ea + Eb) := by
  have hbpowa : 0 < bpow beta Ea := bpow_gt_0 _ _
  have hbpowb : 0 < bpow beta Eb := bpow_gt_0 _ _
  calc |(Ma * bpow beta Ea) * (Mb * bpow beta Eb)|
      = |Ma * Mb| * (bpow beta Ea * bpow beta Eb) := by
        rw [show (Ma * bpow beta Ea) * (Mb * bpow beta Eb)
              = (Ma * Mb) * (bpow beta Ea * bpow beta Eb) from by ring,
          abs_mul, abs_of_pos (mul_pos hbpowa hbpowb)]
    _ ≤ (Ca * Cb) * (bpow beta Ea * bpow beta Eb) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (mul_pos hbpowa hbpowb))
        calc |Ma * Mb| = |Ma| * |Mb| := abs_mul _ _
          _ ≤ Ca * Cb := mul_le_mul ha hb (abs_nonneg _) hCa
    _ = (Ca * Cb) * bpow beta (Ea + Eb) := by rw [bpow_plus]

/-- **Medium sub-product bound.** A product of a full half-part (`|·| ≤ β^s`) and
a tail half-part (`|·| ≤ β^s/2`), whose exponents sum to `s + E0`, is bounded by
`½·β^(prec+s+E0)`. Covers `hx·ty` and `tx·hy` (after `2s = prec`). -/
theorem prod_bound_medium (beta : radix) (prec s : ℤ) (hs : 2 * s = prec)
    (Ma Mb : ℝ) (Ea Eb E0 : ℤ) (hE : Ea + Eb = s + E0)
    (ha : |Ma| ≤ bpow beta s) (hb : |Mb| ≤ bpow beta s / 2) :
    |(Ma * bpow beta Ea) * (Mb * bpow beta Eb)| ≤ bpow beta (prec + (s + E0)) / 2 := by
  refine le_trans (abs_prod_bpow_le beta Ma Mb Ea Eb (bpow beta s) (bpow beta s / 2)
    (le_of_lt (bpow_gt_0 _ _)) ha hb) (le_of_eq ?_)
  rw [hE]
  have hbp : bpow beta s * bpow beta s = bpow beta prec := by rw [← bpow_plus]; congr 1; omega
  have hrw : (bpow beta s * (bpow beta s / 2)) * bpow beta (s + E0)
      = (bpow beta s * bpow beta s) * bpow beta (s + E0) / 2 := by ring
  rw [hrw, hbp, ← bpow_plus]

/-- **Small sub-product bound.** A product of two tail half-parts (each `|·| ≤
β^s/2`), exponents summing to `E0`, is bounded by `¼·β^(prec+E0)`. Covers
`tx·ty`. -/
theorem prod_bound_small (beta : radix) (prec s : ℤ) (hs : 2 * s = prec)
    (Ma Mb : ℝ) (Ea Eb E0 : ℤ) (hE : Ea + Eb = E0)
    (ha : |Ma| ≤ bpow beta s / 2) (hb : |Mb| ≤ bpow beta s / 2) :
    |(Ma * bpow beta Ea) * (Mb * bpow beta Eb)| ≤ bpow beta (prec + E0) / 4 := by
  refine le_trans (abs_prod_bpow_le beta Ma Mb Ea Eb (bpow beta s / 2) (bpow beta s / 2)
    (le_of_lt (half_pos (bpow_gt_0 _ _))) ha hb) (le_of_eq ?_)
  rw [hE]
  have hbp : bpow beta s * bpow beta s = bpow beta prec := by rw [← bpow_plus]; congr 1; omega
  have hrw : (bpow beta s / 2 * (bpow beta s / 2)) * bpow beta E0
      = (bpow beta s * bpow beta s) * bpow beta E0 / 4 := by ring
  rw [hrw, hbp, ← bpow_plus]

private theorem abs_sub1_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [show a - b = a + (-b) from by ring]
  exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))

private theorem abs_sub2_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h2 : |a - b - c| ≤ |a - b| + |c| := by
    rw [show a - b - c = (a - b) + (-c) from by ring]
    exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
  linarith [abs_sub1_le a b]

private theorem abs_sub3_le (a b c d : ℝ) : |a - b - c - d| ≤ |a| + |b| + |c| + |d| := by
  have h3 : |a - b - c - d| ≤ |a - b - c| + |d| := by
    rw [show a - b - c - d = (a - b - c) + (-d) from by ring]
    exact le_trans (abs_add_le _ _) (le_of_eq (by rw [abs_neg]))
  linarith [abs_sub2_le a b c]

/-- The Veltkamp parts of `0` are `0` (every rounding step collapses). -/
private theorem Veltkamp_parts_zero (beta : radix) (prec : ℤ) (c : ℤ → Bool) (s : ℤ) :
    Veltkamp_hx_FLX beta prec c s 0 = 0 ∧ Veltkamp_tx_FLX beta prec c s 0 = 0 := by
  have hp0 : Veltkamp_p_FLX beta prec c s 0 = 0 := by
    unfold Veltkamp_p_FLX; rw [zero_mul, round_0]
  have hq0 : Veltkamp_q_FLX beta prec c s 0 = 0 := by
    unfold Veltkamp_q_FLX; rw [hp0, sub_zero, round_0]
  have hhx0 : Veltkamp_hx_FLX beta prec c s 0 = 0 := by
    unfold Veltkamp_hx_FLX; rw [hp0, hq0, add_zero, round_0]
  exact ⟨hhx0, by unfold Veltkamp_tx_FLX; rw [hhx0, sub_zero, round_0]⟩

/-- **Dekker TwoProduct, even precision, nonzero inputs.** For `x, y ≠ 0` in
`F(FLX, prec)` with `2s = prec`, the four-step Dekker error chain reconstructs
the rounding error exactly: `x·y = round(x·y) + t4`, where each summation step
rounds exactly (the partial sums live on common grids small enough to be
representable). -/
private theorem TwoProduct_FLX_main (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y)
    (hs : 2 * s = prec) (hs_lo : 2 ≤ s) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    x * y
      = round beta (FLX_exp prec) (Znearest choice) (x * y)
      + round beta (FLX_exp prec) (Znearest choice)
          (round beta (FLX_exp prec) (Znearest choice)
            (round beta (FLX_exp prec) (Znearest choice)
              (round beta (FLX_exp prec) (Znearest choice)
                  (Veltkamp_hx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y
                    - round beta (FLX_exp prec) (Znearest choice) (x * y))
                + Veltkamp_hx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y)
              + Veltkamp_tx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y)
            + Veltkamp_tx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y) := by
  have hs_hi : s + 2 ≤ prec := by omega
  have hxy_ne : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hβ2 : (2 : ℝ) ≤ (beta.val : ℝ) := by exact_mod_cast beta.prop
  -- Structural decompositions and the bilinear expansion, before abbreviating.
  obtain ⟨M_x, M_hx, hx_form, hhx_form, hMhx_bd, hclose_x⟩ :=
    Veltkamp_struct_FLX_general beta prec hp choice Fx hx0 hs_lo hs_hi
  obtain ⟨M_y, M_hy, hy_form, hhy_form, hMhy_bd, hclose_y⟩ :=
    Veltkamp_struct_FLX_general beta prec hp choice Fy hy0 hs_lo hs_hi
  obtain ⟨hsplit_x, _, _⟩ := Veltkamp_split_FLX_general beta prec hp choice Fx hs_lo hs_hi
  obtain ⟨hsplit_y, _, _⟩ := Veltkamp_split_FLX_general beta prec hp choice Fy hs_lo hs_hi
  obtain ⟨hexp, _, _, _, _⟩ := twoproduct_expand_exact beta prec hp choice Fx Fy hs hs_lo
  set cx := cexp beta (FLX_exp prec) x with hcx_def
  set cy := cexp beta (FLX_exp prec) y with hcy_def
  set cr := cexp beta (FLX_exp prec) (x * y) with hcr_def
  set hx := Veltkamp_hx_FLX beta prec choice s x with hhx_def
  set tx := Veltkamp_tx_FLX beta prec choice s x with htx_def
  set hy := Veltkamp_hx_FLX beta prec choice s y with hhy_def
  set ty := Veltkamp_tx_FLX beta prec choice s y with hty_def
  set r := round beta (FLX_exp prec) (Znearest choice) (x * y) with hr_def
  -- Mantissa bounds in usable real form.
  rw [show prec - s = s from by omega] at hMhx_bd hMhy_bd
  -- tx, ty as (real mantissa)·β^c.
  have htx_form : tx = ((M_x : ℝ) - (M_hx : ℝ) * bpow beta s) * bpow beta cx := by
    have htxv : tx = x - hx := by linarith [hsplit_x]
    rw [htxv, hx_form, hhx_form, bpow_plus]; ring
  have hty_form : ty = ((M_y : ℝ) - (M_hy : ℝ) * bpow beta s) * bpow beta cy := by
    have htyv : ty = y - hy := by linarith [hsplit_y]
    rw [htyv, hy_form, hhy_form, bpow_plus]; ring
  -- cexp = mag − prec.
  have hcx_mag : cx = mag beta x - prec := by rw [hcx_def]; unfold cexp FLX_exp; rfl
  have hcy_mag : cy = mag beta y - prec := by rw [hcy_def]; unfold cexp FLX_exp; rfl
  have hcr_mag : cr = mag beta (x * y) - prec := by rw [hcr_def]; unfold cexp FLX_exp; rfl
  obtain ⟨hmag_lo, hmag_hi⟩ := mag_mult beta hx0 hy0
  have hcr_lo : prec + (cx + cy) - 1 ≤ cr := by rw [hcr_mag, hcx_mag, hcy_mag]; omega
  have hcr_hi : cr ≤ prec + (cx + cy) := by rw [hcr_mag, hcx_mag, hcy_mag]; omega
  -- r on the coarse grid cr.
  have hr_eq : r = ((Ztrunc (scaled_mantissa beta (FLX_exp prec) r) : ℤ) : ℝ)
      * bpow beta (cexp beta (FLX_exp prec) r) :=
    generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) (x * y)
  obtain ⟨M_r, hr_grid_eq⟩ : ∃ M_r : ℤ, r = (M_r : ℝ) * bpow beta cr := by
    by_cases hr0 : r = 0
    · exact ⟨0, by rw [hr0]; push_cast; ring⟩
    · have hcr_le : cr ≤ cexp beta (FLX_exp prec) r := by
        rw [hcr_def]
        exact cexp_round_ge beta (FLX_exp prec) (FLX_exp_valid prec hp)
          (FLX_exp_monotone prec) (Znearest choice) hr0
      exact ⟨Ztrunc (scaled_mantissa beta (FLX_exp prec) r)
          * beta.val ^ (cexp beta (FLX_exp prec) r - cr).toNat,
        by conv_lhs => rw [hr_eq]
           exact bpow_coarsen beta _ cr (cexp beta (FLX_exp prec) r) hcr_le⟩
  -- Integer mantissa casts for the tail parts.
  have hcast_s : ((beta.val ^ s.toNat : ℤ) : ℝ) = bpow beta s :=
    IZR_Zpower beta (by omega)
  have hM_ty_cast : ((M_y - M_hy * beta.val ^ s.toNat : ℤ) : ℝ)
      = (M_y : ℝ) - (M_hy : ℝ) * bpow beta s := by
    rw [Int.cast_sub, Int.cast_mul, hcast_s]
  have hM_tx_cast : ((M_x - M_hx * beta.val ^ s.toNat : ℤ) : ℝ)
      = (M_x : ℝ) - (M_hx : ℝ) * bpow beta s := by
    rw [Int.cast_sub, Int.cast_mul, hcast_s]
  -- Grid representations of the four sub-products.
  have hphh_grid : hx * hy = ((M_hx * M_hy : ℤ) : ℝ) * bpow beta (prec + (cx + cy)) := by
    rw [hhx_form, hhy_form,
      show bpow beta (prec + (cx + cy)) = bpow beta (s + cx) * bpow beta (s + cy) from by
        rw [← bpow_plus]; congr 1; omega]
    push_cast; ring
  have hpht_grid : hx * ty
      = ((M_hx * (M_y - M_hy * beta.val ^ s.toNat) : ℤ) : ℝ) * bpow beta (s + (cx + cy)) := by
    rw [hhx_form, hty_form,
      show bpow beta (s + (cx + cy)) = bpow beta (s + cx) * bpow beta cy from by
        rw [← bpow_plus]; congr 1; omega, ← hM_ty_cast]
    push_cast; ring
  have hpth_grid : tx * hy
      = (((M_x - M_hx * beta.val ^ s.toNat) * M_hy : ℤ) : ℝ) * bpow beta (s + (cx + cy)) := by
    rw [htx_form, hhy_form,
      show bpow beta (s + (cx + cy)) = bpow beta cx * bpow beta (s + cy) from by
        rw [← bpow_plus]; congr 1; omega, ← hM_tx_cast]
    push_cast; ring
  -- phh coarsened to the cr grid and the s+(cx+cy) grid; r to the s+(cx+cy) grid.
  have hphh_at_cr : hx * hy
      = ((M_hx * M_hy * beta.val ^ (prec + (cx + cy) - cr).toNat : ℤ) : ℝ) * bpow beta cr := by
    rw [hphh_grid]; exact bpow_coarsen beta (M_hx * M_hy) cr (prec + (cx + cy)) hcr_hi
  have hphh_at_g : hx * hy
      = ((M_hx * M_hy * beta.val ^ s.toNat : ℤ) : ℝ) * bpow beta (s + (cx + cy)) := by
    rw [hphh_grid,
      show bpow beta (prec + (cx + cy)) = bpow beta s * bpow beta (s + (cx + cy)) from by
        rw [← bpow_plus]; congr 1; omega, ← hcast_s]
    push_cast; ring
  have hr_at_g : r
      = ((M_r * beta.val ^ (cr - (s + (cx + cy))).toNat : ℤ) : ℝ) * bpow beta (s + (cx + cy)) := by
    rw [hr_grid_eq]; exact bpow_coarsen beta M_r (s + (cx + cy)) cr (by omega)
  have hu2 : hx * hy - r
      = ((M_hx * M_hy * beta.val ^ s.toNat
            - M_r * beta.val ^ (cr - (s + (cx + cy))).toNat : ℤ) : ℝ)
        * bpow beta (s + (cx + cy)) := by
    rw [hphh_at_g, hr_at_g]; push_cast; ring
  have hu3 : (hx * hy - r) + hx * ty
      = ((M_hx * M_hy * beta.val ^ s.toNat
            - M_r * beta.val ^ (cr - (s + (cx + cy))).toNat
            + M_hx * (M_y - M_hy * beta.val ^ s.toNat) : ℤ) : ℝ)
        * bpow beta (s + (cx + cy)) := by
    rw [hu2, hpht_grid]; push_cast; ring
  -- Scale abbreviations and the monotonicity facts they satisfy.
  have hC2_pos : 0 < bpow beta (prec + (cx + cy)) := bpow_gt_0 _ _
  have hC_pos : 0 < bpow beta (prec + (s + (cx + cy))) := bpow_gt_0 _ _
  have hD_pos : 0 < bpow beta (2 * prec - 2 + (cx + cy)) := bpow_gt_0 _ _
  have hcr_C2 : bpow beta cr ≤ bpow beta (prec + (cx + cy)) := bpow_le beta (by omega)
  have hcr_D : bpow beta cr ≤ bpow beta (2 * prec - 2 + (cx + cy)) := bpow_le beta (by omega)
  have hC_D : bpow beta (prec + (s + (cx + cy))) ≤ bpow beta (2 * prec - 2 + (cx + cy)) :=
    bpow_le beta (by omega)
  have hC2_D : bpow beta (prec + (cx + cy)) ≤ bpow beta (2 * prec - 2 + (cx + cy)) :=
    bpow_le beta (by omega)
  have h2C2 : 2 * bpow beta (prec + (cx + cy)) ≤ bpow beta (prec + (s + (cx + cy))) := by
    have hsplit : bpow beta (prec + (s + (cx + cy)))
        = bpow beta s * bpow beta (prec + (cx + cy)) := by rw [← bpow_plus]; congr 1; omega
    have hbs2 : (2 : ℝ) ≤ bpow beta s := by
      calc (2 : ℝ) ≤ (beta.val : ℝ) := hβ2
        _ = bpow beta 1 := (bpow_one beta).symm
        _ ≤ bpow beta s := bpow_le beta (by omega)
    rw [hsplit]; exact mul_le_mul_of_nonneg_right hbs2 (le_of_lt hC2_pos)
  have hthresh1 : 2 * bpow beta (2 * prec - 2 + (cx + cy)) ≤ bpow beta (prec + cr) := by
    have hbge2 : (2 : ℝ) ≤ bpow beta 1 := by rw [bpow_one]; exact hβ2
    calc 2 * bpow beta (2 * prec - 2 + (cx + cy))
        ≤ bpow beta 1 * bpow beta (2 * prec - 2 + (cx + cy)) :=
          mul_le_mul_of_nonneg_right hbge2 (le_of_lt hD_pos)
      _ = bpow beta (1 + (2 * prec - 2 + (cx + cy))) := (bpow_plus beta _ _).symm
      _ ≤ bpow beta (prec + cr) := bpow_le beta (by omega)
  -- The four sub-product magnitude bounds and the rounding-error bound.
  have hb_err : |x * y - r| ≤ bpow beta cr / 2 := by
    have h := error_le_half_ulp beta (FLX_exp prec) (FLX_exp_valid prec hp) choice (x * y)
    rw [ulp_neq_0 beta (FLX_exp prec) hxy_ne, ← hr_def, ← hcr_def] at h
    rw [abs_sub_comm]; linarith [h]
  have hb_pht : |hx * ty| ≤ bpow beta (prec + (s + (cx + cy))) / 2 := by
    rw [hhx_form, hty_form]
    exact prod_bound_medium beta prec s hs (M_hx : ℝ) ((M_y : ℝ) - (M_hy : ℝ) * bpow beta s)
      (s + cx) cy (cx + cy) (by ring) hMhx_bd hclose_y
  have hb_pth : |tx * hy| ≤ bpow beta (prec + (s + (cx + cy))) / 2 := by
    rw [show tx * hy = hy * tx from mul_comm _ _, hhy_form, htx_form]
    exact prod_bound_medium beta prec s hs (M_hy : ℝ) ((M_x : ℝ) - (M_hx : ℝ) * bpow beta s)
      (s + cy) cx (cx + cy) (by ring) hMhy_bd hclose_x
  have hb_ptt : |tx * ty| ≤ bpow beta (prec + (cx + cy)) / 4 := by
    rw [htx_form, hty_form]
    exact prod_bound_small beta prec s hs ((M_x : ℝ) - (M_hx : ℝ) * bpow beta s)
      ((M_y : ℝ) - (M_hy : ℝ) * bpow beta s) cx cy (cx + cy) (by ring) hclose_x hclose_y
  -- The three running-sum magnitude bounds.
  have hexp' : x * y = hx * hy + hx * ty + tx * hy + tx * ty := hexp
  have hS1_eq : hx * hy - r = (x * y - r) - hx * ty - tx * hy - tx * ty := by
    linear_combination -hexp'
  have hS2_eq : (hx * hy - r) + hx * ty = (x * y - r) - tx * hy - tx * ty := by
    linear_combination -hexp'
  have hS3_eq : ((hx * hy - r) + hx * ty) + tx * hy = (x * y - r) - tx * ty := by
    linear_combination -hexp'
  have hS1_bound : |hx * hy - r| < bpow beta (prec + cr) := by
    rw [hS1_eq]
    have htri := abs_sub3_le (x * y - r) (hx * ty) (tx * hy) (tx * ty)
    linarith [htri, hb_err, hb_pht, hb_pth, hb_ptt, hcr_D, hC_D, hC2_D, hthresh1, hD_pos]
  have hS2_bound : |(hx * hy - r) + hx * ty| < bpow beta (prec + (s + (cx + cy))) := by
    rw [hS2_eq]
    have htri := abs_sub2_le (x * y - r) (tx * hy) (tx * ty)
    linarith [htri, hb_err, hb_pth, hb_ptt, hcr_C2, h2C2, hC2_pos, hC_pos]
  have hS3_bound : |((hx * hy - r) + hx * ty) + tx * hy| < bpow beta (prec + (s + (cx + cy))) := by
    rw [hS3_eq]
    have htri := abs_sub1_le (x * y - r) (tx * ty)
    linarith [htri, hb_err, hb_ptt, hcr_C2, h2C2, hC2_pos, hC_pos]
  -- Each step rounds exactly.
  have ht1 : round beta (FLX_exp prec) (Znearest choice) (hx * hy - r) = hx * hy - r := by
    have hw1 : -r = ((-M_r : ℤ) : ℝ) * bpow beta cr := by rw [hr_grid_eq]; push_cast; ring
    have h := round_add_grid_exact beta prec choice cr
      (M_hx * M_hy * beta.val ^ (prec + (cx + cy) - cr).toNat) (-M_r)
      hphh_at_cr hw1
      (by rw [show hx * hy + -r = hx * hy - r from by ring]; exact hS1_bound)
    rw [show hx * hy - r = hx * hy + -r from by ring]; exact h
  have ht2 : round beta (FLX_exp prec) (Znearest choice) ((hx * hy - r) + hx * ty)
      = (hx * hy - r) + hx * ty :=
    round_add_grid_exact beta prec choice (s + (cx + cy))
      (M_hx * M_hy * beta.val ^ s.toNat - M_r * beta.val ^ (cr - (s + (cx + cy))).toNat)
      (M_hx * (M_y - M_hy * beta.val ^ s.toNat)) hu2 hpht_grid hS2_bound
  have ht3 : round beta (FLX_exp prec) (Znearest choice) (((hx * hy - r) + hx * ty) + tx * hy)
      = ((hx * hy - r) + hx * ty) + tx * hy :=
    round_add_grid_exact beta prec choice (s + (cx + cy))
      (M_hx * M_hy * beta.val ^ s.toNat - M_r * beta.val ^ (cr - (s + (cx + cy))).toNat
        + M_hx * (M_y - M_hy * beta.val ^ s.toNat))
      ((M_x - M_hx * beta.val ^ s.toNat) * M_hy) hu3 hpth_grid hS3_bound
  have hS4_format : generic_format beta (FLX_exp prec) (x * y - r) := by
    have h := mult_error_FLX beta prec hp (Znearest choice) Fx Fy
    have h2 := generic_format_opp beta (FLX_exp prec) h
    rw [show -(r - x * y) = x * y - r from by ring] at h2
    exact h2
  have ht4 : round beta (FLX_exp prec) (Znearest choice)
      ((((hx * hy - r) + hx * ty) + tx * hy) + tx * ty) = x * y - r := by
    have hop : (((hx * hy - r) + hx * ty) + tx * hy) + tx * ty = x * y - r := by
      linear_combination -hexp'
    rw [hop]; exact round_generic beta (FLX_exp prec) (Znearest choice) hS4_format
  rw [ht1, ht2, ht3, ht4]; ring

/-- **Dekker TwoProduct, even precision.** For any `x, y` in `F(FLX, prec)` with
`2s = prec`, the FMA-free Dekker construction is error-free:
`x·y = round(x·y) + e`, where `e` is the four-step summation of the Veltkamp
sub-products against the rounded product. Covers all even-precision IEEE
variants (binary32, the decimal formats). The radix-2 odd-precision case
(binary64) needs the separate `tx·ty` exactness branch (Chunk 2). -/
theorem TwoProduct_FLX (beta : radix) (prec : ℤ) (hp : 0 < prec)
    (choice : ℤ → Bool) {s : ℤ} {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Fy : generic_format beta (FLX_exp prec) y)
    (hs : 2 * s = prec) (hs_lo : 2 ≤ s) :
    x * y
      = round beta (FLX_exp prec) (Znearest choice) (x * y)
      + round beta (FLX_exp prec) (Znearest choice)
          (round beta (FLX_exp prec) (Znearest choice)
            (round beta (FLX_exp prec) (Znearest choice)
              (round beta (FLX_exp prec) (Znearest choice)
                  (Veltkamp_hx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y
                    - round beta (FLX_exp prec) (Znearest choice) (x * y))
                + Veltkamp_hx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y)
              + Veltkamp_tx_FLX beta prec choice s x * Veltkamp_hx_FLX beta prec choice s y)
            + Veltkamp_tx_FLX beta prec choice s x * Veltkamp_tx_FLX beta prec choice s y) := by
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0
    rw [(Veltkamp_parts_zero beta prec choice s).1, (Veltkamp_parts_zero beta prec choice s).2]
    simp only [zero_mul, round_0, sub_zero, add_zero]
  rcases eq_or_ne y 0 with hy0 | hy0
  · subst hy0
    rw [(Veltkamp_parts_zero beta prec choice s).1, (Veltkamp_parts_zero beta prec choice s).2]
    simp only [mul_zero, round_0, sub_zero, add_zero]
  exact TwoProduct_FLX_main beta prec hp choice Fx Fy hs hs_lo hx0 hy0

end LeanFlocq
