/-
Port of `flocq/src/Calc/Div.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Helper function and theorem for computing the rounded quotient of two
floating-point numbers.
-/

import LeanFlocq.Calc.Bracket
import LeanFlocq.Core.Generic_fmt

namespace LeanFlocq

variable (beta : radix) (fexp : ℤ → ℤ)

/-! ## Magnitude of a quotient of `F2R`s -/

/-- `mag β (F2R⟨m1, e1⟩ / F2R⟨m2, e2⟩)` is between
`(Zdigits m1 + e1) - (Zdigits m2 + e2)` and that plus 1. -/
theorem mag_div_F2R (m1 e1 m2 e2 : ℤ) (Hm1 : 0 < m1) (Hm2 : 0 < m2) :
    let e := (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2)
    e ≤ mag beta (F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩) ∧
    mag beta (F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩) ≤ e + 1 := by
  have hm1_ne : m1 ≠ 0 := by linarith
  have hm2_ne : m2 ≠ 0 := by linarith
  have hF1 : F2R (beta := beta) ⟨m1, e1⟩ ≠ 0 := F2R_neq_0 ⟨m1, e1⟩ hm1_ne
  have hF2 : F2R (beta := beta) ⟨m2, e2⟩ ≠ 0 := F2R_neq_0 ⟨m2, e2⟩ hm2_ne
  have h_mag1 : mag beta (F2R (beta := beta) ⟨m1, e1⟩) = Zdigits beta m1 + e1 :=
    mag_F2R_Zdigits m1 e1 hm1_ne
  have h_mag2 : mag beta (F2R (beta := beta) ⟨m2, e2⟩) = Zdigits beta m2 + e2 :=
    mag_F2R_Zdigits m2 e2 hm2_ne
  have h := mag_div beta hF1 hF2
  rw [h_mag1, h_mag2] at h
  exact h

/-! ## Helper: normalize `m * bpow e / (m' * bpow e')` to canonical form -/

private theorem quot_eq_mul_bpow (m1 m2 : ℤ) (e1 e2 : ℤ) (Hm2 : (m2 : ℝ) ≠ 0) :
    (m1 : ℝ) * bpow beta e1 / ((m2 : ℝ) * bpow beta e2)
      = ((m1 : ℝ) / (m2 : ℝ)) * bpow beta (e1 - e2) := by
  have h_bpow : bpow beta e1 = bpow beta (e1 - e2) * bpow beta e2 := by
    rw [← bpow_plus]; congr 1; ring
  have h_bpow_e2_ne : bpow beta e2 ≠ 0 := bpow_ne_0 beta e2
  rw [h_bpow]
  field_simp

/-! ## The Fdiv_core algorithm -/

/-- Shifted mantissa pair for `Fdiv_core`. -/
private noncomputable def fdiv_pair (m1 e1 m2 e2 e : ℤ) : ℤ × ℤ :=
  if e ≤ e1 - e2 then (m1 * (beta.val : ℤ) ^ (e1 - e2 - e).toNat, m2)
  else (m1, m2 * (beta.val : ℤ) ^ (e - (e1 - e2)).toNat)

/-- The shifted pair satisfies the quotient identity. -/
private theorem fdiv_pair_quot (m1 e1 m2 e2 e : ℤ) (Hm2 : 0 < m2) :
    let p := fdiv_pair beta m1 e1 m2 e2 e
    F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩
      = ((p.1 : ℝ) / (p.2 : ℝ)) * bpow beta e ∧ 0 < p.2 := by
  unfold fdiv_pair
  have h_m2_real_ne : (m2 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt Hm2)
  have h_m2_real_pos : (0 : ℝ) < (m2 : ℝ) := by exact_mod_cast Hm2
  have h_lhs_canonical :
      F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩
        = ((m1 : ℝ) / (m2 : ℝ)) * bpow beta (e1 - e2) := by
    show ((m1 : ℝ) * bpow beta e1) / ((m2 : ℝ) * bpow beta e2) = _
    exact quot_eq_mul_bpow beta m1 m2 e1 e2 h_m2_real_ne
  by_cases he : e ≤ e1 - e2
  · simp only [if_pos he]
    refine ⟨?_, Hm2⟩
    have hd : 0 ≤ e1 - e2 - e := by omega
    have hpow_real : (((beta.val : ℤ) ^ (e1 - e2 - e).toNat : ℤ) : ℝ) = bpow beta (e1 - e2 - e) :=
      IZR_Zpower beta hd
    rw [h_lhs_canonical]
    show ((m1 : ℝ) / (m2 : ℝ)) * bpow beta (e1 - e2)
        = ((((m1 * (beta.val : ℤ) ^ (e1 - e2 - e).toNat : ℤ)) : ℝ) / (m2 : ℝ)) * bpow beta e
    rw [show (((m1 * (beta.val : ℤ) ^ (e1 - e2 - e).toNat : ℤ)) : ℝ)
        = (m1 : ℝ) * (((beta.val : ℤ) ^ (e1 - e2 - e).toNat : ℤ) : ℝ) from by push_cast; ring]
    rw [hpow_real]
    have h_split : bpow beta (e1 - e2) = bpow beta (e1 - e2 - e) * bpow beta e := by
      rw [← bpow_plus]; congr 1; ring
    rw [h_split]; ring
  · simp only [if_neg he]
    push_neg at he
    have hd : 0 ≤ e - (e1 - e2) := by omega
    have hpow_real : (((beta.val : ℤ) ^ (e - (e1 - e2)).toNat : ℤ) : ℝ) = bpow beta (e - (e1 - e2)) :=
      IZR_Zpower beta hd
    have h_pow_pos : 0 < (beta.val : ℤ) ^ (e - (e1 - e2)).toNat := pow_pos beta.radix_gt_0 _
    refine ⟨?_, mul_pos Hm2 h_pow_pos⟩
    rw [h_lhs_canonical]
    show ((m1 : ℝ) / (m2 : ℝ)) * bpow beta (e1 - e2)
        = ((m1 : ℝ) / (((m2 * (beta.val : ℤ) ^ (e - (e1 - e2)).toNat : ℤ) : ℝ))) * bpow beta e
    rw [show (((m2 * (beta.val : ℤ) ^ (e - (e1 - e2)).toNat : ℤ)) : ℝ)
        = (m2 : ℝ) * (((beta.val : ℤ) ^ (e - (e1 - e2)).toNat : ℤ) : ℝ) from by push_cast; ring]
    rw [hpow_real]
    have h_split : bpow beta e = bpow beta (e1 - e2) * bpow beta (e - (e1 - e2)) := by
      rw [← bpow_plus]; congr 1; ring
    have h_bpow_diff_pos : 0 < bpow beta (e - (e1 - e2)) := bpow_gt_0 _ _
    have h_bpow_diff_ne : bpow beta (e - (e1 - e2)) ≠ 0 := ne_of_gt h_bpow_diff_pos
    rw [h_split]
    field_simp

/-- `Fdiv_core m1 e1 m2 e2 e`: the core division producing
`(quotient, location)` for the bracketing of the real quotient at exp `e`. -/
noncomputable def Fdiv_core (m1 e1 m2 e2 e : ℤ) : ℤ × location :=
  let p := fdiv_pair beta m1 e1 m2 e2 e
  (p.1 / p.2, new_location p.2 (p.1 % p.2) location.Exact)

/-- Correctness of `Fdiv_core`: the result brackets the real quotient. -/
theorem Fdiv_core_correct (m1 e1 m2 e2 e : ℤ) (Hm1 : 0 < m1) (Hm2 : 0 < m2) :
    let r := Fdiv_core beta m1 e1 m2 e2 e
    inbetween_float beta r.1 e
      (F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩) r.2 := by
  unfold Fdiv_core
  set p := fdiv_pair beta m1 e1 m2 e2 e with hp
  obtain ⟨h_quot, h_m2'_pos⟩ := fdiv_pair_quot beta m1 e1 m2 e2 e Hm2
  rw [show fdiv_pair beta m1 e1 m2 e2 e = p from rfl] at h_quot h_m2'_pos
  rw [h_quot]
  set q := p.1 / p.2 with hq
  set r := p.1 % p.2 with hr
  have h_r_lt : r < p.2 := Int.emod_lt_of_pos p.1 h_m2'_pos
  have h_r_ge : 0 ≤ r := Int.emod_nonneg p.1 (ne_of_gt h_m2'_pos)
  have h_div_mod : p.2 * q + r = p.1 := Int.mul_ediv_add_emod p.1 p.2
  have h_p2_real_pos : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast h_m2'_pos
  have h_p2_real_ne : (p.2 : ℝ) ≠ 0 := ne_of_gt h_p2_real_pos
  have h_pq : (p.1 : ℝ) / (p.2 : ℝ) = (q : ℝ) + (r : ℝ) / (p.2 : ℝ) := by
    have h_real : (p.1 : ℝ) = (p.2 : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast h_div_mod.symm
    rw [h_real]
    field_simp
  rw [h_pq]
  unfold inbetween_float
  show inbetween ((q : ℝ) * bpow beta e) (((q + 1 : ℤ) : ℝ) * bpow beta e)
        (((q : ℝ) + (r : ℝ) / (p.2 : ℝ)) * bpow beta e)
        (new_location p.2 r location.Exact)
  rw [show (((q + 1 : ℤ)) : ℝ) = (q : ℝ) + 1 from by push_cast; rfl]
  -- Establish unit-scale inbetween, then lift by inbetween_mult_compat.
  have h_inbetween_unit : inbetween (q : ℝ) ((q : ℝ) + 1) ((q : ℝ) + (r : ℝ) / (p.2 : ℝ))
      (new_location p.2 r location.Exact) := by
    by_cases hm2 : p.2 = 1
    · have hr0 : r = 0 := by omega
      have hnl : new_location 1 0 location.Exact = location.Exact := by
        unfold new_location
        rw [if_neg (by decide : ¬ ((1 : ℤ) % 2 = 0))]
        unfold new_location_odd
        rw [if_pos rfl]
      rw [hr0, hm2, hnl]
      have h_x_eq : (q : ℝ) + ((0 : ℤ) : ℝ) / ((1 : ℤ) : ℝ) = (q : ℝ) := by push_cast; ring
      rw [h_x_eq]
      exact .Exact rfl
    · have h_p2_gt_1 : 1 < p.2 := by omega
      have h_step_pos : (0 : ℝ) < 1 / (p.2 : ℝ) := by positivity
      have hk_bd : 0 ≤ r ∧ r < p.2 := ⟨h_r_ge, h_r_lt⟩
      have h_inner : inbetween ((q : ℝ) + (r : ℝ) * (1 / (p.2 : ℝ)))
          ((q : ℝ) + (((r + 1 : ℤ)) : ℝ) * (1 / (p.2 : ℝ)))
          ((q : ℝ) + (r : ℝ) / (p.2 : ℝ)) location.Exact := by
        refine .Exact ?_
        field_simp
      have h_apply := new_location_correct (q : ℝ) (1 / (p.2 : ℝ)) h_step_pos
        p.2 h_p2_gt_1 ((q : ℝ) + (r : ℝ) / (p.2 : ℝ)) r location.Exact hk_bd h_inner
      have h_q_p1 : (q : ℝ) + ((p.2 : ℤ) : ℝ) * (1 / (p.2 : ℝ)) = (q : ℝ) + 1 := by
        push_cast
        field_simp
      rw [h_q_p1] at h_apply
      exact h_apply
  exact inbetween_mult_compat (q : ℝ) ((q : ℝ) + 1) ((q : ℝ) + (r : ℝ) / (p.2 : ℝ))
    (new_location p.2 r location.Exact) (bpow beta e) (bpow_gt_0 beta e) h_inbetween_unit

/-! ## The full Fdiv -/

/-- `Fdiv x y`: divide `x` by `y` in float representation, returning a triple
`(m, e, l)` where `m` is the quotient mantissa at exponent `e ≤ cexp(x/y)`,
with location `l` indicating the residue. -/
noncomputable def Fdiv (x y : float beta) : ℤ × ℤ × location :=
  let m1 := x.Fnum
  let e1 := x.Fexp
  let m2 := y.Fnum
  let e2 := y.Fexp
  let e' := (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2)
  let e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2)
  let r := Fdiv_core beta m1 e1 m2 e2 e
  (r.1, e, r.2)

/-- Correctness of `Fdiv`: bracketing at exponent ≤ canonical exponent of quotient. -/
theorem Fdiv_correct (x y : float beta) (Hx : 0 < F2R x) (Hy : 0 < F2R y) :
    let r := Fdiv beta fexp x y
    r.2.1 ≤ cexp beta fexp (F2R x / F2R y) ∧
    inbetween_float beta r.1 r.2.1 (F2R x / F2R y) r.2.2 := by
  unfold Fdiv
  cases x with | mk m1 e1 =>
  cases y with | mk m2 e2 =>
  have hm1 : 0 < m1 := gt_0_F2R Hx
  have hm2 : 0 < m2 := gt_0_F2R Hy
  set e' := (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2) with he'_def
  set e := min (min (fexp e') (fexp (e' + 1))) (e1 - e2) with he_def
  have h_mag := mag_div_F2R beta m1 e1 m2 e2 hm1 hm2
  rw [show (Zdigits beta m1 + e1) - (Zdigits beta m2 + e2) = e' from rfl] at h_mag
  obtain ⟨h_mag_ge, h_mag_le⟩ := h_mag
  have h_core := Fdiv_core_correct beta m1 e1 m2 e2 e hm1 hm2
  refine ⟨?_, h_core⟩
  -- e ≤ cexp x/y
  show e ≤ fexp (mag beta (F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩))
  rcases lt_or_eq_of_le h_mag_ge with h_strict | h_eq
  · -- mag = e' + 1
    have h_mag_eq : mag beta (F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩) = e' + 1 := by
      omega
    rw [h_mag_eq]
    calc e ≤ min (fexp e') (fexp (e' + 1)) := min_le_left _ _
      _ ≤ fexp (e' + 1) := min_le_right _ _
  · -- mag = e'
    have h_mag_eq : mag beta (F2R (beta := beta) ⟨m1, e1⟩ / F2R (beta := beta) ⟨m2, e2⟩) = e' := h_eq.symm
    rw [h_mag_eq]
    calc e ≤ min (fexp e') (fexp (e' + 1)) := min_le_left _ _
      _ ≤ fexp e' := min_le_left _ _

end LeanFlocq
