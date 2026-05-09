/-
Port of `flocq/src/Calc/Bracket.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Locations: where a real number is positioned with respect to its
rounded-down value in an arbitrary format.

This file ports the foundational `location` enum, the `inbetween`
predicate, and the basic structural theorems. Step lemmas
(`new_location`, `inbetween_step_*`) and the float-level specialization
(`inbetween_float`) live in subsequent sections.
-/

import LeanFlocq.Core.Float_prop

namespace LeanFlocq

/-! ## Location of a real between two reference points -/

/-- A "location" of a real `x` relative to two reference points `d < u`:
either exact (`x = d`) or inexact, with the given ordering of `x` against
the midpoint `(d + u) / 2`. -/
inductive location where
  | Exact : location
  | Inexact (c : Ordering) : location
  deriving DecidableEq

/-- The "natural" location of `x` relative to `(d, u)`: exact when `x = d`,
otherwise inexact with the comparison of `x` against the midpoint. -/
noncomputable def inbetween_loc (d u x : ℝ) : location :=
  match compare x d with
  | .gt => location.Inexact (compare x ((d + u) / 2))
  | _ => location.Exact

/-- `inbetween d u x l`: the real `x` is positioned at location `l` relative
to `[d, u]`. `Exact` means `x = d`; `Inexact c` means `d < x < u` with
`compare x ((d+u)/2) = c`. -/
inductive inbetween (d u x : ℝ) : location → Prop where
  | Exact (h : x = d) : inbetween d u x location.Exact
  | Inexact (c : Ordering) (hx_lo : d < x) (hx_hi : x < u)
      (hc : compare x ((d + u) / 2) = c) :
        inbetween d u x (location.Inexact c)

/-! ### Foundational theorems on `inbetween` -/

/-- Comparison against the midpoint equals comparison of distances:
`compare x ((d+u)/2) = compare (x - d) (u - x)`. -/
theorem compare_middle_eq (d u x : ℝ) :
    compare x ((d + u) / 2) = compare (x - d) (u - x) := by
  rcases lt_trichotomy x ((d + u) / 2) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    have : x - d < u - x := by linarith
    rw [compare_lt_iff_lt.mpr this]
  · rw [compare_eq_iff_eq.mpr h]
    have : x - d = u - x := by linarith
    rw [compare_eq_iff_eq.mpr this]
  · rw [compare_gt_iff_gt.mpr h]
    have : u - x < x - d := by linarith
    rw [compare_gt_iff_gt.mpr this]

/-- `inbetween_loc` is the unique correct location for any `x` in `[d, u)`. -/
theorem inbetween_spec {d u : ℝ} (Hdu : d < u) {x : ℝ}
    (Hx : d ≤ x ∧ x < u) : inbetween d u x (inbetween_loc d u x) := by
  unfold inbetween_loc
  rcases lt_trichotomy x d with h | h | h
  · exfalso; linarith [Hx.1]
  · -- x = d, compare x d = .eq, falls through to Exact
    rw [compare_eq_iff_eq.mpr h]
    exact .Exact h
  · -- x > d
    rw [compare_gt_iff_gt.mpr h]
    exact .Inexact _ h Hx.2 rfl

/-- Two locations agreeing on `x` are equal. -/
theorem inbetween_unique {d u x : ℝ} {l l' : location}
    (Hl : inbetween d u x l) (Hl' : inbetween d u x l') : l = l' := by
  cases Hl with
  | Exact h =>
    cases Hl' with
    | Exact _ => rfl
    | Inexact _ hx_lo _ _ => exfalso; linarith
  | Inexact c hx_lo _ hc =>
    cases Hl' with
    | Exact h => exfalso; linarith
    | Inexact c' _ _ hc' =>
      congr 1; rw [← hc, ← hc']

/-- The bounds on `x` implied by `inbetween d u x l` (assuming `d < u`). -/
theorem inbetween_bounds {d u : ℝ} (Hdu : d < u) {x : ℝ} {l : location}
    (Hx : inbetween d u x l) : d ≤ x ∧ x < u := by
  cases Hx with
  | Exact h => exact ⟨le_of_eq h.symm, h ▸ Hdu⟩
  | Inexact _ hx_lo hx_hi _ => exact ⟨le_of_lt hx_lo, hx_hi⟩

/-- For non-`Exact` locations, the bounds are strict on both sides. -/
theorem inbetween_bounds_not_Eq {d u x : ℝ} {l : location}
    (Hx : inbetween d u x l) (Hl : l ≠ location.Exact) :
    d < x ∧ x < u := by
  cases Hx with
  | Exact _ => exact absurd rfl Hl
  | Inexact _ hx_lo hx_hi _ => exact ⟨hx_lo, hx_hi⟩

/-- For an inexact location, the comparison-of-distances equals the location's
recorded ordering. -/
theorem inbetween_distance_inexact {d u x : ℝ} {l : Ordering}
    (h : inbetween d u x (location.Inexact l)) :
    compare (x - d) (u - x) = l := by
  cases h with
  | Inexact _ _ _ hc => rw [← hc, compare_middle_eq]

/-- Variant using absolute values: `compare |d - x| |u - x| = l`. -/
theorem inbetween_distance_inexact_abs {d u x : ℝ} {l : Ordering}
    (h : inbetween d u x (location.Inexact l)) :
    compare |d - x| |u - x| = l := by
  -- From inbetween_Inexact: d < x < u.
  have ⟨hlo, hhi⟩ : d < x ∧ x < u := by
    cases h with
    | Inexact _ hx_lo hx_hi _ => exact ⟨hx_lo, hx_hi⟩
  -- |d - x| = x - d, |u - x| = u - x.
  rw [show |d - x| = x - d from by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)]
  rw [show |u - x| = u - x from abs_of_nonneg (by linarith)]
  exact inbetween_distance_inexact h

/-- Existence: for any `d < u` and any location `l`, some `x` realizes
`inbetween d u x l`. -/
theorem inbetween_ex {d u : ℝ} (Hdu : d < u) (l : location) :
    ∃ x, inbetween d u x l := by
  cases l with
  | Exact => exact ⟨d, .Exact rfl⟩
  | Inexact c =>
    have h_ud : 0 < u - d := by linarith
    -- Witness: d + (k/4) * (u - d), with k = 1, 2, 3 for c = lt, eq, gt.
    -- Compare against midpoint reduces to compare k 2.
    cases c with
    | lt =>
      refine ⟨d + (1/4) * (u - d), .Inexact .lt ?_ ?_ ?_⟩
      · have : 0 < (1/4 : ℝ) * (u - d) := by positivity
        linarith
      · have : (1/4 : ℝ) * (u - d) < u - d := by linarith
        linarith
      · apply compare_lt_iff_lt.mpr
        nlinarith
    | eq =>
      refine ⟨d + (1/2) * (u - d), .Inexact .eq ?_ ?_ ?_⟩
      · have : 0 < (1/2 : ℝ) * (u - d) := by positivity
        linarith
      · have : (1/2 : ℝ) * (u - d) < u - d := by linarith
        linarith
      · apply compare_eq_iff_eq.mpr; ring
    | gt =>
      refine ⟨d + (3/4) * (u - d), .Inexact .gt ?_ ?_ ?_⟩
      · have : 0 < (3/4 : ℝ) * (u - d) := by positivity
        linarith
      · have : (3/4 : ℝ) * (u - d) < u - d := by linarith
        linarith
      · apply compare_gt_iff_gt.mpr
        nlinarith

/-! ## Step lemmas: subdividing an interval into `nb_steps` parts -/

/-- Consecutive steps are ordered. -/
theorem ordered_steps (start step : ℝ) (Hstep : 0 < step) (k : ℤ) :
    start + (k : ℝ) * step < start + ((k + 1 : ℤ) : ℝ) * step := by
  push_cast
  nlinarith

/-- Midpoint formula for the interval `[start, start + k·step]`. -/
theorem middle_range (start step : ℝ) (k : ℤ) :
    (start + (start + (k : ℝ) * step)) / 2 = start + ((k : ℝ) / 2) * step := by
  ring

/-- Generic step dispatcher: an inbetween at sub-interval `k` lifts to an
inbetween at the global interval, with location given by comparing `x`
to the global midpoint. -/
theorem inbetween_step_not_Eq (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (x : ℝ) (k : ℤ) (l : location) (l' : Ordering)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l)
    (Hk : 0 < k ∧ k < nb_steps)
    (Hl' : compare x (start + ((nb_steps : ℝ) / 2) * step) = l') :
    inbetween start (start + (nb_steps : ℝ) * step) x (location.Inexact l') := by
  -- Bounds on x from the inner inbetween
  have h_inner := inbetween_bounds (ordered_steps start step Hstep k) Hx
  obtain ⟨hx_lo, hx_hi⟩ := h_inner
  -- Lift to outer bounds
  have h_outer_lo : start < x := by
    have h1 : start + 0 * step < start + (k : ℝ) * step := by
      have : 0 < (k : ℝ) := by exact_mod_cast Hk.1
      nlinarith
    have h2 : start = start + 0 * step := by ring
    linarith
  have h_outer_hi : x < start + (nb_steps : ℝ) * step := by
    have hk1 : (k + 1 : ℤ) ≤ nb_steps := Hk.2
    have : start + ((k + 1 : ℤ) : ℝ) * step ≤ start + (nb_steps : ℝ) * step := by
      have : ((k + 1 : ℤ) : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast hk1
      nlinarith
    linarith
  refine .Inexact l' h_outer_lo h_outer_hi ?_
  rw [← Hl', middle_range]

/-- Sub-interval `k` is in the lower half of `[0, nb_steps]` (`2k+1 < nb_steps`):
the location is `.lt`. -/
theorem inbetween_step_Lo (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (x : ℝ) (k : ℤ) (l : location)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l)
    (Hk1 : 0 < k) (Hk2 : 2 * k + 1 < nb_steps) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (location.Inexact .lt) := by
  apply inbetween_step_not_Eq start step Hstep nb_steps x k l .lt Hx
  · refine ⟨Hk1, ?_⟩; omega
  · -- Show compare x (start + (nb_steps/2) * step) = .lt
    apply compare_lt_iff_lt.mpr
    have h_inner := inbetween_bounds (ordered_steps start step Hstep k) Hx
    have hx_hi : x < start + ((k + 1 : ℤ) : ℝ) * step := h_inner.2
    -- (k+1)*step ≤ (nb_steps/2) * step
    have h_step_le : ((k + 1 : ℤ) : ℝ) * step ≤ ((nb_steps : ℝ) / 2) * step := by
      have h_int : 2 * (k + 1) ≤ nb_steps := by omega
      have h_real : ((k + 1 : ℤ) : ℝ) ≤ (nb_steps : ℝ) / 2 := by
        have : (2 : ℝ) * ((k + 1 : ℤ) : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast h_int
        linarith
      exact mul_le_mul_of_nonneg_right h_real (le_of_lt Hstep)
    linarith

/-- Sub-interval `k` is in the upper half (`nb_steps < 2k`): location is `.gt`. -/
theorem inbetween_step_Hi (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (x : ℝ) (k : ℤ) (l : location)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l)
    (Hk1 : nb_steps < 2 * k) (Hk2 : k < nb_steps) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (location.Inexact .gt) := by
  apply inbetween_step_not_Eq start step Hstep nb_steps x k l .gt Hx
  · refine ⟨?_, Hk2⟩; omega
  · -- Show compare x (start + (nb_steps/2) * step) = .gt
    apply compare_gt_iff_gt.mpr
    have h_inner := inbetween_bounds (ordered_steps start step Hstep k) Hx
    have hx_lo : start + (k : ℝ) * step ≤ x := h_inner.1
    -- (nb_steps/2) * step < k * step  (since 2k > nb_steps)
    have h_step_lt : ((nb_steps : ℝ) / 2) * step < (k : ℝ) * step := by
      have h_real : (nb_steps : ℝ) / 2 < (k : ℝ) := by
        have : (nb_steps : ℝ) < 2 * (k : ℝ) := by exact_mod_cast Hk1
        linarith
      exact mul_lt_mul_of_pos_right h_real Hstep
    linarith

/-- The 1-step case: `inbetween start (start + step) x l` with `l ≠ Exact`
and `nb_steps > 1` lifts to `Inexact .lt`. -/
theorem inbetween_step_Lo_not_Eq (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (x : ℝ) (l : location)
    (Hx : inbetween start (start + step) x l)
    (Hl : l ≠ location.Exact) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (location.Inexact .lt) := by
  -- Convert to the `inbetween_step_Lo` form via k = 0... no wait, k = 0 is excluded.
  -- Direct proof: x is in (start, start + step) strictly. start + step ≤ start + (nb_steps/2)*step.
  have hx_strict := inbetween_bounds_not_Eq Hx Hl
  refine .Inexact .lt hx_strict.1 ?_ ?_
  · -- x < start + nb_steps * step
    have h_step_le : start + step ≤ start + (nb_steps : ℝ) * step := by
      have : (1 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast (by omega : 1 ≤ nb_steps)
      have : step ≤ (nb_steps : ℝ) * step := by nlinarith
      linarith
    linarith [hx_strict.2]
  · -- compare x ((start + (start + nb_steps*step))/2) = .lt
    rw [middle_range]
    apply compare_lt_iff_lt.mpr
    -- x < start + step ≤ start + (nb_steps/2) * step  (since nb_steps ≥ 2)
    have h_step_le : start + step ≤ start + ((nb_steps : ℝ) / 2) * step := by
      have : (1 : ℝ) ≤ (nb_steps : ℝ) / 2 := by
        have : (2 : ℝ) ≤ (nb_steps : ℝ) := by exact_mod_cast (by omega : 2 ≤ nb_steps)
        linarith
      nlinarith
    linarith [hx_strict.2]

/-- For odd `nb_steps`, the midpoint of the `k`-th sub-interval (where
`2k+1 = nb_steps`) coincides with the global midpoint. -/
theorem middle_odd (start step : ℝ) (nb_steps : ℤ) (k : ℤ)
    (Hk : 2 * k + 1 = nb_steps) :
    ((start + (k : ℝ) * step) + (start + ((k + 1 : ℤ) : ℝ) * step)) / 2
      = start + (nb_steps : ℝ) / 2 * step := by
  have h_real : (2 : ℝ) * (k : ℝ) + 1 = (nb_steps : ℝ) := by exact_mod_cast Hk
  push_cast
  have : (start + (k : ℝ) * step + (start + ((k : ℝ) + 1) * step)) / 2
       = start + ((2 * (k : ℝ) + 1) / 2) * step := by ring
  rw [this, h_real]

/-- Odd `nb_steps`, `k`-th sub-interval is the middle one (`2k+1 = nb_steps`),
with an Inexact location: result is the same Inexact ordering. -/
theorem inbetween_step_any_Mi_odd (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (x : ℝ) (k : ℤ) (l : Ordering)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x (location.Inexact l))
    (Hk : 2 * k + 1 = nb_steps) :
    inbetween start (start + (nb_steps : ℝ) * step) x (location.Inexact l) := by
  apply inbetween_step_not_Eq start step Hstep nb_steps x k _ l Hx
  · refine ⟨?_, ?_⟩ <;> omega
  · cases Hx with
    | Inexact _ _ _ hc =>
      rw [show start + ((nb_steps : ℝ) / 2) * step
          = (start + (k : ℝ) * step + (start + ((k + 1 : ℤ) : ℝ) * step)) / 2
          from (middle_odd start step nb_steps k Hk).symm]
      exact hc

/-- Odd `nb_steps`, `k`-th sub-interval is the middle one and the inner
location is Exact: result is `Inexact .lt`. -/
theorem inbetween_step_Lo_Mi_Eq_odd (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (x : ℝ) (k : ℤ)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x location.Exact)
    (Hk : 2 * k + 1 = nb_steps) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (location.Inexact .lt) := by
  apply inbetween_step_not_Eq start step Hstep nb_steps x k _ .lt Hx
  · refine ⟨?_, ?_⟩ <;> omega
  · cases Hx with
    | Exact h =>
      rw [h]
      apply compare_lt_iff_lt.mpr
      -- start + k*step < start + ((nb_steps)/2) * step ↔ k < nb_steps/2
      have h_real : (2 : ℝ) * (k : ℝ) + 1 = (nb_steps : ℝ) := by exact_mod_cast Hk
      have : (k : ℝ) < (nb_steps : ℝ) / 2 := by linarith
      nlinarith

/-- Even `nb_steps`, `k = nb_steps/2`, with non-Exact inner location:
result is `Inexact .gt`. -/
theorem inbetween_step_Hi_Mi_even (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (x : ℝ) (k : ℤ) (l : location)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l)
    (Hl : l ≠ location.Exact)
    (Hk : 2 * k = nb_steps) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (location.Inexact .gt) := by
  apply inbetween_step_not_Eq start step Hstep nb_steps x k l .gt Hx
  · refine ⟨?_, ?_⟩ <;> omega
  · apply compare_gt_iff_gt.mpr
    have hx_strict := inbetween_bounds_not_Eq Hx Hl
    -- x > start + k*step = start + (nb_steps/2)*step
    have h_real : (2 : ℝ) * (k : ℝ) = (nb_steps : ℝ) := by exact_mod_cast Hk
    have h_eq : (k : ℝ) = (nb_steps : ℝ) / 2 := by linarith
    have : start + (k : ℝ) * step = start + ((nb_steps : ℝ) / 2) * step := by rw [h_eq]
    linarith [hx_strict.1]

/-- Even `nb_steps`, `k = nb_steps/2`, inner location is Exact:
result is `Inexact .eq`. -/
theorem inbetween_step_Mi_Mi_even (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (x : ℝ) (k : ℤ)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x location.Exact)
    (Hk : 2 * k = nb_steps) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (location.Inexact .eq) := by
  apply inbetween_step_not_Eq start step Hstep nb_steps x k _ .eq Hx
  · refine ⟨?_, ?_⟩ <;> omega
  · cases Hx with
    | Exact h =>
      rw [h]
      apply compare_eq_iff_eq.mpr
      have h_real : (2 : ℝ) * (k : ℝ) = (nb_steps : ℝ) := by exact_mod_cast Hk
      have h_eq : (k : ℝ) = (nb_steps : ℝ) / 2 := by linarith
      rw [h_eq]

/-! ## new_location: dispatch between even and odd radix -/

/-- New location for even `nb_steps`. -/
def new_location_even (nb_steps : ℤ) (k : ℤ) (l : location) : location :=
  if k = 0 then
    match l with
    | .Exact => .Exact
    | _ => .Inexact .lt
  else
    match compare (2 * k) nb_steps with
    | .lt => .Inexact .lt
    | .eq =>
      match l with
      | .Exact => .Inexact .eq
      | _ => .Inexact .gt
    | .gt => .Inexact .gt

/-- New location for odd `nb_steps`. -/
def new_location_odd (nb_steps : ℤ) (k : ℤ) (l : location) : location :=
  if k = 0 then
    match l with
    | .Exact => .Exact
    | _ => .Inexact .lt
  else
    match compare (2 * k + 1) nb_steps with
    | .lt => .Inexact .lt
    | .eq =>
      match l with
      | .Exact => .Inexact .lt
      | .Inexact c => .Inexact c
    | .gt => .Inexact .gt

/-- The general `new_location`: dispatches on the parity of `nb_steps`. -/
def new_location (nb_steps : ℤ) (k : ℤ) (l : location) : location :=
  if nb_steps % 2 = 0 then new_location_even nb_steps k l
  else new_location_odd nb_steps k l

theorem new_location_even_correct (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (Heven : nb_steps % 2 = 0)
    (x : ℝ) (k : ℤ) (l : location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (new_location_even nb_steps k l) := by
  unfold new_location_even
  by_cases hk0 : k = 0
  · subst hk0
    -- Hx is on the interval [start + 0*step, start + 1*step] = [start, start + step]
    have h_eq1 : (start + ((0 : ℤ) : ℝ) * step) = start := by push_cast; ring
    have h_eq2 : (start + ((0 + 1 : ℤ) : ℝ) * step) = start + step := by
      push_cast; ring
    rw [h_eq1, h_eq2] at Hx
    simp only [if_pos rfl]
    cases l with
    | Exact =>
      cases Hx with
      | Exact h => exact .Exact h
    | Inexact c =>
      apply inbetween_step_Lo_not_Eq start step Hstep nb_steps Hnb x (.Inexact c) Hx
      intro h; cases h
  · simp only [if_neg hk0]
    rcases lt_trichotomy (2 * k) nb_steps with h_lt | h_eq | h_gt
    · rw [compare_lt_iff_lt.mpr h_lt]
      apply inbetween_step_Lo start step Hstep nb_steps x k l Hx (by omega)
      omega
    · rw [compare_eq_iff_eq.mpr h_eq]
      cases l with
      | Exact =>
        exact inbetween_step_Mi_Mi_even start step Hstep nb_steps Hnb x k Hx h_eq
      | Inexact c =>
        apply inbetween_step_Hi_Mi_even start step Hstep nb_steps Hnb x k
          (.Inexact c) Hx ?_ h_eq
        intro hh; cases hh
    · rw [compare_gt_iff_gt.mpr h_gt]
      exact inbetween_step_Hi start step Hstep nb_steps x k l Hx h_gt Hk.2

theorem new_location_odd_correct (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps) (Hodd : nb_steps % 2 = 1)
    (x : ℝ) (k : ℤ) (l : location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (new_location_odd nb_steps k l) := by
  unfold new_location_odd
  by_cases hk0 : k = 0
  · subst hk0
    have h_eq1 : (start + ((0 : ℤ) : ℝ) * step) = start := by push_cast; ring
    have h_eq2 : (start + ((0 + 1 : ℤ) : ℝ) * step) = start + step := by
      push_cast; ring
    rw [h_eq1, h_eq2] at Hx
    simp only [if_pos rfl]
    cases l with
    | Exact =>
      cases Hx with
      | Exact h => exact .Exact h
    | Inexact c =>
      apply inbetween_step_Lo_not_Eq start step Hstep nb_steps Hnb x (.Inexact c) Hx
      intro h; cases h
  · simp only [if_neg hk0]
    rcases lt_trichotomy (2 * k + 1) nb_steps with h_lt | h_eq | h_gt
    · rw [compare_lt_iff_lt.mpr h_lt]
      exact inbetween_step_Lo start step Hstep nb_steps x k l Hx (by omega) h_lt
    · rw [compare_eq_iff_eq.mpr h_eq]
      cases l with
      | Exact =>
        exact inbetween_step_Lo_Mi_Eq_odd start step Hstep nb_steps Hnb x k Hx h_eq
      | Inexact c =>
        exact inbetween_step_any_Mi_odd start step Hstep nb_steps Hnb x k c Hx h_eq
    · rw [compare_gt_iff_gt.mpr h_gt]
      apply inbetween_step_Hi start step Hstep nb_steps x k l Hx ?_ Hk.2
      omega

/-- The general dispatcher. -/
theorem new_location_correct (start step : ℝ) (Hstep : 0 < step)
    (nb_steps : ℤ) (Hnb : 1 < nb_steps)
    (x : ℝ) (k : ℤ) (l : location)
    (Hk : 0 ≤ k ∧ k < nb_steps)
    (Hx : inbetween (start + (k : ℝ) * step)
                    (start + ((k + 1 : ℤ) : ℝ) * step) x l) :
    inbetween start (start + (nb_steps : ℝ) * step) x
              (new_location nb_steps k l) := by
  unfold new_location
  by_cases hev : nb_steps % 2 = 0
  · rw [if_pos hev]
    exact new_location_even_correct start step Hstep nb_steps Hnb hev x k l Hk Hx
  · rw [if_neg hev]
    have hodd : nb_steps % 2 = 1 := by omega
    exact new_location_odd_correct start step Hstep nb_steps Hnb hodd x k l Hk Hx

end LeanFlocq
