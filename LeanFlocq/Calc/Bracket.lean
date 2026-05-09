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

end LeanFlocq
