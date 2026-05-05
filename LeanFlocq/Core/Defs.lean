/-
Port of `flocq/src/Core/Defs.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Basic definitions: float, F2R, and rounding predicates.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import LeanFlocq.Core.Raux

namespace LeanFlocq

/-- A floating-point number in radix `beta`: integer mantissa and exponent. -/
structure float (beta : radix) where
  Fnum : ℤ
  Fexp : ℤ

/-- Real value of a float: `Fnum * beta^Fexp`. -/
noncomputable def F2R {beta : radix} (f : float beta) : ℝ :=
  (f.Fnum : ℝ) * bpow beta f.Fexp

/-! ### Requirements on a rounding mode -/

/-- A rounding predicate is total: every real has at least one rounded image. -/
def round_pred_total (P : ℝ → ℝ → Prop) : Prop :=
  ∀ x, ∃ f, P x f

/-- A rounding predicate is monotone in its input. -/
def round_pred_monotone (P : ℝ → ℝ → Prop) : Prop :=
  ∀ x y f g, P x f → P y g → x ≤ y → f ≤ g

/-- A rounding predicate is total and monotone. -/
def round_pred (P : ℝ → ℝ → Prop) : Prop :=
  round_pred_total P ∧ round_pred_monotone P

/-! ### Pointwise rounding properties -/

/-- `f` is the round-down (toward −∞) of `x` in format `F`. -/
def Rnd_DN_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ f ≤ x ∧ ∀ g, F g → g ≤ x → g ≤ f

/-- `f` is the round-up (toward +∞) of `x` in format `F`. -/
def Rnd_UP_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ x ≤ f ∧ ∀ g, F g → x ≤ g → f ≤ g

/-- `f` is the round-toward-zero of `x` in format `F`. -/
def Rnd_ZR_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  (0 ≤ x → Rnd_DN_pt F x f) ∧ (x ≤ 0 → Rnd_UP_pt F x f)

/-- `f` is a round-to-nearest of `x` in format `F`. -/
def Rnd_N_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧ ∀ g, F g → |f - x| ≤ |g - x|

/-- Round to nearest with tie-breaking by predicate `P`. -/
def Rnd_NG_pt (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_N_pt F x f ∧ (P x f ∨ ∀ f2, Rnd_N_pt F x f2 → f2 = f)

/-- Round to nearest, ties away from zero. -/
def Rnd_NA_pt (F : ℝ → Prop) (x f : ℝ) : Prop :=
  Rnd_N_pt F x f ∧ ∀ f2, Rnd_N_pt F x f2 → |f2| ≤ |f|

end LeanFlocq
