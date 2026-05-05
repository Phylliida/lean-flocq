/-
Port of `flocq/src/Core/Round_pred.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Properties of rounding predicates: monotonicity, uniqueness, reflexivity,
idempotence, behaviour under negation, and characterizations of round-to-nearest.

Skipped here (require real-number completeness machinery):
`round_val_of_pred`, `round_fun_of_pred`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import LeanFlocq.Core.Defs

namespace LeanFlocq

variable {F : ℝ → Prop}

/-! ### Function-level rounding predicates -/

/-- Function `rnd` is a round-down for format `F`. -/
def Rnd_DN (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  ∀ x, Rnd_DN_pt F x (rnd x)

/-- Function `rnd` is a round-up for format `F`. -/
def Rnd_UP (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  ∀ x, Rnd_UP_pt F x (rnd x)

/-- Function `rnd` is a round-toward-zero for format `F`. -/
def Rnd_ZR (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  ∀ x, Rnd_ZR_pt F x (rnd x)

/-- Function `rnd` is a round-to-nearest for format `F`. -/
def Rnd_N (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  ∀ x, Rnd_N_pt F x (rnd x)

/-- Function `rnd` is round-to-nearest with tie-breaking `P`. -/
def Rnd_NG (F : ℝ → Prop) (P : ℝ → ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  ∀ x, Rnd_NG_pt F P x (rnd x)

/-- Function `rnd` is round-to-nearest with ties away from zero. -/
def Rnd_NA (F : ℝ → Prop) (rnd : ℝ → ℝ) : Prop :=
  ∀ x, Rnd_NA_pt F x (rnd x)

/-! ### Uniqueness from monotonicity -/

theorem round_unique (rnd : ℝ → ℝ → Prop) (Hr : round_pred_monotone rnd)
    {x f1 f2 : ℝ} (h1 : rnd x f1) (h2 : rnd x f2) : f1 = f2 :=
  le_antisymm (Hr x x f1 f2 h1 h2 (le_refl x))
              (Hr x x f2 f1 h2 h1 (le_refl x))

/-! ### Round-down properties -/

theorem Rnd_DN_pt_monotone (F : ℝ → Prop) :
    round_pred_monotone (Rnd_DN_pt F) := by
  intro x y f g hx hy hxy
  exact hy.2.2 f hx.1 (le_trans hx.2.1 hxy)

theorem Rnd_DN_pt_unique (F : ℝ → Prop) {x f1 f2 : ℝ}
    (h1 : Rnd_DN_pt F x f1) (h2 : Rnd_DN_pt F x f2) : f1 = f2 :=
  round_unique _ (Rnd_DN_pt_monotone F) h1 h2

theorem Rnd_DN_unique (F : ℝ → Prop) {rnd1 rnd2 : ℝ → ℝ}
    (h1 : Rnd_DN F rnd1) (h2 : Rnd_DN F rnd2) (x : ℝ) :
    rnd1 x = rnd2 x :=
  Rnd_DN_pt_unique F (h1 x) (h2 x)

/-! ### Round-up properties -/

theorem Rnd_UP_pt_monotone (F : ℝ → Prop) :
    round_pred_monotone (Rnd_UP_pt F) := by
  intro x y f g hx hy hxy
  exact hx.2.2 g hy.1 (le_trans hxy hy.2.1)

theorem Rnd_UP_pt_unique (F : ℝ → Prop) {x f1 f2 : ℝ}
    (h1 : Rnd_UP_pt F x f1) (h2 : Rnd_UP_pt F x f2) : f1 = f2 :=
  round_unique _ (Rnd_UP_pt_monotone F) h1 h2

theorem Rnd_UP_unique (F : ℝ → Prop) {rnd1 rnd2 : ℝ → ℝ}
    (h1 : Rnd_UP F rnd1) (h2 : Rnd_UP F rnd2) (x : ℝ) :
    rnd1 x = rnd2 x :=
  Rnd_UP_pt_unique F (h1 x) (h2 x)

/-! ### Reflexivity and idempotence -/

theorem Rnd_DN_pt_refl (F : ℝ → Prop) {x : ℝ} (hx : F x) : Rnd_DN_pt F x x :=
  ⟨hx, le_refl x, fun _ _ hg => hg⟩

theorem Rnd_DN_pt_idempotent (F : ℝ → Prop) {x f : ℝ}
    (h : Rnd_DN_pt F x f) (hx : F x) : f = x :=
  le_antisymm h.2.1 (h.2.2 x hx (le_refl x))

theorem Rnd_UP_pt_refl (F : ℝ → Prop) {x : ℝ} (hx : F x) : Rnd_UP_pt F x x :=
  ⟨hx, le_refl x, fun _ _ hg => hg⟩

theorem Rnd_UP_pt_idempotent (F : ℝ → Prop) {x f : ℝ}
    (h : Rnd_UP_pt F x f) (hx : F x) : f = x :=
  le_antisymm (h.2.2 x hx (le_refl x)) h.2.1

/-! ### Negation symmetry between DN and UP -/

theorem Rnd_UP_pt_opp (F : ℝ → Prop) (HF : ∀ x, F x → F (-x))
    {x f : ℝ} (h : Rnd_DN_pt F x f) : Rnd_UP_pt F (-x) (-f) := by
  refine ⟨HF f h.1, neg_le_neg h.2.1, ?_⟩
  intro g Hg Hxg
  rw [show g = -(-g) from (neg_neg g).symm]
  apply neg_le_neg
  exact h.2.2 (-g) (HF g Hg) (by linarith)

theorem Rnd_DN_pt_opp (F : ℝ → Prop) (HF : ∀ x, F x → F (-x))
    {x f : ℝ} (h : Rnd_UP_pt F x f) : Rnd_DN_pt F (-x) (-f) := by
  refine ⟨HF f h.1, neg_le_neg h.2.1, ?_⟩
  intro g Hg Hxg
  rw [show g = -(-g) from (neg_neg g).symm]
  apply neg_le_neg
  exact h.2.2 (-g) (HF g Hg) (by linarith)

theorem Rnd_DN_opp (F : ℝ → Prop) (HF : ∀ x, F x → F (-x))
    {rnd1 rnd2 : ℝ → ℝ} (h1 : Rnd_DN F rnd1) (h2 : Rnd_UP F rnd2)
    (x : ℝ) : rnd1 (-x) = -rnd2 x := by
  have hrnd' : Rnd_UP F (fun y => -rnd1 (-y)) := by
    intro y
    have hdn : Rnd_DN_pt F (-y) (rnd1 (-y)) := h1 (-y)
    have hup : Rnd_UP_pt F (-(-y)) (-(rnd1 (-y))) := Rnd_UP_pt_opp F HF hdn
    rw [neg_neg] at hup
    exact hup
  have heq : -rnd1 (-x) = rnd2 x := Rnd_UP_unique F hrnd' h2 x
  linarith

/-! ### Splits, only-DN-or-UP, nearest characterization -/

theorem Rnd_DN_UP_pt_split (F : ℝ → Prop) {x d u : ℝ}
    (Hd : Rnd_DN_pt F x d) (Hu : Rnd_UP_pt F x u)
    {f : ℝ} (Hf : F f) : f ≤ d ∨ u ≤ f := by
  rcases le_or_gt f x with h | h
  · exact Or.inl (Hd.2.2 f Hf h)
  · exact Or.inr (Hu.2.2 f Hf (le_of_lt h))

theorem Only_DN_or_UP (F : ℝ → Prop) {x fd fu f : ℝ}
    (Hd : Rnd_DN_pt F x fd) (Hu : Rnd_UP_pt F x fu)
    (Hf : F f) (hbnds : fd ≤ f ∧ f ≤ fu) : f = fd ∨ f = fu := by
  rcases le_or_gt x f with h | h
  · exact Or.inr (le_antisymm hbnds.2 (Hu.2.2 f Hf h))
  · exact Or.inl (le_antisymm (Hd.2.2 f Hf (le_of_lt h)) hbnds.1)

theorem Rnd_N_pt_DN_or_UP (F : ℝ → Prop) {x f : ℝ}
    (h : Rnd_N_pt F x f) : Rnd_DN_pt F x f ∨ Rnd_UP_pt F x f := by
  obtain ⟨Hf1, Hf2⟩ := h
  rcases le_or_gt x f with hxf | hxf
  · -- x ≤ f: this is an UP rounding
    refine Or.inr ⟨Hf1, hxf, ?_⟩
    intro g Hg Hxg
    have := Hf2 g Hg
    rw [abs_of_nonneg (sub_nonneg.mpr hxf), abs_of_nonneg (sub_nonneg.mpr Hxg)] at this
    linarith
  · -- f < x: this is a DN rounding
    refine Or.inl ⟨Hf1, le_of_lt hxf, ?_⟩
    intro g Hg Hxg
    have := Hf2 g Hg
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxf)),
        abs_of_nonpos (sub_nonpos.mpr Hxg)] at this
    linarith

theorem Rnd_N_pt_DN_or_UP_eq (F : ℝ → Prop) {x fd fu f : ℝ}
    (Hd : Rnd_DN_pt F x fd) (Hu : Rnd_UP_pt F x fu)
    (Hf : Rnd_N_pt F x f) : f = fd ∨ f = fu := by
  rcases Rnd_N_pt_DN_or_UP F Hf with h | h
  · exact Or.inl (Rnd_DN_pt_unique F h Hd)
  · exact Or.inr (Rnd_UP_pt_unique F h Hu)

end LeanFlocq
