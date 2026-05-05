/-
Port of `flocq/src/Core/Round_pred.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Properties of rounding predicates: monotonicity, uniqueness, reflexivity,
idempotence, behaviour under negation, and characterizations of round-to-nearest.

Skipped here (require real-number completeness machinery):
`round_val_of_pred`, `round_fun_of_pred`.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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

/-! ### Round-to-nearest: symmetry and reflexivity -/

theorem Rnd_N_pt_opp_inv (F : ℝ → Prop) (HF : ∀ x, F x → F (-x))
    {x f : ℝ} (h : Rnd_N_pt F (-x) (-f)) : Rnd_N_pt F x f := by
  refine ⟨?_, ?_⟩
  · have : F (-(-f)) := HF (-f) h.1
    rwa [neg_neg] at this
  · intro g Hg
    have hopp : F (-g) := HF g Hg
    have := h.2 (-g) hopp
    have e1 : -f - -x = -(f - x) := by ring
    have e2 : -g - -x = -(g - x) := by ring
    rw [e1, e2, abs_neg, abs_neg] at this
    exact this

theorem Rnd_N_pt_refl (F : ℝ → Prop) {x : ℝ} (hx : F x) : Rnd_N_pt F x x := by
  refine ⟨hx, ?_⟩
  intro g _
  rw [sub_self, abs_zero]
  exact abs_nonneg _

theorem Rnd_N_pt_idempotent (F : ℝ → Prop) {x f : ℝ}
    (h : Rnd_N_pt F x f) (hx : F x) : f = x := by
  have hbound : |f - x| ≤ |x - x| := h.2 x hx
  rw [sub_self, abs_zero] at hbound
  have habs : |f - x| ≤ 0 := hbound
  have : f - x = 0 := abs_nonpos_iff.mp habs
  linarith

theorem Rnd_N_pt_0 (F : ℝ → Prop) (HF : F 0) : Rnd_N_pt F 0 0 := by
  refine ⟨HF, ?_⟩
  intro g _
  rw [sub_zero, sub_zero, abs_zero]
  exact abs_nonneg _

/-! ### Round-to-nearest is monotone -/

/-- If `f` is the nearest in `F` to `x` and `g` is the nearest to `y`, then
`x < y` implies `f ≤ g`. -/
theorem Rnd_N_pt_monotone (F : ℝ → Prop) {x y f g : ℝ}
    (hf : Rnd_N_pt F x f) (hg : Rnd_N_pt F y g) (hxy : x < y) : f ≤ g := by
  by_contra hgf
  push_neg at hgf
  have Hfgx : |f - x| ≤ |g - x| := hf.2 g hg.1
  have Hgfy : |g - y| ≤ |f - y| := hg.2 f hf.1
  rcases le_or_gt x g with hxg | hgx
  · -- x ≤ g < f
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ f - x),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ g - x)] at Hfgx
    linarith
  · rcases le_or_gt f y with hfy | hyf
    · -- g < x < y and f ≤ y
      rw [abs_of_nonpos (by linarith : g - y ≤ 0),
          abs_of_nonpos (by linarith : f - y ≤ 0)] at Hgfy
      linarith
    · -- g < x < y < f
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ f - x),
          abs_of_nonpos (by linarith : g - x ≤ 0)] at Hfgx
      rw [abs_of_nonpos (by linarith : g - y ≤ 0),
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ f - y)] at Hgfy
      linarith

/-- Round-to-nearest is unique when there is no tie. -/
theorem Rnd_N_pt_unique (F : ℝ → Prop) {x d u f1 f2 : ℝ}
    (Hd : Rnd_DN_pt F x d) (Hu : Rnd_UP_pt F x u) (Hdu : x - d ≠ u - x)
    (Hf1 : Rnd_N_pt F x f1) (Hf2 : Rnd_N_pt F x f2) : f1 = f2 := by
  -- A strict < between two N-rounded values leads to contradiction.
  have strict : ∀ a b : ℝ, Rnd_N_pt F x a → Rnd_N_pt F x b → a < b → False := by
    intro a b Ha Hb hab
    rcases Rnd_N_pt_DN_or_UP F Ha with Hda | Hua
    · rcases Rnd_N_pt_DN_or_UP F Hb with Hdb | Hub
      · -- both DN → equal, contradicts a < b
        exact absurd (Rnd_DN_pt_unique F Hda Hdb) (ne_of_lt hab)
      · -- a = d (DN), b = u (UP); equal distances would force the tie
        have ha_eq_d : a = d := Rnd_DN_pt_unique F Hda Hd
        have hb_eq_u : b = u := Rnd_UP_pt_unique F Hub Hu
        have h1 : |a - x| ≤ |b - x| := Ha.2 b Hb.1
        have h2 : |b - x| ≤ |a - x| := Hb.2 a Ha.1
        have heq : |a - x| = |b - x| := le_antisymm h1 h2
        have hax : a - x ≤ 0 := sub_nonpos.mpr Hda.2.1
        have hbx : 0 ≤ b - x := sub_nonneg.mpr Hub.2.1
        rw [abs_of_nonpos hax, abs_of_nonneg hbx] at heq
        have heq2 : x - a = b - x := by linarith
        rw [ha_eq_d, hb_eq_u] at heq2
        exact Hdu heq2
    · rcases Rnd_N_pt_DN_or_UP F Hb with Hdb | Hub
      · -- a is UP (a ≥ x), b is DN (b ≤ x); but a < b would force x ≤ a ≤ b ≤ x then a < b impossible
        exact absurd hab (not_lt.mpr (le_trans Hdb.2.1 Hua.2.1))
      · -- both UP → equal, contradicts a < b
        exact absurd (Rnd_UP_pt_unique F Hua Hub) (ne_of_lt hab)
  rcases lt_trichotomy f1 f2 with h | h | h
  · exact (strict f1 f2 Hf1 Hf2 h).elim
  · exact h
  · exact (strict f2 f1 Hf2 Hf1 h).elim

/-! ### Sign preservation under nearest rounding -/

theorem Rnd_N_pt_ge_0 (F : ℝ → Prop) (HF : F 0)
    {x f : ℝ} (hx : 0 ≤ x) (h : Rnd_N_pt F x f) : 0 ≤ f := by
  rcases hx.lt_or_eq with hlt | heq
  · exact Rnd_N_pt_monotone F (Rnd_N_pt_0 F HF) h hlt
  · have hx_eq : x = 0 := heq.symm
    have hF_x : F x := hx_eq ▸ HF
    have hf_eq : f = x := Rnd_N_pt_idempotent F h hF_x
    linarith

theorem Rnd_N_pt_le_0 (F : ℝ → Prop) (HF : F 0)
    {x f : ℝ} (hx : x ≤ 0) (h : Rnd_N_pt F x f) : f ≤ 0 := by
  rcases hx.lt_or_eq with hlt | heq
  · exact Rnd_N_pt_monotone F h (Rnd_N_pt_0 F HF) hlt
  · have hx_eq : x = 0 := heq
    have hF_x : F x := hx_eq ▸ HF
    have hf_eq : f = x := Rnd_N_pt_idempotent F h hF_x
    linarith

theorem Rnd_N_pt_abs (F : ℝ → Prop) (HF0 : F 0) (HF : ∀ x, F x → F (-x))
    {x f : ℝ} (Hxf : Rnd_N_pt F x f) : Rnd_N_pt F |x| |f| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (Rnd_N_pt_ge_0 F HF0 hx Hxf)]
    exact Hxf
  · rw [abs_of_neg hx,
        abs_of_nonpos (Rnd_N_pt_le_0 F HF0 (le_of_lt hx) Hxf)]
    apply Rnd_N_pt_opp_inv F HF
    rw [neg_neg, neg_neg]
    exact Hxf

end LeanFlocq
