/-
Port of `flocq/src/Core/Round_NE.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Round to nearest, ties to even — IEEE 754's default rounding mode.
Builds on `Znearest` with the choice function "round up at a tie iff
the floor is odd," which produces an even canonical mantissa.
-/

import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.Ulp

namespace LeanFlocq

/-- The round-to-nearest-even integer rounder: at a tie, pick the side that
makes the result even. Concretely, the choice returns `true` (= round up to
ceil) when `⌊x⌋` is odd. -/
noncomputable def ZnearestE : ℝ → ℤ :=
  Znearest (fun n => decide (¬ Even n))

/-- `round_NE β fexp x` is the round-to-nearest-even of `x` in the given format. -/
noncomputable def round_NE (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  round beta fexp ZnearestE x

/-- The "even canonical mantissa" tie-breaking property: `f` is the F2R of a
canonical float whose mantissa is even. -/
def NE_prop (beta : radix) (fexp : ℤ → ℤ) (_x f : ℝ) : Prop :=
  ∃ g : float beta, f = F2R g ∧ canonical beta fexp g ∧ Even g.Fnum

/-- `f` is *the* round-to-nearest-even of `x` in the format `F`: it rounds
to the nearest, and at a tie it picks the even one (or there's no tie at all). -/
def Rnd_NE_pt (beta : radix) (fexp : ℤ → ℤ) (x f : ℝ) : Prop :=
  Rnd_NG_pt (generic_format beta fexp) (NE_prop beta fexp) x f

/-- The round-NE function lands at a `Rnd_N_pt` (without yet checking the
parity tie-breaking). Immediate from `round_N_pt` with the round-up-on-odd-floor
choice. -/
theorem round_NE_pt_N (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp) (x : ℝ) :
    Rnd_N_pt (generic_format beta fexp) x (round_NE beta fexp x) := by
  unfold round_NE ZnearestE
  exact round_N_pt beta fexp hValid _ x

/-! ### `Exists_NE`: the typeclass enabling round-to-nearest-even

The DN_UP parity theorem requires either `β` is odd, or `fexp` "doesn't get
stuck" in any narrow ways: in the small regime it stabilizes at one
exponent, and in the large regime it grows enough that the canonical
mantissa picks up extra factors of `β`. This is captured by `Exists_NE`. -/
class Exists_NE (beta : radix) (fexp : ℤ → ℤ) : Prop where
  cond : Odd beta.val ∨
    ∀ e : ℤ,
      (fexp e < e → fexp (e + 1) < e) ∧
      (e ≤ fexp e → fexp (fexp e + 1) = fexp e)

/-- The DN/UP parity property restricted to positive `x ∉ F`: the canonical
up-rounded mantissa flips parity from the down-rounded one. -/
def DN_UP_parity_pos_prop (beta : radix) (fexp : ℤ → ℤ) : Prop :=
  ∀ (x : ℝ) (xd xu : float beta),
    0 < x → ¬ generic_format beta fexp x →
    canonical beta fexp xd → canonical beta fexp xu →
    F2R xd = round beta fexp (fun y : ℝ => ⌊y⌋) x →
    F2R xu = round beta fexp (fun y : ℝ => ⌈y⌉) x →
    (Even xu.Fnum ↔ ¬ Even xd.Fnum)

/-- The DN/UP parity property for general `x ∉ F`. -/
def DN_UP_parity_prop (beta : radix) (fexp : ℤ → ℤ) : Prop :=
  ∀ (x : ℝ) (xd xu : float beta),
    ¬ generic_format beta fexp x →
    canonical beta fexp xd → canonical beta fexp xu →
    F2R xd = round beta fexp (fun y : ℝ => ⌊y⌋) x →
    F2R xu = round beta fexp (fun y : ℝ => ⌈y⌉) x →
    (Even xu.Fnum ↔ ¬ Even xd.Fnum)

/-- General DN/UP parity reduces to the positive case via opp-symmetry on
canonical floats. -/
theorem DN_UP_parity_aux (beta : radix) (fexp : ℤ → ℤ)
    (Hpos : DN_UP_parity_pos_prop beta fexp) : DN_UP_parity_prop beta fexp := by
  intro x xd xu Hfx Hd Hu Hxd Hxu
  rcases lt_trichotomy 0 x with hx | hx | hx
  · -- 0 < x: direct application.
    exact Hpos x xd xu hx Hfx Hd Hu Hxd Hxu
  · -- x = 0: contradicts ¬ generic_format x.
    exfalso; apply Hfx
    rw [← hx]; exact generic_format_0 beta fexp
  · -- x < 0: apply Hpos at -x with negated mantissas.
    have hx' : 0 < -x := by linarith
    obtain ⟨md, ed⟩ := xd
    obtain ⟨mu, eu⟩ := xu
    -- The canonical of (-md, ed) at (-x): F2R = -F2R xd = round_DN(-x) via round_UP_opp.
    have F_neg_x_n_F : ¬ generic_format beta fexp (-x) := by
      intro h
      apply Hfx
      rw [show x = -(-x) from (neg_neg x).symm]
      exact generic_format_opp beta fexp h
    have Hd_neg : canonical beta fexp ⟨-md, ed⟩ := canonical_opp beta fexp md ed Hd
    have Hu_neg : canonical beta fexp ⟨-mu, eu⟩ := canonical_opp beta fexp mu eu Hu
    have h_round_DN_neg : round beta fexp (fun y : ℝ => ⌊y⌋) (-x)
        = -(round beta fexp (fun y : ℝ => ⌈y⌉) x) := round_DN_opp beta fexp x
    have h_round_UP_neg : round beta fexp (fun y : ℝ => ⌈y⌉) (-x)
        = -(round beta fexp (fun y : ℝ => ⌊y⌋) x) := round_UP_opp beta fexp x
    have Hxd' : F2R (beta := beta) ⟨-mu, eu⟩
        = round beta fexp (fun y : ℝ => ⌊y⌋) (-x) := by
      rw [F2R_Zopp, h_round_DN_neg, ← Hxu]
    have Hxu' : F2R (beta := beta) ⟨-md, ed⟩
        = round beta fexp (fun y : ℝ => ⌈y⌉) (-x) := by
      rw [F2R_Zopp, h_round_UP_neg, ← Hxd]
    have h_par := Hpos (-x) ⟨-mu, eu⟩ ⟨-md, ed⟩ hx' F_neg_x_n_F Hu_neg Hd_neg Hxd' Hxu'
    -- h_par : Even (-md) ↔ ¬ Even (-mu); want Even mu ↔ ¬ Even md.
    show Even mu ↔ ¬ Even md
    have h_even_neg_mu : Even (-mu) ↔ Even mu := by simp
    have h_even_neg_md : Even (-md) ↔ Even md := by simp
    rw [h_even_neg_mu, h_even_neg_md] at h_par
    tauto

end LeanFlocq
