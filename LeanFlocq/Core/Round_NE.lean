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

end LeanFlocq
