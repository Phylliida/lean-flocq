/-
Lean port of Coq Flocq's `Prop/Double_rounding.v` — conditions for innocuous
double rounding.

Double rounding occurs when a value is first rounded at one precision, then
rounded again to a coarser target precision. In general this can give a
different answer than rounding directly. This file establishes sufficient
conditions under which double rounding is equivalent to single rounding.

Original Coq is © 2014–2018 Sylvie Boldo, Guillaume Melquiond, and Pierre Roux.
LGPL v3+.

The file is large (~4500 Coq lines). Top-level structure:

- **Core mid-rounding theorems** (~600 Coq lines): `round_round_lt_mid` and
  `round_round_gt_mid` families. Show that double rounding agrees with direct
  rounding when `x` is "far enough" from the midpoint.
- **Multiplication** (~160 lines): `round_round_mult` and format-specific
  instantiations (FLX, FLT, FTZ).
- **Plus/Minus** (~1760 lines, the largest): `round_round_plus`,
  `round_round_minus`, with FLX/FLT/FTZ instantiations and a separate
  `radix_ge_3` track.
- **Square root** (~870 lines): `round_round_sqrt` family.
- **Division** (~1100 lines): `round_round_div` family with a long bridge
  lemma `round_round_eq_mid_beta_even` (~97 lines).

The `round_N_odd` theorem from `Prop/Round_odd.lean` is the primary
underlying tool used throughout.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.Round_NE
import LeanFlocq.Core.Ulp
import LeanFlocq.Core.FLX
import LeanFlocq.Core.FLT
import LeanFlocq.Core.FTZ
import LeanFlocq.Calc.Operations
import LeanFlocq.Prop.Round_odd

namespace LeanFlocq

/-! ## Definitions -/

/-- The double-rounding agrees with the single-rounding: rounding `x` at the
finer format `fexp2` and then at the target format `fexp1` gives the same
result as rounding directly at `fexp1`. -/
def round_round_eq (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    (choice1 choice2 : ℤ → Bool) (x : ℝ) : Prop :=
  round beta fexp1 (Znearest choice1) (round beta fexp2 (Znearest choice2) x)
    = round beta fexp1 (Znearest choice1) x

/-- The midpoint between `round_DN x` and `round_UP x`, expressed via the
round-down witness plus half a ulp. -/
noncomputable def midp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  round beta fexp (fun y : ℝ => ⌊y⌋) x + (1 : ℝ) / 2 * ulp beta fexp x

/-- The midpoint expressed via the round-up witness minus half a ulp.
Equal to `midp` when `x ∉ F`. -/
noncomputable def midp' (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  round beta fexp (fun y : ℝ => ⌈y⌉) x - (1 : ℝ) / 2 * ulp beta fexp x

end LeanFlocq
