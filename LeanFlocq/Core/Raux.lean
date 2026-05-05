/-
Port of `flocq/src/Core/Raux.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

This file currently provides only `bpow`. The bulk of `Raux.v` (auxiliary
real-number lemmas) will be ported on demand.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import LeanFlocq.Core.Zaux

namespace LeanFlocq

open radix

/-- Power of the radix: `bpow beta e = beta^e` as a real number. -/
noncomputable def bpow (beta : radix) (e : ℤ) : ℝ :=
  (beta.val : ℝ) ^ e

/-- The radix is positive in ℝ. -/
theorem radix_pos (r : radix) : (0 : ℝ) < (r.val : ℝ) := by
  exact_mod_cast r.radix_gt_0

end LeanFlocq
