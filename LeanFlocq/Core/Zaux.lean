/-
Port of `flocq/src/Core/Zaux.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

This file currently provides only the `radix` record. Auxiliary integer
lemmas from `Zaux.v` will be ported on demand as later modules require them.
-/

import Mathlib.Data.Int.Init

namespace LeanFlocq

/-- A radix is an integer ≥ 2. -/
structure radix where
  val : ℤ
  prop : 2 ≤ val

namespace radix

instance : Coe radix ℤ := ⟨radix.val⟩

/-- The radix is positive. -/
theorem radix_gt_0 (r : radix) : 0 < r.val := by
  have := r.prop; omega

/-- The radix is greater than 1. -/
theorem radix_gt_1 (r : radix) : 1 < r.val := by
  have := r.prop; omega

/-- The binary radix. -/
def radix2 : radix := ⟨2, by omega⟩

end radix

/-- Conditional integer negation: `cond_Zopp true m = -m`, `false → m`. -/
def cond_Zopp (b : Bool) (m : ℤ) : ℤ := if b then -m else m

@[simp] theorem cond_Zopp_true (m : ℤ) : cond_Zopp true m = -m := rfl
@[simp] theorem cond_Zopp_false (m : ℤ) : cond_Zopp false m = m := rfl

end LeanFlocq
