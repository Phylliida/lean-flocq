/-
Port of `flocq/src/Core/FIX.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Fixed-point format: every value has the same exponent `emin`.
The simplest concrete instance of the generic-format machinery.
-/

import LeanFlocq.Core.Generic_fmt

namespace LeanFlocq

/-- A real `x` is in the FIX format with exponent `emin` if it is the F2R of
some float whose exponent is exactly `emin`. -/
def FIX_format (beta : radix) (emin : ℤ) (x : ℝ) : Prop :=
  ∃ f : float beta, x = F2R f ∧ f.Fexp = emin

/-- The FIX exponent function: constantly `emin`, regardless of input. -/
def FIX_exp (emin : ℤ) : ℤ → ℤ := fun _ => emin

/-- `FIX_exp emin` is a `Valid_exp`. -/
theorem FIX_exp_valid (emin : ℤ) : Valid_exp (FIX_exp emin) := by
  intro k
  refine ⟨?_, ?_⟩
  · -- small regime: emin < k → emin ≤ k
    intro hk
    exact le_of_lt hk
  · -- large regime: stabilization (trivial since FIX_exp is constant)
    intro _
    refine ⟨le_refl _, ?_⟩
    intro _ _
    rfl

/-- Every FIX-format real is in the generic format with `FIX_exp emin`. -/
theorem generic_format_FIX (beta : radix) (emin : ℤ) {x : ℝ}
    (h : FIX_format beta emin x) : generic_format beta (FIX_exp emin) x := by
  obtain ⟨⟨xm, xe⟩, hx, he⟩ := h
  rw [hx]
  apply generic_format_canonical
  -- canonical ⟨xm, xe⟩ : xe = cexp _ _ (F2R ⟨xm, xe⟩) = FIX_exp emin _ = emin
  show xe = cexp beta (FIX_exp emin) (F2R (beta := beta) ⟨xm, xe⟩)
  unfold cexp FIX_exp
  exact he

/-- Every generic-format-with-`FIX_exp` real is in the FIX format. -/
theorem FIX_format_generic (beta : radix) (emin : ℤ) {x : ℝ}
    (h : generic_format beta (FIX_exp emin) x) : FIX_format beta emin x := by
  refine ⟨⟨Ztrunc (scaled_mantissa beta (FIX_exp emin) x),
           cexp beta (FIX_exp emin) x⟩, h, ?_⟩
  -- f.Fexp = cexp = FIX_exp _ = emin
  show cexp beta (FIX_exp emin) x = emin
  unfold cexp FIX_exp
  rfl

/-- The FIX format admits all the abstract round predicates from `Round_pred`. -/
theorem FIX_format_satisfies_any (beta : radix) (emin : ℤ) :
    satisfies_any (FIX_format beta emin) := by
  refine satisfies_any_eq (F1 := generic_format beta (FIX_exp emin)) ?_
    (generic_format_satisfies_any beta (FIX_exp emin) (FIX_exp_valid emin))
  intro x
  exact ⟨FIX_format_generic beta emin, generic_format_FIX beta emin⟩

/-- `FIX_exp` is monotone (trivially — it is constant). -/
theorem FIX_exp_monotone (emin : ℤ) : Monotone_exp (FIX_exp emin) := by
  intro _ _ _; exact le_refl _

end LeanFlocq
