/-
# M4-C4 coverage: every census mask is frontier-dominated up to rotation

The Route-A coverage fact for the M5 assembly: for every mask in the
1,445,865-entry census, some rotation of it (via `permMask`) is either
above a minimal-periodic frontier mask (⟹ periodic by C2 + mono +
transport-back) or below a maximal-empty frontier mask (⟹ empty by C3 +
mono + transport).

The checker recomputes `permMask g m` once per (m, g) and short-circuits
the frontier scans; the decode lemma `covered_iff` lifts the boolean to
the existential shape M5 consumes. One `native_decide` over the whole
census (est. minutes: 34M permMask evaluations + frontier scans).
-/
import Mathlib
import LeanFlocq.AnyK3DCensusFast
import LeanFlocq.AnyK3DPeriodicCerts
import LeanFlocq.AnyK3DTransport

set_option maxRecDepth 100000

namespace AnyK3D

/-- `m` is frontier-covered: some rotation of it is above a
minimal-periodic or below a maximal-empty frontier mask. -/
def covered (m : ℕ) : Bool :=
  (List.range 24).any fun g =>
    let pm := permMask g m
    minPeriodic.toList.any (fun q => q ||| pm == pm) ||
    maxEmpty.toList.any (fun e => pm ||| e == e)

/-- THE COVERAGE COMPUTATION: all 1,445,865 census masks are covered. -/
theorem census_covered : censusFast.toList.all covered = true := by
  native_decide

/-- The existential shape for the assembly. -/
theorem covered_iff {m : ℕ} (h : covered m = true) :
    ∃ g < 24,
      (∃ q ∈ minPeriodic.toList, q ||| permMask g m = permMask g m) ∨
      (∃ e ∈ maxEmpty.toList, permMask g m ||| e = e) := by
  unfold covered at h
  rw [List.any_eq_true] at h
  obtain ⟨g, hg, h⟩ := h
  rw [Bool.or_eq_true, List.any_eq_true, List.any_eq_true] at h
  have hg' := List.mem_range.mp hg
  rcases h with ⟨q, hq, hqq⟩ | ⟨e, he, hee⟩
  · exact ⟨g, hg', Or.inl ⟨q, hq, beq_iff_eq.mp hqq⟩⟩
  · exact ⟨g, hg', Or.inr ⟨e, he, beq_iff_eq.mp hee⟩⟩

/-- Every census member is covered, membership form. -/
theorem mem_census_covered {m : ℕ} (hm : m ∈ censusFast.toList) :
    ∃ g < 24,
      (∃ q ∈ minPeriodic.toList, q ||| permMask g m = permMask g m) ∨
      (∃ e ∈ maxEmpty.toList, permMask g m ||| e = e) :=
  covered_iff ((List.all_eq_true.mp census_covered) m hm)

end AnyK3D
