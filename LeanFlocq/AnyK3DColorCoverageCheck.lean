/-
# Color coverage check: the canonical form of every census mask is in
the verdict table

THE COVERAGE COMPUTATION of the color track (the analogue of
`AnyK3DCoverage.lean`'s `census_covered`): for every one of the
9,341,248 achievable color profiles in `censusFastC`, its canonical
form (`canonOf` — the min over the 24 `permMask` rotations) is a member
of the 414,079-entry verdict table `colorAllProfs`. One `native_decide`
over the whole color census (canonOf + mergeSort + greedy subsequence
walk), plus the assembly-facing decode `mem_censusFastC_covered`.
-/
import LeanFlocq.AnyK3DColorCoverage
import LeanFlocq.AnyK3DColorComplete

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace AnyK3D

/-- THE COVERAGE COMPUTATION: the canonical forms of all 9,341,248
color census masks form a subsequence of the verdict table's
profiles. -/
theorem color_census_covered :
    sublistOf ((censusFastC.toList.map canonOf).mergeSort (· ≤ ·))
      (colorAllProfs.toList.map (·.1)) = true := by
  native_decide

/-- Every color census mask has a rotation in the verdict table. -/
theorem mem_censusFastC_covered {m : ℕ} (hm : m ∈ censusFastC.toList) :
    ∃ g < 24, permMask g m ∈ colorAllProfs.toList.map (·.1) := by
  obtain ⟨g, hg, hgm⟩ := canonOf_mem m
  refine ⟨g, hg, ?_⟩
  rw [hgm]
  exact mem_of_sublistOf color_census_covered
    (List.mem_mergeSort.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩))

end AnyK3D
