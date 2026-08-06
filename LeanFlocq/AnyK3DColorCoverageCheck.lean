/-
# Color coverage check: assembly of the 16 chunks + the decode

THE COVERAGE COMPUTATION of the color track (the analogue of
`AnyK3DCoverage.lean`'s `census_covered`), split into 16 chunk modules
(`AnyK3DColorCovChunk{j}.lean`) for parallel builds: every one of the
9,341,248 achievable color profiles in `censusFastC` has a rotation
(`permMask g`) in the 414,079-entry verdict table `colorAllProfs`.

This file: the chunk union (`colorCov_chunk_all`), the list-slice
membership bridge (`mem_slice`), and the assembly-facing decode
`mem_censusFastC_covered`.
-/
import LeanFlocq.AnyK3DColorCovChunk0
import LeanFlocq.AnyK3DColorCovChunk1
import LeanFlocq.AnyK3DColorCovChunk2
import LeanFlocq.AnyK3DColorCovChunk3
import LeanFlocq.AnyK3DColorCovChunk4
import LeanFlocq.AnyK3DColorCovChunk5
import LeanFlocq.AnyK3DColorCovChunk6
import LeanFlocq.AnyK3DColorCovChunk7
import LeanFlocq.AnyK3DColorCovChunk8
import LeanFlocq.AnyK3DColorCovChunk9
import LeanFlocq.AnyK3DColorCovChunk10
import LeanFlocq.AnyK3DColorCovChunk11
import LeanFlocq.AnyK3DColorCovChunk12
import LeanFlocq.AnyK3DColorCovChunk13
import LeanFlocq.AnyK3DColorCovChunk14
import LeanFlocq.AnyK3DColorCovChunk15
import LeanFlocq.AnyK3DColorComplete
import LeanFlocq.AnyK3DColorCensusCount

set_option maxRecDepth 1000000

namespace AnyK3D

/-- All 16 chunks verified. -/
theorem colorCov_chunk_all (j : ℕ) (hj : j < 16) : colorCovChunk j = true := by
  interval_cases j
  · exact colorCov_chunk0
  · exact colorCov_chunk1
  · exact colorCov_chunk2
  · exact colorCov_chunk3
  · exact colorCov_chunk4
  · exact colorCov_chunk5
  · exact colorCov_chunk6
  · exact colorCov_chunk7
  · exact colorCov_chunk8
  · exact colorCov_chunk9
  · exact colorCov_chunk10
  · exact colorCov_chunk11
  · exact colorCov_chunk12
  · exact colorCov_chunk13
  · exact colorCov_chunk14
  · exact colorCov_chunk15

/-- The `i`-th element of a list lies in its `(i / C)`-th size-`C`
slice. -/
theorem mem_slice {α : Type*} (l : List α) (C i : ℕ) (hC : 0 < C)
    (hi : i < l.length) :
    l[i] ∈ ((l.drop (i / C * C)).take C) := by
  rw [List.mem_iff_getElem]
  have h1 : i / C * C ≤ i := Nat.div_mul_le_self i C
  have hkey : i - i / C * C = i % C := by
    have h2 := Nat.div_add_mod i C
    have h5 : i / C * C = C * (i / C) := Nat.mul_comm _ _
    omega
  refine ⟨i - i / C * C, ?_, ?_⟩
  · have h3 : i % C < C := Nat.mod_lt i hC
    have h4 : i % C < l.length - i / C * C := by
      rw [← hkey]
      omega
    simp only [List.length_take, List.length_drop]
    rw [hkey]
    exact lt_min h3 h4
  · rw [List.getElem_take, List.getElem_drop]
    congr 1
    exact Nat.add_sub_of_le h1

/-- Every color census mask has a rotation in the verdict table. -/
theorem mem_censusFastC_covered {m : ℕ} (hm : m ∈ censusFastC.toList) :
    ∃ g < 24, permMask g m ∈ colorAllProfs.toList.map (·.1) := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hm
  have hlen : censusFastC.toList.length = 9341248 := by
    rw [Array.length_toList, census_count_fastC]
  have hCe : colorCovChunkSize = 584000 := rfl
  have hj : i / colorCovChunkSize < 16 := by
    rw [hCe]
    have hi2 : i < 9341248 := by omega
    omega
  have hmem : m ∈ ((censusFastC.toList.drop
      (i / colorCovChunkSize * colorCovChunkSize)).take
      colorCovChunkSize) := by
    have h := mem_slice censusFastC.toList colorCovChunkSize i
      (by rw [hCe]; norm_num) hi
    rwa [hget] at h
  have hcov : colorCovered (colorAllProfs.map (·.1)) m = true :=
    (List.all_eq_true.mp (colorCov_chunk_all _ hj)) m hmem
  simp only [colorCovered, List.any_eq_true, List.mem_range] at hcov
  obtain ⟨g, hg, hgm⟩ := hcov
  refine ⟨g, hg, ?_⟩
  have h2 := binMem_sound hgm
  rwa [Array.toList_map] at h2

end AnyK3D
