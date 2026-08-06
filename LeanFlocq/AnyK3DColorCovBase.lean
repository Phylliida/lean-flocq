/-
# Color coverage check, base: binary search + chunk scaffolding

The checker half of the color coverage computation. `colorCovChunk j`
is the per-slice check — each of the 16 slices of the 9,341,248-entry
color census gets its own `native_decide` in
`AnyK3DColorCovChunk{j}.lean` (parallel builds; a single-module run was
measured at ~4.5 h single-threaded). The decode
(`mem_censusFastC_covered`) lives in `AnyK3DColorCoverageCheck.lean`.

The claim (externally pre-validated on all 9,341,248 profiles by
`monotile/check_color_coverage_full.py`, zero misses): every achievable
color profile has a rotation (`permMask g`) in the 414,079-entry
verdict table.
-/
import Mathlib
import LeanFlocq.AnyK3DColorCensus
import LeanFlocq.AnyK3DColorVerdictData
import LeanFlocq.AnyK3DTransport

set_option maxRecDepth 1000000

namespace AnyK3D

/-! ## binMem: binary search with a soundness lemma (no sortedness
needed for the found direction) -/

/-- Binary search over an array, fueled by the window size (fuel =
`a.size` is always enough: each step strictly shrinks `hi - lo`). -/
def binMemGo (a : Array ℕ) (x lo hi fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if hi ≤ lo then false
    else
      let mid := (lo + hi) / 2
      let v := a.getD mid 0
      if x == v then true
      else if x < v then binMemGo a x lo mid f
      else binMemGo a x (mid + 1) hi f

/-- Binary search membership check (complete when `a` is sorted
ascending — which the coverage computation itself confirms). -/
def binMem (a : Array ℕ) (x : ℕ) : Bool := binMemGo a x 0 a.size a.size

theorem binMemGo_sound (a : Array ℕ) (x : ℕ) :
    ∀ (lo hi fuel : ℕ), hi ≤ a.size → binMemGo a x lo hi fuel = true →
      x ∈ a.toList := by
  intro lo hi fuel
  induction fuel generalizing lo hi with
  | zero => intro hhi h; simp [binMemGo] at h
  | succ f ih =>
    intro hhi h
    simp only [binMemGo] at h
    split at h
    · simp at h
    · rename_i hlo
      split at h
      · rename_i heq
        have hlt : lo < hi := Nat.lt_of_not_ge hlo
        have hmid : (lo + hi) / 2 < a.size := by
          have : (lo + hi) / 2 < hi := by omega
          omega
        rw [beq_iff_eq] at heq
        rw [heq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid]
        exact Array.getElem_mem_toList hmid
      · split at h
        · have hle : (lo + hi) / 2 ≤ hi := by omega
          exact ih lo ((lo + hi) / 2) (le_trans hle hhi) h
        · exact ih ((lo + hi) / 2 + 1) hi hhi h

theorem binMem_sound {a : Array ℕ} {x : ℕ} (h : binMem a x = true) :
    x ∈ a.toList :=
  binMemGo_sound a x 0 a.size a.size (Nat.le_refl _) h

/-! ## The per-chunk coverage check -/

/-- The rotation-membership check: some rotation of `m` is a
verdict-table profile (early exit on hit). -/
def colorCovered (T : Array ℕ) (m : ℕ) : Bool :=
  (List.range 24).any fun g => binMem T (permMask g m)

/-- Census slice size for the chunked coverage check (16 chunks). -/
def colorCovChunkSize : ℕ := 584000

/-- The chunk check: every census mask in slice `j` has a rotation in
the verdict table. -/
def colorCovChunk (j : ℕ) : Bool :=
  ((censusFastC.toList.drop (j * colorCovChunkSize)).take
    colorCovChunkSize).all (colorCovered (colorAllProfs.map (·.1)))

end AnyK3D
