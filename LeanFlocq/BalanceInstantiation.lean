/-
Generic engines reducing the two remaining Coverage obligations
(`hcert`, `hgeo`) to concrete, decidable data about the arena.

After this file, completing the monotile closure in Lean needs only:
  • the concrete arena (24 rotations as perms of Fin 54, the `pairs`
    tables, the 33 patterns + their torus certificates) entered as
    Lean `def`s (mechanical data, exportable from the Python), and
  • the finite geometric facts those engines consume, checked by
    `decide` / `native_decide`.
No further *mathematics* remains for this layer — the ∀-decoration
reasoning is all proven here, sorry-free.

`admitsPeriodic_of_cert` / `hcert_of_provider`: a periodic certificate
tiling (a v-periodic ℤ³ map whose every adjacency pair lies in S)
yields `AdmitsPeriodic` for every decoration realizing S — this is
exactly `hcert`, modulo providing the (data-level) certificates.

`face_cancel_of_zip`: if the interface pair-list of an axis is the zip
of the two touching faces' point-lists, complementary matching forces
the two face height-sums to cancel — this is `FaceDecomp.cancx/y/z`,
the one non-trivial fact in `hgeo`. `zip_add_sum` is its combinatorial
core.
-/
import LeanFlocq.Coverage

namespace MonotileCoverage

/-- A decoration realizing `S` admits the certified periodic tiling. -/
theorem admitsPeriodic_of_cert
    (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair) (S : Pattern) {dec : Dec}
    (T : Cell → Fin 24) (v : Cell) (hv : v ≠ (0, 0, 0))
    (hper : ∀ c, T (cadd c v) = T c)
    (hsub : ∀ c (ax : Fin 3), ∀ p ∈ pairs ax (T c) (T (shift c ax)), p ∈ S)
    (hreal : Realizes dec S) :
    AdmitsPeriodic pairs dec := by
  refine ⟨T, ?_, v, hv, hper⟩
  intro c ax p hp
  exact hreal p (hsub c ax p hp)

/-- `hcert` from a (decoration-independent) certificate provider: one
periodic tiling per pattern whose adjacencies stay inside the pattern. -/
theorem hcert_of_provider
    (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair) (patterns : List Pattern)
    (prov : ∀ S ∈ patterns, ∃ (T : Cell → Fin 24) (v : Cell),
      v ≠ (0, 0, 0) ∧ (∀ c, T (cadd c v) = T c) ∧
      (∀ c (ax : Fin 3), ∀ p ∈ pairs ax (T c) (T (shift c ax)), p ∈ S)) :
    ∀ S ∈ patterns, ∀ dec : Dec, Realizes dec S → AdmitsPeriodic pairs dec := by
  intro S hS dec hreal
  obtain ⟨T, v, hv, hper, hsub⟩ := prov S hS
  exact admitsPeriodic_of_cert pairs S T v hv hper hsub hreal

/-- Combinatorial core: a zipped sum of `f`-first and `g`-second splits. -/
theorem zip_add_sum (f g : Fin 54 → ℤ) :
    ∀ (A B : List (Fin 54)), A.length = B.length →
      ((A.zip B).map (fun p => f p.1 + g p.2)).sum
        = (A.map f).sum + (B.map g).sum := by
  intro A
  induction A with
  | nil =>
    intro B hB
    cases B with
    | nil => simp
    | cons b B => simp at hB
  | cons a A ih =>
    intro B hB
    cases B with
    | nil => simp at hB
    | cons b B =>
      have hlen' : A.length = B.length := by simpa using hB
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [ih B hlen']
      ring

/-- `FaceDecomp.cancx`-style fact: matching across an axis forces the
two touching faces' height-sums to cancel, when the interface pairs are
the zip of the faces' point-lists. -/
theorem face_cancel_of_zip
    (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair) (dec : Dec)
    (ax : Fin 3) (o1 o2 : Fin 24) (A B : List (Fin 54))
    (hlen : A.length = B.length)
    (hzip : pairs ax o1 o2 = A.zip B)
    (hcompat : Compat pairs dec ax o1 o2) :
    (A.map dec).sum + (B.map dec).sum = 0 := by
  have h1 : (A.map dec).sum + (B.map dec).sum
      = ((pairs ax o1 o2).map (fun p => dec p.1 + dec p.2)).sum := by
    rw [hzip, zip_add_sum dec dec A B hlen]
  rw [h1]
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact hcompat p hp

end MonotileCoverage

#print axioms MonotileCoverage.admitsPeriodic_of_cert
#print axioms MonotileCoverage.hcert_of_provider
#print axioms MonotileCoverage.zip_add_sum
#print axioms MonotileCoverage.face_cancel_of_zip
