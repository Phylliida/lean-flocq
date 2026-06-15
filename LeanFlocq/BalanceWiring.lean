/-
Wiring the proven Balance Law (BalanceLaw.balance_of_faces) into the
Coverage development's `balance_law`, through a geometric interface.

`FaceDecomp` packages the genuinely geometric data of one rotation
orbit: for each orientation o, the orbit's height-sum on each of the six
faces (`F ax side o`), together with the three facts that connect it to
the arena —
  • cell:   the six face-sums add to the orbit total (faces partition
            the orbit + rotation invariance of the total);
  • cancx/y/z:  matching across an axis (`Compat`) forces the touching
            faces' sums to cancel (the interface pairs are the
            coinciding face points);
  • hM:     each face-sum is bounded.
None of these is "balance"; balance (σ = 0) is the CONCLUSION, supplied
by the n³-box telescoping limit already proven in BalanceLaw.

`balance_law_of_faceDecomp` turns a FaceDecomp + a tiling into balance,
with NO new axioms. `coverage_wired` then re-derives the full coverage
theorem with `balance_law` discharged — the only remaining inputs are
the assumed UNSAT, the (geometric, decidable) FaceDecomp provider, and
the per-pattern periodic certificate.
-/
import LeanFlocq.Coverage
import LeanFlocq.BalanceLaw

namespace MonotileCoverage

open MonotileBalance

/-- Per-orbit face-sum data and the geometric facts relating it to the
arena's matching rules. -/
structure FaceDecomp (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair)
    (orb : List (Fin 54)) (dec : Dec) where
  F : Fin 3 → Bool → Fin 24 → ℤ
  M : ℤ
  hM : ∀ (ax : Fin 3) (s : Bool) (o : Fin 24), |F ax s o| ≤ M
  cell : ∀ o : Fin 24,
    F 0 true o + F 0 false o + F 1 true o + F 1 false o
      + F 2 true o + F 2 false o = (orb.map dec).sum
  cancx : ∀ o1 o2, Compat pairs dec 0 o1 o2 → F 0 true o1 + F 0 false o2 = 0
  cancy : ∀ o1 o2, Compat pairs dec 1 o1 o2 → F 1 true o1 + F 1 false o2 = 0
  cancz : ∀ o1 o2, Compat pairs dec 2 o1 o2 → F 2 true o1 + F 2 false o2 = 0

/-- Shift reduction (definitional). -/
theorem shift0 (c : Cell) : shift c 0 = (c.1 + 1, c.2.1, c.2.2) := rfl
theorem shift1 (c : Cell) : shift c 1 = (c.1, c.2.1 + 1, c.2.2) := rfl
theorem shift2 (c : Cell) : shift c 2 = (c.1, c.2.1, c.2.2 + 1) := rfl

/-- **Wiring lemma.** A face decomposition plus a ℤ³ tiling yield
balance, via the proven box-telescoping limit. No `sorry`. -/
theorem balance_law_of_faceDecomp
    (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair)
    {orb : List (Fin 54)} {dec : Dec}
    (T : Cell → Fin 24) (hT : ValidSpace pairs dec T)
    (fd : FaceDecomp pairs orb dec) :
    (orb.map dec).sum = 0 := by
  apply MonotileBalance.balance_of_faces (M := fd.M)
    (fx := fun a b c => fd.F 0 true (T (a, b, c)))
    (gx := fun a b c => fd.F 0 false (T (a, b, c)))
    (fy := fun a b c => fd.F 1 true (T (a, b, c)))
    (gy := fun a b c => fd.F 1 false (T (a, b, c)))
    (fz := fun a b c => fd.F 2 true (T (a, b, c)))
    (gz := fun a b c => fd.F 2 false (T (a, b, c)))
  constructor
  · intro a b c; exact fd.cell (T (a, b, c))
  · intro a b c; exact fd.cancx _ _ (hT (a, b, c) 0)
  · intro a b c; exact fd.cancy _ _ (hT (a, b, c) 1)
  · intro a b c; exact fd.cancz _ _ (hT (a, b, c) 2)
  · intro a b c; exact fd.hM 0 false (T (a, b, c))
  · intro a b c; exact fd.hM 1 false (T (a, b, c))
  · intro a b c; exact fd.hM 2 false (T (a, b, c))

/-- **Coverage, with Balance Law discharged.** Identical conclusion to
`coverage`, but instead of the sorried `balance_law` it consumes a
geometric face-decomposition provider `hgeo` (decidable for the concrete
arena) and proves balance through the verified telescoping limit. The
only remaining black box is `hcert` (per-pattern periodic certificate). -/
theorem coverage_wired
    (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair)
    (orbits : List (List (Fin 54))) (patterns : List Pattern)
    (hunsat : SearchUnsat pairs orbits patterns)
    (hgeo : ∀ orb ∈ orbits, ∀ dec, FaceDecomp pairs orb dec)
    (hcert : ∀ S ∈ patterns, ∀ dec, Realizes dec S → AdmitsPeriodic pairs dec)
    (dec : Dec) : TilesSpace pairs dec → AdmitsPeriodic pairs dec := by
  intro hspace
  by_contra hnp
  have hbal : Balanced orbits dec := by
    intro orb hmem
    obtain ⟨T, hT⟩ := hspace
    exact balance_law_of_faceDecomp pairs T hT (hgeo orb hmem dec)
  exact hunsat ⟨dec, hbal, box_restriction pairs dec hspace,
    fun S hS hreal => hnp (hcert S hS dec hreal)⟩

/-- No strongly-aperiodic monotile, with balance discharged. -/
theorem no_einstein_wired
    (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair)
    (orbits : List (List (Fin 54))) (patterns : List Pattern)
    (hunsat : SearchUnsat pairs orbits patterns)
    (hgeo : ∀ orb ∈ orbits, ∀ dec, FaceDecomp pairs orb dec)
    (hcert : ∀ S ∈ patterns, ∀ dec, Realizes dec S → AdmitsPeriodic pairs dec)
    (dec : Dec) : ¬ Einstein pairs dec := by
  rintro ⟨hspace, hnp⟩
  exact hnp (coverage_wired pairs orbits patterns hunsat hgeo hcert dec hspace)

end MonotileCoverage

#print axioms MonotileCoverage.balance_law_of_faceDecomp
#print axioms MonotileCoverage.coverage_wired
