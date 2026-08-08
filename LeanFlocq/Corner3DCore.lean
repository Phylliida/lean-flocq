/-
# The generic core-certificate reduction lemma

One decoration-INDEPENDENT theorem subsuming the whole hard-direction
machinery of the 3D corner chirality conjecture
(`monotile/DESIGN-corner-chirality.md` §3b):

**`not_tileable_of_core`** — if the decoration's rotation patterns
admit no consistent assignment on a finite "core" of cubes around a
lattice vertex (colors agreeing at all shared vertices), then the
decoration does not tile ℤ³. A tiling restricts to such an assignment:
`IsTiling` gives an orientation per cube, the orientation's pattern is
in the table (`hcover`), and shared vertices agree because the coloring
is a function (`hgeom` says the constraint corners really are the same
lattice point). So `hunsat` — a finite check over `Fin k → Fin n` — is
impossible.

The certificate data per decoration (pattern table `tab`, cube
selection `sel`, constraint table `cons`) is exported from
`monotile/corner3d_vertexprobe.py`; all three hypotheses are kernel
`decide`. The geometry (`vcubes`, `cons`) is decoration-independent —
only `tab`, `hcover`, `hunsat` vary per decoration.

Validated here on #10 and #11 (the chiral T=2 pair): 4-cube edge cores,
12 patterns, 20 constraints — re-deriving `dec10_not_tileable` /
`dec11_not_tileable` (originally `Corner3DDec10.lean`) through the
generic route. For T=3 the same theorem takes the 102 edge cores and
the 30 vertex-core certificates (see the design doc).

Trust base: kernel + `decide` only (`#print axioms` below).
-/
import LeanFlocq.Corner3D

set_option maxRecDepth 1000000
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

namespace Corner3DCore

open Corner3D

/-- The 8 cubes around the vertex `(0,0,0)`: `vcubes i = -cornerVec i`
(matches `CUBES` in `monotile/corner3d_vertexprobe.py`). -/
def vcubes : Fin 8 → ℤ × ℤ × ℤ :=
  ![ (0, 0, 0), (-1, 0, 0), (0, -1, 0), (-1, -1, 0),
     (0, 0, -1), (-1, 0, -1), (0, -1, -1), (-1, -1, -1) ]

/-- A core constraint: the patterns of selected cubes `a` and `b` must
agree at corners `ei`, `ej` respectively (which `hgeom` certifies to be
the same lattice vertex). -/
abbrev CoreCon (k : ℕ) := Fin k × Fin k × Fin 8 × Fin 8

/-- **The generic reduction lemma.** Given
* `tab`: the decoration's rotation patterns (`hcover`: complete),
* `sel`: the core's cubes (indices into `vcubes`),
* `cons`: shared-vertex constraints among them (`hgeom`: sound),
* `hunsat`: no assignment of patterns to the core cubes satisfies all
  constraints,
the decoration does not tile ℤ³. -/
theorem not_tileable_of_core {α : Type*} [DecidableEq α] {d : Fin 8 → α}
    {k n m : ℕ}
    (tab : Fin n → Fin 8 → α) (sel : Fin k → Fin 8) (cons : Fin m → CoreCon k)
    (hcover : ∀ o : Fin 24, ∃ j : Fin n, tab j = d ∘ rot o)
    (hgeom : ∀ t : Fin m,
        vcubes (sel (cons t).1) + cornerVec (cons t).2.2.1
          = vcubes (sel (cons t).2.1) + cornerVec (cons t).2.2.2)
    (hunsat : ∀ choice : Fin k → Fin n, ∃ t : Fin m,
        tab (choice (cons t).1) (cons t).2.2.1
          ≠ tab (choice (cons t).2.1) (cons t).2.2.2) :
    ¬ ∃ ℓ : Coloring α, IsTiling d ℓ := by
  rintro ⟨ℓ, hT⟩
  have key : ∀ a : Fin k, ∃ o : Fin 24,
      cubePat ℓ (vcubes (sel a)) = d ∘ rot o := fun a => hT _
  choose o ho using key
  have cov : ∀ a : Fin k, ∃ j : Fin n, tab j = d ∘ rot (o a) :=
    fun a => hcover (o a)
  choose j hj using cov
  obtain ⟨t, hne⟩ := hunsat j
  apply hne
  have e1 : tab (j (cons t).1) (cons t).2.2.1
      = ℓ (vcubes (sel (cons t).1) + cornerVec (cons t).2.2.1) := by
    have h1 := congrFun (hj (cons t).1) (cons t).2.2.1
    have h2 := congrFun (ho (cons t).1) (cons t).2.2.1
    simp only [Function.comp_apply] at h1
    simp only [cubePat, Function.comp_apply] at h2
    rw [h1, h2]
  have e2 : tab (j (cons t).2.1) (cons t).2.2.2
      = ℓ (vcubes (sel (cons t).2.1) + cornerVec (cons t).2.2.2) := by
    have h1 := congrFun (hj (cons t).2.1) (cons t).2.2.2
    have h2 := congrFun (ho (cons t).2.1) (cons t).2.2.2
    simp only [Function.comp_apply] at h1
    simp only [cubePat, Function.comp_apply] at h2
    rw [h1, h2]
  rw [e1, e2, hgeom t]

/-! ## The shared edge-core geometry (decoration-independent) -/

/-- The 4 layer cubes around the edge from `(0,0,0)` to `(0,0,1)`. -/
def sel4 : Fin 4 → Fin 8 := ![0, 1, 2, 3]

/-- The 20 shared-vertex constraints among them (exported from
`PAIR_SHARED` in `monotile/corner3d_vertexprobe.py`). -/
def consEdge : Fin 20 → CoreCon 4 :=
  ![ (0, 1, 0, 1), (0, 1, 2, 3), (0, 1, 4, 5), (0, 1, 6, 7),
     (0, 2, 0, 2), (0, 2, 1, 3), (0, 2, 4, 6), (0, 2, 5, 7),
     (0, 3, 0, 3), (0, 3, 4, 7),
     (1, 2, 1, 2), (1, 2, 5, 6),
     (1, 3, 0, 2), (1, 3, 1, 3), (1, 3, 4, 6), (1, 3, 5, 7),
     (2, 3, 0, 1), (2, 3, 2, 3), (2, 3, 4, 5), (2, 3, 6, 7) ]

/-- The edge-core constraints are geometrically sound (kernel check of
the ℤ³ arithmetic; decoration-independent, reusable for every T). -/
theorem consEdge_geom : ∀ t : Fin 20,
    vcubes (sel4 (consEdge t).1) + cornerVec (consEdge t).2.2.1
      = vcubes (sel4 (consEdge t).2.1) + cornerVec (consEdge t).2.2.2 := by
  decide

/-- Converting a nested-`Fin` UNSAT certificate into the function form
(the kernel `decide` enumerates nested `Fin` quantifiers much faster
than `Fin 4 → Fin n`). -/
theorem unsat4_of_nested {n m : ℕ} {tab : Fin n → Fin 8 → Fin 2}
    {cons : Fin m → CoreCon 4}
    (h : ∀ c₀ c₁ c₂ c₃ : Fin n, ∃ t : Fin m,
      tab (![c₀, c₁, c₂, c₃] (cons t).1) (cons t).2.2.1
        ≠ tab (![c₀, c₁, c₂, c₃] (cons t).2.1) (cons t).2.2.2) :
    ∀ choice : Fin 4 → Fin n, ∃ t : Fin m,
      tab (choice (cons t).1) (cons t).2.2.1
        ≠ tab (choice (cons t).2.1) (cons t).2.2.2 := by
  intro choice
  have h' := h (choice 0) (choice 1) (choice 2) (choice 3)
  have heq : (![choice 0, choice 1, choice 2, choice 3] : Fin 4 → Fin n)
      = choice := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h'

/-! ## #10 and #11 through the generic route -/

/-- #10's 12 rotation patterns (exported from
`monotile/corner3d_vertexprobe.py`). -/
def tab10 : Fin 12 → Fin 8 → Fin 2 :=
  ![ ![0, 0, 1, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 1, 1, 1],
     ![1, 0, 1, 1, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 1, 1],
     ![1, 1, 0, 1, 0, 0, 0, 1], ![1, 0, 0, 0, 1, 1, 0, 1],
     ![1, 1, 1, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 1, 0, 1, 0],
     ![0, 1, 0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0, 1, 1],
     ![0, 1, 1, 1, 0, 0, 1, 0], ![0, 0, 1, 1, 0, 1, 0, 1] ]

/-- #11's 12 rotation patterns. -/
def tab11 : Fin 12 → Fin 8 → Fin 2 :=
  ![ ![1, 1, 0, 1, 1, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 1, 1],
     ![1, 0, 1, 0, 1, 1, 0, 0], ![0, 0, 1, 0, 0, 1, 1, 1],
     ![0, 0, 0, 1, 1, 1, 0, 1], ![0, 0, 1, 1, 1, 0, 1, 0],
     ![1, 1, 0, 0, 0, 1, 0, 1], ![0, 1, 1, 1, 0, 1, 0, 0],
     ![0, 1, 0, 1, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 0, 1, 0],
     ![0, 1, 0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 0, 0, 0, 1] ]

theorem tab10_cover : ∀ o : Fin 24, ∃ j : Fin 12,
    tab10 j = dec10 ∘ rot o := by decide

theorem tab11_cover : ∀ o : Fin 24, ∃ j : Fin 12,
    tab11 j = dec11 ∘ rot o := by decide

theorem consEdge_unsat10 : ∀ choice : Fin 4 → Fin 12, ∃ t : Fin 20,
    tab10 (choice (consEdge t).1) (consEdge t).2.2.1
      ≠ tab10 (choice (consEdge t).2.1) (consEdge t).2.2.2 :=
  unsat4_of_nested (cons := consEdge) (tab := tab10) (by decide)

theorem consEdge_unsat11 : ∀ choice : Fin 4 → Fin 12, ∃ t : Fin 20,
    tab11 (choice (consEdge t).1) (consEdge t).2.2.1
      ≠ tab11 (choice (consEdge t).2.1) (consEdge t).2.2.2 :=
  unsat4_of_nested (cons := consEdge) (tab := tab11) (by decide)

/-- **#10 does not tile ℤ³** — through the generic core lemma. -/
theorem dec10_not_tileable' :
    ¬ ∃ ℓ : Coloring (Fin 2), IsTiling dec10 ℓ :=
  not_tileable_of_core tab10 sel4 consEdge
    tab10_cover consEdge_geom consEdge_unsat10

/-- **#11 does not tile ℤ³** — through the generic core lemma. -/
theorem dec11_not_tileable' :
    ¬ ∃ ℓ : Coloring (Fin 2), IsTiling dec11 ℓ :=
  not_tileable_of_core tab11 sel4 consEdge
    tab11_cover consEdge_geom consEdge_unsat11

end Corner3DCore

#print axioms Corner3DCore.not_tileable_of_core
#print axioms Corner3DCore.dec10_not_tileable'
#print axioms Corner3DCore.dec11_not_tileable'
