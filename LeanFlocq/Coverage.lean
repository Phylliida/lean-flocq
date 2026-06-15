/-
Coverage / sufficiency of the monotile arena-2 search.

Goal (Danielle's framing): ASSUMING the Python encoding is faithful and
the run genuinely returned UNSAT, prove — machine-checked — that the
finite search has covered the WHOLE space: no bigger box and no further
patterns are needed; there is no aperiodic cube monotile in the family.

The two trusted inputs are bundled into ONE hypothesis, `SearchUnsat`:
"no balanced decoration tiles the 4³ box while avoiding all blocked
patterns." (Faithfulness of this predicate to the Python CNF = "code is
right"; its emptiness = "the UNSAT run is right".)

From that single hypothesis, `coverage` derives the infinite conclusion
(every ℤ³-tiler admits a periodic tiling) and `no_einstein` concludes
no strongly-aperiodic monotile exists — both fully proven here. They
rest on exactly three lemmas:
  • box_restriction  — every space-tiler tiles the box   (PROVEN: a box
                       tiling is a logical weakening of a space tiling;
                       this is precisely why no LARGER box is needed —
                       we only ever use the necessary direction)
  • balance_law      — every space-tiler is balanced     (obligation 1,
                       the telescoping/boundary argument; `sorry`)
  • pattern_periodic — realizing a blocked pattern ⟹ a periodic tiling
                       (obligation 2, per-pattern torus certificate;
                       `sorry`)

Geometry (interface point-pairs, orbits, the 33 patterns) is left as
parameters; instantiating them with the concrete K=3 cube data and
discharging the two obligations for that data is the remaining work.
`#print axioms` at the bottom exposes the current dependency on
`sorryAx` so the holes are auditable.
-/
import Mathlib

namespace MonotileCoverage

abbrev Dec := Fin 54 → Int           -- ±1 heights at the 54 surface pts
abbrev Pair := Fin 54 × Fin 54
abbrev Pattern := List Pair
abbrev Cell := Int × Int × Int       -- a unit cell of ℤ³

def cadd (c v : Cell) : Cell := (c.1 + v.1, c.2.1 + v.2.1, c.2.2 + v.2.2)

def shift (c : Cell) (ax : Fin 3) : Cell :=
  match ax.val with
  | 0 => (c.1 + 1, c.2.1, c.2.2)
  | 1 => (c.1, c.2.1 + 1, c.2.2)
  | _ => (c.1, c.2.1, c.2.2 + 1)

/-- A 4×4×4 window of ℤ³ (the synthesizer's detector box). -/
def InBox (c : Cell) : Prop :=
  0 ≤ c.1 ∧ c.1 < 4 ∧ 0 ≤ c.2.1 ∧ c.2.1 < 4 ∧ 0 ≤ c.2.2 ∧ c.2.2 < 4

/-- Analytic heart of the Balance Law. After summing presented heights
over an n³ box (interior faces cancel by complementarity, boundary is
O(n²)) and dividing by n², a rotation orbit-sum `k` satisfies
`n·|k| ≤ C` for every `n`; an integer with that property is zero.
PROVEN — this is the "infinite ⟹ finite" core that forces balance. -/
theorem balance_core (k C : ℤ) (h : ∀ n : ℕ, (n : ℤ) * |k| ≤ C) :
    k = 0 := by
  by_contra hk
  have hk1 : (1 : ℤ) ≤ |k| := by have := abs_pos.mpr hk; omega
  have hC : (0 : ℤ) ≤ C := by have := h 0; simpa using this
  have key : ∀ n : ℕ, (n : ℤ) ≤ C := by
    intro n
    calc (n : ℤ) = (n : ℤ) * 1 := by ring
      _ ≤ (n : ℤ) * |k| := mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ ≤ C := h n
  have hbig := key (C.toNat + 1)
  have hCnat : ((C.toNat : ℤ)) = C := Int.toNat_of_nonneg hC
  push_cast at hbig
  omega

section
variable (pairs : Fin 3 → Fin 24 → Fin 24 → List Pair)
variable (orbits : List (List (Fin 54)))
variable (patterns : List Pattern)

/-- Two coinciding surface points complement (bump meets dent). -/
def Compl (dec : Dec) (p : Pair) : Prop := dec p.1 + dec p.2 = 0

/-- Orientations o1,o2 may sit face-to-face along axis `ax`: every one
of the (up to 9) coinciding point-pairs complements. -/
def Compat (dec : Dec) (ax : Fin 3) (o1 o2 : Fin 24) : Prop :=
  ∀ p ∈ pairs ax o1 o2, Compl dec p

/-- `dec` realizes a pattern: all its forced pairs complement. -/
def Realizes (dec : Dec) (S : Pattern) : Prop := ∀ p ∈ S, Compl dec p

/-- A tiling of all of ℤ³ by the 24 oriented copies, every adjacency
matching. -/
def ValidSpace (dec : Dec) (T : Cell → Fin 24) : Prop :=
  ∀ c ax, Compat pairs dec ax (T c) (T (shift c ax))

def TilesSpace (dec : Dec) : Prop := ∃ T, ValidSpace pairs dec T

/-- A box tiling: matching required ONLY on in-box adjacencies. As a
predicate on a ℤ³-indexed map this is a strict weakening of
`ValidSpace`, which is exactly why the box check is a sound necessary
condition needing no larger window. -/
def ValidBox (dec : Dec) (T : Cell → Fin 24) : Prop :=
  ∀ c ax, InBox c → InBox (shift c ax) →
    Compat pairs dec ax (T c) (T (shift c ax))

def TilesBox (dec : Dec) : Prop := ∃ T, ValidBox pairs dec T

/-- Balanced: each rotation orbit of surface points carries height-sum
zero (the synthesizer's cardinality pruning). -/
def Balanced (dec : Dec) : Prop := ∀ orb ∈ orbits, (orb.map dec).sum = 0

/-- Admits SOME tiling invariant under a nonzero translation — i.e. is
NOT strongly aperiodic. (The certificates give full lattices; a single
nonzero period already refutes einstein-hood.) -/
def AdmitsPeriodic (dec : Dec) : Prop :=
  ∃ T, ValidSpace pairs dec T ∧
    ∃ v : Cell, v ≠ (0, 0, 0) ∧ ∀ c, T (cadd c v) = T c

/-- A strongly-aperiodic monotile: tiles space, but no tiling has a
period. -/
def Einstein (dec : Dec) : Prop :=
  TilesSpace pairs dec ∧ ¬ AdmitsPeriodic pairs dec

/-- **No larger box needed.** A space tiling, viewed on the box, is a
box tiling — `ValidBox` is just `ValidSpace` with the hypotheses
dropped. PROVEN. -/
theorem box_restriction (dec : Dec) :
    TilesSpace pairs dec → TilesBox pairs dec := by
  rintro ⟨T, hT⟩
  exact ⟨T, fun c ax _ _ => hT c ax⟩

/-- **Obligation 1** (substantive, infinite→finite): every ℤ³-tiler is
balanced. Telescoping the presented-height sum over a growing box:
internal faces cancel by complementarity, the boundary is O(n²), so the
per-tile orbit-sum (scaling like n³) must vanish. TODO. -/
theorem balance_law (dec : Dec) :
    TilesSpace pairs dec → Balanced orbits dec := by
  sorry

/-- **Obligation 2** (per-pattern certificate): a decoration realizing a
blocked pattern admits that pattern's certified periodic tiling. Each
pattern ships with an explicit lattice B and quotient grid; the grid
repeated B-periodically is a valid tiling whose adjacencies demand
exactly the realized pairs. TODO (finite `decide` per pattern once the
geometry is instantiated). -/
theorem pattern_periodic (S : Pattern) (hS : S ∈ patterns) (dec : Dec) :
    Realizes dec S → AdmitsPeriodic pairs dec := by
  sorry

/-- The bundled trusted input: the search predicate is empty.
"= Python encodes this faithfully" ⊗ "the run returned UNSAT". -/
def SearchUnsat : Prop :=
  ¬ ∃ dec : Dec, Balanced orbits dec ∧ TilesBox pairs dec ∧
      ∀ S ∈ patterns, ¬ Realizes dec S

/-- **Coverage.** From the single UNSAT hypothesis: every decoration
that tiles ℤ³ admits a periodic tiling. The finite 4³ search over
balanced decorations, together with the finite pattern list, exhausts
the entire infinite family — nothing larger is required. -/
theorem coverage (hunsat : SearchUnsat pairs orbits patterns)
    (dec : Dec) : TilesSpace pairs dec → AdmitsPeriodic pairs dec := by
  intro hspace
  by_contra hnp
  exact hunsat ⟨dec, balance_law pairs orbits dec hspace,
                box_restriction pairs dec hspace,
                fun S hS hreal =>
                  hnp (pattern_periodic pairs patterns S hS dec hreal)⟩

/-- **No einstein.** No decoration in the family is a strongly-aperiodic
monotile. -/
theorem no_einstein (hunsat : SearchUnsat pairs orbits patterns)
    (dec : Dec) : ¬ Einstein pairs dec := by
  rintro ⟨hspace, hnp⟩
  exact hnp (coverage pairs orbits patterns hunsat dec hspace)

end

#print axioms coverage
#print axioms no_einstein

end MonotileCoverage
