/-
# The one-edge obstruction: kernel certificate for the 4-cube UNSAT

The hard direction of the 3D corner chirality conjecture for the chiral
T=2 pair #10/#11 reduces (see `monotile/DESIGN-corner-chirality.md`,
`monotile/HANDOFF.md`) to a single finite fact, verified here in the
Lean kernel.

**The reduced model** (exact for #10, `monotile/corner3d_dimer.py`):
each cube of a tiling picks an ordered pair of adjacent faces
`(A-face, B-face)` — the faces carrying its absolute-even resp.
absolute-odd marked corner diagonals — with axis-cyclic class `+1` at
even cubes and `−1` at odd cubes (the parity flip; 12 choices per
cube). A cube's mark at a corner is: even corners are marked iff they
lie on the A-face, odd corners iff they lie on the B-face (with A/B
swapped at odd cubes). Vertex glue: cubes incident to a lattice vertex
agree on its mark.

**The edge system** (`monotile/corner3d_edge.py`): the four cubes
around one lattice edge — positions (1,1), (1,2), (2,1), (2,2) of one
layer, around the edge from vertex (2,2,0) to (2,2,1) — with mark
agreement at every lattice vertex shared by ≥ 2 of them: the two 4-wise
edge endpoints plus 8 pairwise vertices (4 per end plane), 10
agreements in total. The cube parities are `(p, 1-p, 1-p, p)` for the
layer phase `p ∈ Fin 2`.

**`edge_unsat`: no assignment of the 12 allowed face pairs to the 4
cubes satisfies all 10 agreements** — for both phases. Any #10-tiling
of ℤ³ would restrict to such a system around every lattice edge
(vertex glue implies the agreements), so #10 (and its mirror #11) does
not tile ℤ³.

Tables are exported from the Python source of truth
(`monotile/corner3d_transfer.py`: `PAIRS`, `FV`); the constraints are
derived from the lattice geometry (and match `corner3d_edge.py`'s
`SHARED`). The certificate is pure kernel `decide` over `Fin` types
(Mathlib is imported only for the `![…]` vector notation).

Trust base: Lean kernel + `decide` only — all three theorems depend on
`propext` alone (`pairTab_complete` also `Quot.sound`), verified by
`#print axioms` below. NOTE: `set_option … in` breaks next to doc
comments, and `maxHeartbeats 0` resets to the default — hence the
file-level heartbeat bump for the 41472-case kernel check (~6 min).
-/

import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 6400000

namespace Corner3DEdge

/-- Faces of the cube: index `2a + s` = (axis `a`, side `s`), matching
`FACES` in `monotile/corner3d_transfer.py`. -/
abbrev Face := Fin 6

/-- Corner-on-face membership: `faceTab e f` iff corner `e` (x-fastest
indexing, `e = x + 2y + 4z`) lies on face `f` (exported from `FV`). -/
def faceTab : Fin 8 → Face → Bool :=
  ![ ![true, false, true, false, true, false],
     ![false, true, true, false, true, false],
     ![true, false, false, true, true, false],
     ![false, true, false, true, true, false],
     ![true, false, true, false, false, true],
     ![false, true, true, false, false, true],
     ![true, false, false, true, false, true],
     ![false, true, false, true, false, true] ]

/-- The 12 allowed (A-face, B-face) pairs per cube parity: adjacent
faces with axis-cyclic class `+1` for even cubes (row 0), `−1` for odd
cubes (row 1). Exported from `PAIRS` in `monotile/corner3d_transfer.py`
(the #10-orbit pair sets). -/
def pairTab : Fin 2 → Fin 12 → Face × Face :=
  ![ ![ (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (2, 5),
        (3, 4), (3, 5), (4, 0), (4, 1), (5, 0), (5, 1) ],
     ![ (0, 4), (0, 5), (1, 4), (1, 5), (2, 0), (2, 1),
        (3, 0), (3, 1), (4, 2), (4, 3), (5, 2), (5, 3) ] ]

/-- Parity of a corner: `(x + y + z) mod 2`. -/
def cornerPar : Fin 8 → Fin 2 := ![0, 1, 1, 0, 1, 0, 0, 1]

/-- The mark (color-1 bit) of a cube of parity `cp` with pair choice `j`
at its corner `e`: even corners are marked iff on the A-face, odd
corners iff on the B-face — with A/B swapped at odd cubes (the absolute
parity flip, cf. `marked_by` in `monotile/corner3d_transfer.py`). -/
def marked (cp : Fin 2) (j : Fin 12) (e : Fin 8) : Bool :=
  let (f, g) := pairTab cp j
  let ef := if cp = 0 then f else g
  let of := if cp = 0 then g else f
  if cornerPar e = 0 then faceTab e ef else faceTab e of

/-- The 10 mark-agreement constraints of the edge system: groups of
(cube, corner) pairs whose marks must all be equal (the lattice
vertices shared by ≥ 2 of the 4 cubes, both end planes; derived from
the lattice geometry — matches `SHARED` in `monotile/corner3d_edge.py`
for the edge from (2,2,0) to (2,2,1)). -/
def edgeCons : List (List (Fin 4 × Fin 8)) :=
  [ [(0, 2), (1, 0)],
    [(0, 1), (2, 0)],
    [(0, 3), (1, 1), (2, 2), (3, 0)],
    [(1, 3), (3, 2)],
    [(2, 3), (3, 1)],
    [(0, 6), (1, 4)],
    [(0, 5), (2, 4)],
    [(0, 7), (1, 5), (2, 6), (3, 4)],
    [(1, 7), (3, 6)],
    [(2, 7), (3, 5)] ]

/-- All marks of a constraint group agree. -/
def groupOK (m : Fin 4 → Fin 8 → Bool) : List (Fin 4 × Fin 8) → Bool
  | [] => true
  | (c0, e0) :: rest => rest.all fun (c, e) => m c e == m c0 e0

/-- The edge system with layer phase `p` and pair choices
`a₀ a₁ a₂ a₃` (cubes (1,1), (1,2), (2,1), (2,2) — parities
`p, 1-p, 1-p, p`): all 10 agreements hold. -/
def edgeConsistent (p : Fin 2) (a₀ a₁ a₂ a₃ : Fin 12) : Bool :=
  let cubePar : Fin 4 → Fin 2 := ![p, 1 - p, 1 - p, p]
  let choice : Fin 4 → Fin 12 := ![a₀, a₁, a₂, a₃]
  let m : Fin 4 → Fin 8 → Bool := fun c e => marked (cubePar c) (choice c) e
  edgeCons.all (groupOK m)

/-- **The one-edge obstruction.** The four cubes around a lattice edge
cannot simultaneously satisfy the class constraint and all vertex-mark
agreements — for both layer phases. Kernel check of all
`2 × 12⁴ = 41472` assignments against the 10 agreements (matches the
solver-free brute force in `monotile/corner3d_edge.py`: 0 survivors). -/
theorem edge_unsat : ∀ (p : Fin 2) (a₀ a₁ a₂ a₃ : Fin 12),
    edgeConsistent p a₀ a₁ a₂ a₃ = false := by decide

/-! ## Sanity / reduction support: the pair tables are exactly the
class-±1 adjacent face pairs (needed by the reduction lemma, N2). -/

/-- The axis of a face (table — computational `Fin` literals with
embedded proof terms block kernel `decide`). -/
def faceAxis : Face → Fin 3 := ![0, 0, 1, 1, 2, 2]

/-- The cyclic sign of an ordered axis pair: `0` = same axis (invalid),
`1` = cyclic-positive `(x,y), (y,z), (z,x)`, `2` = cyclic-negative
(cf. `AXSIGN` in `monotile/corner3d_transfer.py`). -/
def axSignTab : Fin 3 → Fin 3 → Fin 3 :=
  ![ ![0, 1, 2],
     ![2, 0, 1],
     ![1, 2, 0] ]

/-- `classOk cp f g` iff `f, g` are adjacent (different axes) with
axis-cyclic class `+1` when `cp = 0` and `−1` when `cp = 1`. -/
def classOk (cp : Fin 2) (f g : Face) : Bool :=
  axSignTab (faceAxis f) (faceAxis g) == (if cp = 0 then 1 else 2)

/-- Every table entry is a valid class-`±1` adjacent pair. -/
theorem pairTab_valid : ∀ (cp : Fin 2) (j : Fin 12),
    classOk cp (pairTab cp j).1 (pairTab cp j).2 := by decide

/-- …and the table is complete: every valid pair occurs. -/
theorem pairTab_complete : ∀ (cp : Fin 2) (f g : Face),
    classOk cp f g = true → ∃ j : Fin 12, pairTab cp j = (f, g) := by
  decide

end Corner3DEdge

#print axioms Corner3DEdge.edge_unsat
#print axioms Corner3DEdge.pairTab_valid
#print axioms Corner3DEdge.pairTab_complete
