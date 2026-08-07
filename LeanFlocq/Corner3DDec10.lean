/-
# The reduction lemma: #10 does not tile ℤ³ (hard direction, T=2)

This file connects the kernel-certified one-edge obstruction
(`Corner3DEdge.edge_unsat`) to the tiling predicate
(`Corner3D.IsTiling`), proving that the chiral T=2 decoration #10
admits no tiling of ℤ³ — the hard direction of the 3D corner chirality
conjecture for #10.

The reduction (`monotile/DESIGN-corner-chirality.md`,
`monotile/corner3d_dimer.py`): if `ℓ` is a tiling by #10, every cube's
pattern is a rotation of #10, hence determines an (A-face, B-face) pair
choice — the faces carrying the absolute-even resp. absolute-odd marked
diagonals — whose axis-cyclic class is `+1` at even cubes and `−1` at
odd cubes. The extraction is a finite fact (`rotToPair_spec`, kernel
`decide` over `2 × 24 × 8`): orientation `o` at cube parity `cp`
reproduces its marks via pair choice `rotToPair cp o`.

Around the lattice edge from `(0,0,0)` to `(0,0,1)` sit the four cubes
`(-1,-1,0), (-1,0,0), (0,-1,0), (0,0,0)` — parities `0,1,1,0`, i.e.
phase `p = 0`. Since `ℓ` is a well-defined function, the four cubes'
marks agree at every shared vertex (`edgeCons_geom`, the 10 shared
vertices of `edgeCons`, kernel `decide` on the lattice arithmetic) — so
their pair choices satisfy `edgeConsistent 0`, contradicting
`Corner3DEdge.edge_unsat`.

Trust base: kernel + `decide` only (`#print axioms` below).
-/
import LeanFlocq.Corner3D
import LeanFlocq.Corner3DEdge

set_option maxRecDepth 1000000
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

namespace Corner3DDec10

open Corner3D Corner3DEdge

/-- The pair-choice extraction table: orientation `o` of #10 at a cube
of parity `cp` shows exactly the marks of pair choice `rotToPair cp o`
(exported from `monotile/corner3d_transfer.py`; `j` is unique per
`(o, cp)`). -/
def rotToPair : Fin 2 → Fin 24 → Fin 12 :=
  ![ ![7, 4, 6, 5, 6, 5, 7, 4, 9, 11, 10, 8, 11, 9, 8, 10, 3, 2, 1, 0, 3, 2, 1, 0],
     ![11, 8, 9, 10, 9, 10, 11, 8, 2, 3, 1, 0, 3, 2, 0, 1, 7, 5, 6, 4, 7, 5, 6, 4] ]

/-- Extraction is correct: the marks of #10 in orientation `o` equal the
pair choice's marks, at both cube parities (the parity flip is built
into the table's second row). -/
theorem rotToPair_spec : ∀ (cp : Fin 2) (o : Fin 24) (e : Fin 8),
    marked cp (rotToPair cp o) e = (dec10 (rot o e) == 1) := by decide

/-- The four cubes around the edge from `(0,0,0)` to `(0,0,1)`. -/
def cubes : Fin 4 → ℤ × ℤ × ℤ := ![(-1, -1, 0), (-1, 0, 0), (0, -1, 0), (0, 0, 0)]

/-- The 10 constraint groups of `edgeCons` really are shared vertices of
these four cubes: all (cube, corner) pairs in a group denote the same
lattice point. (Kernel check of the lattice arithmetic.) -/
theorem edgeCons_geom : ∀ grp ∈ edgeCons, ∀ ie ∈ grp, ∀ ie' ∈ grp,
    cubes ie.1 + cornerVec ie.2 = cubes ie'.1 + cornerVec ie'.2 := by
  decide

/-- `edgeConsistent` with the lets inlined (defeq, for rewriting). -/
theorem edgeConsistent_eq (p : Fin 2) (a₀ a₁ a₂ a₃ : Fin 12) :
    edgeConsistent p a₀ a₁ a₂ a₃ =
      edgeCons.all (groupOK (fun c e =>
        marked ((![p, 1 - p, 1 - p, p] : Fin 4 → Fin 2) c)
          ((![a₀, a₁, a₂, a₃] : Fin 4 → Fin 12) c) e)) := rfl

/-- A constraint group whose marks are all equal passes. -/
theorem groupOK_true {m : Fin 4 → Fin 8 → Bool} {grp : List (Fin 4 × Fin 8)}
    (h : ∀ ie ∈ grp, ∀ ie' ∈ grp, m ie.1 ie.2 = m ie'.1 ie'.2) :
    groupOK m grp = true := by
  induction grp with
  | nil => rfl
  | cons x rest _ =>
    simp only [groupOK]
    rw [List.all_eq_true]
    intro y hy
    show (m y.1 y.2 == m x.1 x.2) = true
    rw [h y (List.Mem.tail _ hy) x (List.Mem.head _)]
    exact beq_self_eq_true _

/-- **The reduction lemma: #10 does not tile ℤ³.** -/
theorem dec10_not_tileable : ¬ ∃ ℓ : Coloring (Fin 2), IsTiling dec10 ℓ := by
  rintro ⟨ℓ, hT⟩
  obtain ⟨o₀, h₀⟩ := hT (-1, -1, 0)
  obtain ⟨o₁, h₁⟩ := hT (-1, 0, 0)
  obtain ⟨o₂, h₂⟩ := hT (0, -1, 0)
  obtain ⟨o₃, h₃⟩ := hT (0, 0, 0)
  -- The four cubes' marks, read two ways.
  have k₀ : ∀ e, marked 0 (rotToPair 0 o₀) e
      = (ℓ ((-1, -1, 0) + cornerVec e) == 1) := fun e =>
    (rotToPair_spec 0 o₀ e).trans (congrArg (· == 1)
      (by simpa [cubePat, Function.comp_apply] using (congrFun h₀ e).symm))
  have k₁ : ∀ e, marked 1 (rotToPair 1 o₁) e
      = (ℓ ((-1, 0, 0) + cornerVec e) == 1) := fun e =>
    (rotToPair_spec 1 o₁ e).trans (congrArg (· == 1)
      (by simpa [cubePat, Function.comp_apply] using (congrFun h₁ e).symm))
  have k₂ : ∀ e, marked 1 (rotToPair 1 o₂) e
      = (ℓ ((0, -1, 0) + cornerVec e) == 1) := fun e =>
    (rotToPair_spec 1 o₂ e).trans (congrArg (· == 1)
      (by simpa [cubePat, Function.comp_apply] using (congrFun h₂ e).symm))
  have k₃ : ∀ e, marked 0 (rotToPair 0 o₃) e
      = (ℓ ((0, 0, 0) + cornerVec e) == 1) := fun e =>
    (rotToPair_spec 0 o₃ e).trans (congrArg (· == 1)
      (by simpa [cubePat, Function.comp_apply] using (congrFun h₃ e).symm))
  -- The pair choices satisfy the edge system's agreements.
  have htrue : edgeConsistent 0 (rotToPair 0 o₀) (rotToPair 1 o₁)
      (rotToPair 1 o₂) (rotToPair 0 o₃) = true := by
    rw [edgeConsistent_eq]
    -- identify the mark function with the ℓ-read one
    have hm : (fun c e => marked ((![(0 : Fin 2), 1 - 0, 1 - 0, 0] : Fin 4 → Fin 2) c)
        ((![rotToPair 0 o₀, rotToPair 1 o₁, rotToPair 1 o₂,
            rotToPair 0 o₃] : Fin 4 → Fin 12) c) e)
        = (fun c e => (ℓ (cubes c + cornerVec e) == 1)) := by
      funext c
      funext e
      fin_cases c <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_succ, Fin.isValue, cubes, Fin.reduceSub]
      · exact k₀ e
      · exact k₁ e
      · exact k₂ e
      · exact k₃ e
    rw [hm, List.all_eq_true]
    intro grp hg
    exact groupOK_true fun ie hi ie' hi' =>
      congrArg (fun v => (ℓ v == 1)) (edgeCons_geom grp hg ie hi ie' hi')
  -- … contradicting the kernel-certified obstruction.
  have hfalse := Corner3DEdge.edge_unsat 0 (rotToPair 0 o₀) (rotToPair 1 o₁)
    (rotToPair 1 o₂) (rotToPair 0 o₃)
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

end Corner3DDec10

#print axioms Corner3DDec10.dec10_not_tileable
