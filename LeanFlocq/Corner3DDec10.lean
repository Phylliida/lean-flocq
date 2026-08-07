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
set_option linter.unnecessarySeqFocus false

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

/-! ## Rotation/mirror transport

Tileability is invariant under the cube group: a tiling by `d ∘ rot o`
(resp. `d ∘ mirror`) pulls back along the corresponding affine map of
ℤ³ to a tiling by `d`. The 24 affine maps are exported from
`monotile/corner3d.py` (`SIG`): `cornerVec (rot o p) = M_o·cornerVec p
+ t_o` with `M_o` a signed permutation matrix. -/

/-- Linear part of rotation `o` (rows of the signed permutation matrix). -/
def rotLinTab : Fin 24 → Fin 3 → Fin 3 → ℤ :=
  ![ ![ ![1, 0, 0], ![0, 1, 0], ![0, 0, 1] ],
     ![ ![1, 0, 0], ![0, -1, 0], ![0, 0, -1] ],
     ![ ![ -1, 0, 0], ![0, 1, 0], ![0, 0, -1] ],
     ![ ![ -1, 0, 0], ![0, -1, 0], ![0, 0, 1] ],
     ![ ![1, 0, 0], ![0, 0, -1], ![0, 1, 0] ],
     ![ ![1, 0, 0], ![0, 0, 1], ![0, -1, 0] ],
     ![ ![ -1, 0, 0], ![0, 0, 1], ![0, 1, 0] ],
     ![ ![ -1, 0, 0], ![0, 0, -1], ![0, -1, 0] ],
     ![ ![0, 1, 0], ![1, 0, 0], ![0, 0, -1] ],
     ![ ![0, -1, 0], ![1, 0, 0], ![0, 0, 1] ],
     ![ ![0, 1, 0], ![ -1, 0, 0], ![0, 0, 1] ],
     ![ ![0, -1, 0], ![ -1, 0, 0], ![0, 0, -1] ],
     ![ ![0, 1, 0], ![0, 0, 1], ![1, 0, 0] ],
     ![ ![0, -1, 0], ![0, 0, -1], ![1, 0, 0] ],
     ![ ![0, 1, 0], ![0, 0, -1], ![ -1, 0, 0] ],
     ![ ![0, -1, 0], ![0, 0, 1], ![ -1, 0, 0] ],
     ![ ![0, 0, 1], ![1, 0, 0], ![0, 1, 0] ],
     ![ ![0, 0, -1], ![1, 0, 0], ![0, -1, 0] ],
     ![ ![0, 0, -1], ![ -1, 0, 0], ![0, 1, 0] ],
     ![ ![0, 0, 1], ![ -1, 0, 0], ![0, -1, 0] ],
     ![ ![0, 0, -1], ![0, 1, 0], ![1, 0, 0] ],
     ![ ![0, 0, 1], ![0, -1, 0], ![1, 0, 0] ],
     ![ ![0, 0, 1], ![0, 1, 0], ![ -1, 0, 0] ],
     ![ ![0, 0, -1], ![0, -1, 0], ![ -1, 0, 0] ] ]

/-- Translation part of rotation `o` (the maps fix the unit cube, so
`t_o ∈ {0,1}³`). -/
def rotShiftTab : Fin 24 → Fin 3 → ℤ :=
  ![ ![0, 0, 0], ![0, 1, 1], ![1, 0, 1], ![1, 1, 0],
     ![0, 1, 0], ![0, 0, 1], ![1, 0, 0], ![1, 1, 1],
     ![0, 0, 1], ![1, 0, 0], ![0, 1, 0], ![1, 1, 1],
     ![0, 0, 0], ![1, 1, 0], ![0, 1, 1], ![1, 0, 1],
     ![0, 0, 0], ![1, 0, 1], ![1, 1, 0], ![0, 1, 1],
     ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1] ]

/-- The linear part applied to a lattice point. -/
def rotLin (o : Fin 24) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (rotLinTab o 0 0 * v.1 + rotLinTab o 0 1 * v.2.1 + rotLinTab o 0 2 * v.2.2,
   rotLinTab o 1 0 * v.1 + rotLinTab o 1 1 * v.2.1 + rotLinTab o 1 2 * v.2.2,
   rotLinTab o 2 0 * v.1 + rotLinTab o 2 1 * v.2.1 + rotLinTab o 2 2 * v.2.2)

/-- The affine rotation map on ℤ³. -/
def rotAff (o : Fin 24) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  ((rotLin o v).1 + rotShiftTab o 0,
   (rotLin o v).2.1 + rotShiftTab o 1,
   (rotLin o v).2.2 + rotShiftTab o 2)

/-- The tables implement the corner permutations (kernel check). -/
theorem cornerVec_rotAff : ∀ (o : Fin 24) (p : Fin 8),
    cornerVec (rot o p) = rotAff o (cornerVec p) := by decide

theorem rotLin_add (o : Fin 24) (v w : ℤ × ℤ × ℤ) :
    rotLin o (v + w) = rotLin o v + rotLin o w := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [rotLin] <;> ring

theorem rotAff_add (o : Fin 24) (c e : ℤ × ℤ × ℤ) :
    rotAff o (c + e) = rotLin o c + rotAff o e := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [rotAff, rotLin_add] <;> ring

/-- Pulling a coloring back along the affine rotation reads the rotated
pattern on the linearly-moved cube. -/
theorem cubePat_comp_rotAff (ℓ : Coloring (Fin 2)) (o : Fin 24)
    (c : ℤ × ℤ × ℤ) (p : Fin 8) :
    cubePat (fun v => ℓ (rotAff o v)) c p
      = cubePat ℓ (rotLin o c) (rot o p) := by
  simp only [cubePat, Function.comp_apply]
  congr 1
  rw [cornerVec_rotAff]
  exact rotAff_add o c (cornerVec p)

/-- Rotation transport: a tiling by `d ∘ rot o` pulls back to a tiling
by `d`. -/
theorem isTiling_of_comp_rot {d : Fin 8 → Fin 2} {o : Fin 24}
    {ℓ : Coloring (Fin 2)} (h : IsTiling (d ∘ rot o) ℓ) :
    IsTiling d (fun v => ℓ (rotAff o v)) := by
  intro c
  obtain ⟨o', ho'⟩ := h (rotLin o c)
  refine ⟨rotCompTab (rotCompTab o o') o, ?_⟩
  funext p
  rw [cubePat_comp_rotAff]
  simp only [Function.comp_apply]
  have e := congrFun ho' (rot o p)
  simp only [Function.comp_apply] at e
  rw [e, ← rot_comp_tab, ← rot_comp_tab]

/-- Linear/affine parts of the mirror `x ↦ 1 − x`. -/
def mirrorLin (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (-v.1, v.2.1, v.2.2)
def mirrorAff (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (1 - v.1, v.2.1, v.2.2)

theorem mirrorAff_add (c e : ℤ × ℤ × ℤ) :
    mirrorAff (c + e) = mirrorLin c + mirrorAff e := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [mirrorAff, mirrorLin] <;> ring

theorem cornerVec_mirrorAff : ∀ p : Fin 8,
    cornerVec (mirror p) = mirrorAff (cornerVec p) := by decide

theorem cubePat_comp_mirrorAff (ℓ : Coloring (Fin 2)) (c : ℤ × ℤ × ℤ)
    (p : Fin 8) :
    cubePat (fun v => ℓ (mirrorAff v)) c p
      = cubePat ℓ (mirrorLin c) (mirror p) := by
  simp only [cubePat, Function.comp_apply]
  congr 1
  rw [cornerVec_mirrorAff]
  exact mirrorAff_add c (cornerVec p)

/-- Mirror transport: a tiling by `d ∘ mirror` pulls back to a tiling
by `d`. -/
theorem isTiling_of_comp_mirror {d : Fin 8 → Fin 2} {ℓ : Coloring (Fin 2)}
    (h : IsTiling (d ∘ mirror) ℓ) :
    IsTiling d (fun v => ℓ (mirrorAff v)) := by
  intro c
  obtain ⟨o', ho'⟩ := h (mirrorLin c)
  obtain ⟨r, hr⟩ := mirror_conj o'
  refine ⟨r, ?_⟩
  funext p
  rw [cubePat_comp_mirrorAff]
  simp only [Function.comp_apply]
  have e := congrFun ho' (mirror p)
  have e2 := congrFun hr p
  simp only [Function.comp_apply] at e e2
  rw [e, e2]

/-! ## #11 and the T=2 assembly -/

/-- #11 is the mirror of #10, up to rotation (witness 12, cf.
`dec10_mirror_dec11`). -/
theorem dec11_eq : dec11 = (dec10 ∘ mirror) ∘ rot 12 := by decide

/-- **#11 does not tile ℤ³** (mirror-transported from #10). -/
theorem dec11_not_tileable :
    ¬ ∃ ℓ : Coloring (Fin 2), IsTiling dec11 ℓ := by
  rintro ⟨ℓ, hT⟩
  rw [dec11_eq] at hT
  exact dec10_not_tileable ⟨_, isTiling_of_comp_mirror (isTiling_of_comp_rot hT)⟩

/-- The only chiral T=2 decorations are the orbits of #10 and #11
(kernel check over all 256 decorations). -/
theorem chiral_T2_cases : ∀ d : Fin 8 → Fin 2,
    Achiral d ∨ (∃ o : Fin 24, d = dec10 ∘ rot o)
      ∨ (∃ o : Fin 24, d = dec11 ∘ rot o) := by
  unfold Achiral
  decide

/-- **The T=2 hard direction**: tileable ⟹ achiral. -/
theorem corner3d_tileable_achiral_T2 (d : Fin 8 → Fin 2)
    (h : ∃ ℓ : Coloring (Fin 2), IsTiling d ℓ) : Achiral d := by
  rcases chiral_T2_cases d with ha | ⟨o, ho⟩ | ⟨o, ho⟩
  · exact ha
  · obtain ⟨ℓ, hT⟩ := h
    subst ho
    exact (dec10_not_tileable ⟨_, isTiling_of_comp_rot hT⟩).elim
  · obtain ⟨ℓ, hT⟩ := h
    subst ho
    exact (dec11_not_tileable ⟨_, isTiling_of_comp_rot hT⟩).elim

/-- **The 3D corner chirality theorem at T=2** (both directions):
a 2-color corner decoration tiles ℤ³ ⟺ it is achiral. -/
theorem corner3d_T2_iff (d : Fin 8 → Fin 2) :
    (∃ ℓ : Coloring (Fin 2), IsTiling d ℓ) ↔ Achiral d :=
  ⟨corner3d_tileable_achiral_T2 d, corner3d_tileable_of_achiral d⟩

end Corner3DDec10

#print axioms Corner3DDec10.dec10_not_tileable
#print axioms Corner3DDec10.dec11_not_tileable
#print axioms Corner3DDec10.corner3d_tileable_achiral_T2
#print axioms Corner3DDec10.corner3d_T2_iff