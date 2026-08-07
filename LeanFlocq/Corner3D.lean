/-
# Corner-marked Wang cubes: achiral ⟺ period-2 ⟹ tileable (K=1, easy half)

A corner decoration `d : Fin 8 → α` colors the eight corners of a cube
tile. A tiling is a vertex coloring `ℓ : ℤ³ → α` such that every unit
cube's corner pattern is a rotation of `d` (24 rotations, no
reflections). Corner indices are x-fastest: `p = x + 2y + 4z`, matching
`monotile/corner3d.py` (`CORNERS` / `SIG`).

**This file proves the easy half of the 3D corner chirality conjecture**
(Phase B, `monotile/DESIGN-corner-chirality.md`):

* `tileable_of_achiral` — achiral ⟹ period-(2,2,2) witness
  (construction `ℓ(v) = d(v mod 2)`);
* `achiral_of_periodic2` — period-(2,2,2) tiling ⟹ achiral;
* `corner3d_achiral_periodic` — the combined iff
  (`Achiral d ↔ ∃ ℓ, IsTiling d ℓ ∧ Periodic2 ℓ`), hence
  achiral ⟹ tileable. The converse (tileable ⟹ achiral) is the open
  hard direction (dimer/parity-flip obstruction, see the design doc).

The mathematical content is finite group theory: the parity shift
`τ_s` (corner relabeling `p ↦ p ⊕ s` induced by translating the cube by
`s ∈ {0,1}³`) is a proper rotation iff `|s|` is even, and a rotation
composed with one fixed mirror reflection iff `|s|` is odd
(`xorTab_cases`, kernel `decide`); the 24 rotations are closed under
composition and inversion and under conjugation by the mirror
(`rot_comp`, `rot_inv`, `mirror_conj`, all kernel `decide`). Both
directions are then pure algebra — no necklace lemma is needed.

The K=1 census cross-check (`census_T2`, `census_T3`: 23/21 and 333/201
canonical/achiral decorations) is a *compiled* computation
(`native_decide`) matching `monotile/corner3d_chiral.py`; it is not
part of the theorem trust base.

Trust base (theorems): Lean kernel + `decide` on finite types only —
propext, Classical.choice, Quot.sound (verified by `#print axioms`
below). No external evidence.
-/
import Mathlib

set_option maxRecDepth 1000000

namespace Corner3D

variable {α : Type*} [DecidableEq α]

/-- Vertex colorings of the cubic lattice. -/
abbrev Coloring (α : Type*) := ℤ × ℤ × ℤ → α

/-- A corner decoration: colors on the eight corners of the tile. -/
abbrev Dec (α : Type*) := Fin 8 → α

/-- Corners of the unit cube, x-fastest: `p = x + 2y + 4z`. -/
def cornerVec : Fin 8 → ℤ × ℤ × ℤ :=
  ![ (0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0),
     (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1) ]

/-- The 24 rotations of the cube as permutations of corner indices
(exported from `monotile/corner3d.py`, `SIG`). -/
def rot : Fin 24 → Fin 8 → Fin 8 :=
  ![ ![0, 1, 2, 3, 4, 5, 6, 7], ![6, 7, 4, 5, 2, 3, 0, 1],
     ![5, 4, 7, 6, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4],
     ![2, 3, 6, 7, 0, 1, 4, 5], ![4, 5, 0, 1, 6, 7, 2, 3],
     ![1, 0, 5, 4, 3, 2, 7, 6], ![7, 6, 3, 2, 5, 4, 1, 0],
     ![4, 6, 5, 7, 0, 2, 1, 3], ![1, 3, 0, 2, 5, 7, 4, 6],
     ![2, 0, 3, 1, 6, 4, 7, 5], ![7, 5, 6, 4, 3, 1, 2, 0],
     ![0, 4, 1, 5, 2, 6, 3, 7], ![3, 7, 2, 6, 1, 5, 0, 4],
     ![6, 2, 7, 3, 4, 0, 5, 1], ![5, 1, 4, 0, 7, 3, 6, 2],
     ![0, 2, 4, 6, 1, 3, 5, 7], ![5, 7, 1, 3, 4, 6, 0, 2],
     ![3, 1, 7, 5, 2, 0, 6, 4], ![6, 4, 2, 0, 7, 5, 3, 1],
     ![1, 5, 3, 7, 0, 4, 2, 6], ![2, 6, 0, 4, 3, 7, 1, 5],
     ![4, 0, 6, 2, 5, 1, 7, 3], ![7, 3, 5, 1, 6, 2, 4, 0] ]

/-- Reflection `x ↦ 1 − x` on corner indices (improper). -/
def mirror : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- The pattern shown on the unit cube with minimal corner `c`. -/
def cubePat (ℓ : Coloring α) (c : ℤ × ℤ × ℤ) : Fin 8 → α :=
  fun p => ℓ (c + cornerVec p)

/-- The tiling predicate: every unit cube shows a rotation of `d`. -/
def IsTiling (d : Dec α) (ℓ : Coloring α) : Prop :=
  ∀ c : ℤ × ℤ × ℤ, ∃ o : Fin 24, cubePat ℓ c = d ∘ rot o

/-- `d` is achiral: its mirror image is a rotation of itself. -/
def Achiral (d : Dec α) : Prop :=
  ∃ o : Fin 24, d ∘ mirror = d ∘ rot o

/-- Period-(2,2,2) colorings. -/
def Periodic2 (ℓ : Coloring α) : Prop :=
  ∀ v : ℤ × ℤ × ℤ,
    ℓ (v.1 + 2, v.2.1, v.2.2) = ℓ v
    ∧ ℓ (v.1, v.2.1 + 2, v.2.2) = ℓ v
    ∧ ℓ (v.1, v.2.1, v.2.2 + 2) = ℓ v

/-! ## Finite group facts (all by kernel `decide`) -/

/-- Composition table of the 24 rotations: `rot a ∘ rot b = rot (rotCompTab a b)`
(exported from `monotile/corner3d.py`, `SIG`). -/
def rotCompTab : Fin 24 → Fin 24 → Fin 24 :=
  ![ ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
     ![1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20],
     ![2, 3, 0, 1, 7, 6, 5, 4, 9, 8, 11, 10, 15, 14, 13, 12, 17, 16, 19, 18, 22, 23, 20, 21],
     ![3, 2, 1, 0, 6, 7, 4, 5, 11, 10, 9, 8, 13, 12, 15, 14, 18, 19, 16, 17, 21, 20, 23, 22],
     ![4, 5, 6, 7, 1, 0, 3, 2, 12, 13, 14, 15, 10, 11, 8, 9, 21, 20, 23, 22, 18, 19, 16, 17],
     ![5, 4, 7, 6, 0, 1, 2, 3, 14, 15, 12, 13, 8, 9, 10, 11, 22, 23, 20, 21, 17, 16, 19, 18],
     ![6, 7, 4, 5, 2, 3, 0, 1, 13, 12, 15, 14, 9, 8, 11, 10, 20, 21, 22, 23, 16, 17, 18, 19],
     ![7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 23, 22, 21, 20, 19, 18, 17, 16],
     ![8, 9, 10, 11, 17, 16, 19, 18, 0, 1, 2, 3, 22, 23, 20, 21, 5, 4, 7, 6, 14, 15, 12, 13],
     ![9, 8, 11, 10, 16, 17, 18, 19, 2, 3, 0, 1, 20, 21, 22, 23, 6, 7, 4, 5, 13, 12, 15, 14],
     ![10, 11, 8, 9, 18, 19, 16, 17, 1, 0, 3, 2, 21, 20, 23, 22, 4, 5, 6, 7, 12, 13, 14, 15],
     ![11, 10, 9, 8, 19, 18, 17, 16, 3, 2, 1, 0, 23, 22, 21, 20, 7, 6, 5, 4, 15, 14, 13, 12],
     ![12, 13, 14, 15, 20, 21, 22, 23, 4, 5, 6, 7, 16, 17, 18, 19, 0, 1, 2, 3, 8, 9, 10, 11],
     ![13, 12, 15, 14, 21, 20, 23, 22, 6, 7, 4, 5, 18, 19, 16, 17, 3, 2, 1, 0, 11, 10, 9, 8],
     ![14, 15, 12, 13, 23, 22, 21, 20, 5, 4, 7, 6, 19, 18, 17, 16, 1, 0, 3, 2, 10, 11, 8, 9],
     ![15, 14, 13, 12, 22, 23, 20, 21, 7, 6, 5, 4, 17, 16, 19, 18, 2, 3, 0, 1, 9, 8, 11, 10],
     ![16, 17, 18, 19, 8, 9, 10, 11, 20, 21, 22, 23, 0, 1, 2, 3, 12, 13, 14, 15, 4, 5, 6, 7],
     ![17, 16, 19, 18, 9, 8, 11, 10, 22, 23, 20, 21, 2, 3, 0, 1, 15, 14, 13, 12, 7, 6, 5, 4],
     ![18, 19, 16, 17, 11, 10, 9, 8, 21, 20, 23, 22, 3, 2, 1, 0, 13, 12, 15, 14, 6, 7, 4, 5],
     ![19, 18, 17, 16, 10, 11, 8, 9, 23, 22, 21, 20, 1, 0, 3, 2, 14, 15, 12, 13, 5, 4, 7, 6],
     ![20, 21, 22, 23, 13, 12, 15, 14, 16, 17, 18, 19, 6, 7, 4, 5, 9, 8, 11, 10, 2, 3, 0, 1],
     ![21, 20, 23, 22, 12, 13, 14, 15, 18, 19, 16, 17, 4, 5, 6, 7, 10, 11, 8, 9, 1, 0, 3, 2],
     ![22, 23, 20, 21, 14, 15, 12, 13, 17, 16, 19, 18, 5, 4, 7, 6, 8, 9, 10, 11, 0, 1, 2, 3],
     ![23, 22, 21, 20, 15, 14, 13, 12, 19, 18, 17, 16, 7, 6, 5, 4, 11, 10, 9, 8, 3, 2, 1, 0] ]

/-- The composition table is correct (certificate + kernel check; the
∃-search formulation is the same statement but slower to verify). -/
theorem rot_comp_tab : ∀ a b : Fin 24, ∀ p : Fin 8,
    rot a (rot b p) = rot (rotCompTab a b) p := by decide

/-- The rotations are closed under composition. -/
theorem rot_comp (a b : Fin 24) : ∃ c : Fin 24, rot a ∘ rot b = rot c :=
  ⟨rotCompTab a b, funext fun p => rot_comp_tab a b p⟩

/-- Every rotation has an inverse rotation. -/
theorem rot_inv : ∀ a : Fin 24, ∃ b : Fin 24, rot a ∘ rot b = id := by decide

/-- The mirror is an involution. -/
theorem mirror_mirror : mirror ∘ mirror = id := by decide

/-- Conjugating a rotation by the mirror is a rotation. -/
theorem mirror_conj : ∀ a : Fin 24, ∃ r : Fin 24,
    mirror ∘ rot a ∘ mirror = rot r := by decide

/-- Corner relabeling induced by translating the cube by `s ∈ {0,1}³`:
`xorTab s p = p ⊕ s` (bitwise, in the `x + 2y + 4z` numbering). -/
def xorTab : Fin 8 → Fin 8 → Fin 8 :=
  ![ ![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6],
     ![2, 3, 0, 1, 6, 7, 4, 5], ![3, 2, 1, 0, 7, 6, 5, 4],
     ![4, 5, 6, 7, 0, 1, 2, 3], ![5, 4, 7, 6, 1, 0, 3, 2],
     ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0] ]

/-- The crux finite fact: a parity shift `τ_s` is a rotation when `|s|`
is even (`s ∈ {0, 3, 5, 6}`) and mirror-∘-rotation when `|s|` is odd —
this is the `S₄`-on-diagonals content of the construction. -/
theorem xorTab_cases : ∀ s : Fin 8,
    (∃ o : Fin 24, xorTab s = rot o) ∨
    (∃ o : Fin 24, xorTab s = mirror ∘ rot o) := by decide

/-- The mirror is not a rotation (the two chiral classes are disjoint). -/
theorem mirror_not_rot : ¬ ∃ o : Fin 24, mirror = rot o := by decide

/-! ## Achiral ⟹ period-2 witness -/

/-- The parity-class index of a vertex: `(x%2, y%2, z%2) ↦ x' + 2y' + 4z'`. -/
def parIdx : ℤ → ℤ → ℤ → Fin 8 := fun x y z =>
  if x % 2 = 0 then (if y % 2 = 0 then (if z % 2 = 0 then 0 else 4)
                     else (if z % 2 = 0 then 2 else 6))
  else (if y % 2 = 0 then (if z % 2 = 0 then 1 else 5)
        else (if z % 2 = 0 then 3 else 7))

/-- The explicit period-2 witness coloring `ℓ(v) = d(v mod 2)`. -/
def wit (d : Dec α) : Coloring α := fun v => d (parIdx v.1 v.2.1 v.2.2)

omit [DecidableEq α] in
theorem pattern_eq (d : Dec α) (c : ℤ × ℤ × ℤ) :
    cubePat (wit d) c =
      d ∘ (fun p => parIdx (c.1 + (cornerVec p).1) (c.2.1 + (cornerVec p).2.1)
        (c.2.2 + (cornerVec p).2.2)) := rfl

/-- Reading the witness coloring on the cube at `c` relabels corners by
exactly the parity shift of `c`. -/
theorem shiftMap (c : ℤ × ℤ × ℤ) :
    (fun p => parIdx (c.1 + (cornerVec p).1) (c.2.1 + (cornerVec p).2.1)
        (c.2.2 + (cornerVec p).2.2))
      = xorTab (parIdx c.1 c.2.1 c.2.2) := by
  rcases Int.emod_two_eq_zero_or_one c.1 with h1 | h1 <;>
  rcases Int.emod_two_eq_zero_or_one c.2.1 with h2 | h2 <;>
  rcases Int.emod_two_eq_zero_or_one c.2.2 with h3 | h3 <;>
  funext p <;>
  fin_cases p <;>
    simp [cornerVec, parIdx, xorTab, h1, h2, h3, Int.add_emod]

omit [DecidableEq α] in
theorem tileable_of_achiral (d : Dec α) (h : Achiral d) :
    ∃ ℓ : Coloring α, IsTiling d ℓ ∧ Periodic2 ℓ := by
  obtain ⟨k0, hk0⟩ := h
  refine ⟨wit d, fun c => ?_, fun v => ⟨?_, ?_, ?_⟩⟩
  · have hpat : cubePat (wit d) c = d ∘ xorTab (parIdx c.1 c.2.1 c.2.2) := by
      rw [pattern_eq, shiftMap c]
    rcases xorTab_cases (parIdx c.1 c.2.1 c.2.2) with ⟨o, ho⟩ | ⟨o, ho⟩
    · exact ⟨o, by rw [hpat, ho]⟩
    · obtain ⟨o', ho'⟩ := rot_comp k0 o
      refine ⟨o', ?_⟩
      rw [hpat, ho, ← Function.comp_assoc, hk0, Function.comp_assoc, ho']
  · have hp : (v.1 + 2) % 2 = v.1 % 2 := by omega
    unfold wit parIdx
    rw [hp]
  · have hp : (v.2.1 + 2) % 2 = v.2.1 % 2 := by omega
    unfold wit parIdx
    rw [hp]
  · have hp : (v.2.2 + 2) % 2 = v.2.2 % 2 := by omega
    unfold wit parIdx
    rw [hp]

/-! ## Period-2 tiling ⟹ achiral -/

/-- Geometric form of the mirror on corners (componentwise). -/
theorem cornerVec_mirror (p : Fin 8) :
    cornerVec (mirror p)
      = (1 - (cornerVec p).1, (cornerVec p).2.1, (cornerVec p).2.2) := by
  fin_cases p <;> rfl

/-- Geometric form of stepping across the mirror plane (componentwise). -/
theorem add_cornerVec (p : Fin 8) :
    (1, 0, 0) + cornerVec p
      = ((cornerVec p).1 + 1, (cornerVec p).2.1, (cornerVec p).2.2) := by
  fin_cases p <;> rfl

omit [DecidableEq α] in
/-- The cube across the mirror plane reads the mirrored pattern:
periodicity identifies its corners with those of the cube at the origin,
composed with `mirror`. -/
theorem cubePat_mirror_link (ℓ : Coloring α) (hP : Periodic2 ℓ) (p : Fin 8) :
    ℓ ((1, 0, 0) + cornerVec p) = ℓ (cornerVec (mirror p)) := by
  rw [add_cornerVec p, cornerVec_mirror p]
  rcases show (cornerVec p).1 = 0 ∨ (cornerVec p).1 = 1
      from by fin_cases p <;> simp [cornerVec] with hx | hx
  · rw [hx]
    show ℓ ((1 : ℤ), (cornerVec p).2.1, (cornerVec p).2.2)
       = ℓ (1, (cornerVec p).2.1, (cornerVec p).2.2)
    rfl
  · rw [hx]
    show ℓ (2, (cornerVec p).2.1, (cornerVec p).2.2)
       = ℓ (0, (cornerVec p).2.1, (cornerVec p).2.2)
    exact (hP (0, (cornerVec p).2.1, (cornerVec p).2.2)).1

omit [DecidableEq α] in
theorem achiral_of_periodic2 (d : Dec α)
    (h : ∃ ℓ : Coloring α, IsTiling d ℓ ∧ Periodic2 ℓ) : Achiral d := by
  obtain ⟨ℓ, hT, hP⟩ := h
  obtain ⟨a, ha⟩ := hT (0, 0, 0)
  obtain ⟨b, hb⟩ := hT (1, 0, 0)
  -- `d ∘ rot a ∘ mirror = d ∘ rot b`, pointwise.
  have key : ∀ q : Fin 8, d (rot a (mirror q)) = d (rot b q) := by
    intro q
    have e1 := congrFun ha (mirror q)
    have e2 := congrFun hb q
    have zadd : ∀ v : ℤ × ℤ × ℤ, (0, 0, 0) + v = v := fun v => zero_add v
    have e1' : ℓ (cornerVec (mirror q)) = d (rot a (mirror q)) := by
      simpa [cubePat, Function.comp_apply, zadd] using e1
    have e2' : ℓ (cornerVec (mirror q)) = d (rot b q) := by
      simpa [cubePat, Function.comp_apply]
        using (cubePat_mirror_link ℓ hP q).symm.trans e2
    exact e1'.symm.trans e2'
  -- Group algebra: `d ∘ mirror = d ∘ rot b ∘ (mirror ∘ rot a⁻¹ ∘ mirror)`.
  obtain ⟨ai, hai⟩ := rot_inv a
  obtain ⟨r, hr⟩ := mirror_conj ai
  obtain ⟨o, ho⟩ := rot_comp b r
  refine ⟨o, ?_⟩
  funext p
  simp only [Function.comp_apply]
  have h1 : rot o p = rot b (mirror (rot ai (mirror p))) := by
    rw [← ho, ← hr]
    simp [Function.comp_apply]
  have h2 : ∀ x : Fin 8, mirror (mirror x) = x := by
    intro x; have := congrFun mirror_mirror x
    simpa [Function.comp_apply] using this
  have h3 : ∀ x : Fin 8, rot a (rot ai x) = x := by
    intro x; have := congrFun hai x
    simpa [Function.comp_apply] using this
  rw [h1, ← key, h2, h3]

/-! ## Main theorem (the easy half of the 3D corner chirality conjecture) -/

omit [DecidableEq α] in
/-- Achiral ⟺ period-(2,2,2) witness. -/
theorem corner3d_achiral_periodic (d : Dec α) :
    Achiral d ↔ ∃ ℓ : Coloring α, IsTiling d ℓ ∧ Periodic2 ℓ :=
  ⟨tileable_of_achiral d, achiral_of_periodic2 d⟩

omit [DecidableEq α] in
/-- In particular, achiral ⟹ tileable. (The converse — tileable ⟹
achiral — is the open hard direction; see the design doc.) -/
theorem corner3d_tileable_of_achiral (d : Dec α) (h : Achiral d) :
    ∃ ℓ : Coloring α, IsTiling d ℓ :=
  (tileable_of_achiral d h).elim fun ℓ hℓ => ⟨ℓ, hℓ.1⟩

/-! ## The chiral T=2 pair #10/#11 (kernel checks) -/

/-- The two empty T=2 decorations of `monotile/corner3d_T2_results.jsonl`
(indices 10 and 11 of the canonical census). -/
def dec10 : Fin 8 → Fin 2 := ![0, 0, 0, 1, 1, 0, 1, 1]
def dec11 : Fin 8 → Fin 2 := ![0, 0, 0, 1, 1, 1, 0, 1]

theorem dec10_chiral : ¬ Achiral dec10 := by unfold Achiral; decide
theorem dec11_chiral : ¬ Achiral dec11 := by unfold Achiral; decide

/-- …and they are mirror images of each other (up to rotation). -/
theorem dec10_mirror_dec11 : ∃ o : Fin 24, dec10 ∘ mirror = dec11 ∘ rot o := by
  decide

/-! ## K=1 census cross-check (compiled; NOT part of the theorem trust base)

Matches `monotile/corner3d_chiral.py`: T=2 has 23 canonical decorations
of which 21 achiral; T=3 has 333 of which 201 achiral. -/

/-- Boolean achirality test over a concrete finite palette. -/
def achiralB {t : ℕ} (d : Fin 8 → Fin (t + 1)) : Bool :=
  (List.finRange 24).any fun o =>
    (List.finRange 8).all fun p => d (mirror p) == d (rot o p)

theorem achiralB_iff {t : ℕ} (d : Fin 8 → Fin (t + 1)) :
    achiralB d ↔ Achiral d := by
  rw [achiralB, List.any_eq_true]
  constructor
  · rintro ⟨o, -, ho⟩
    rw [List.all_eq_true] at ho
    refine ⟨o, funext fun p => ?_⟩
    have hp := ho p (List.mem_finRange p)
    simpa using hp
  · rintro ⟨o, ho⟩
    refine ⟨o, List.mem_finRange o, ?_⟩
    rw [List.all_eq_true]
    intro p _
    have hp := congrFun ho p
    simpa [Function.comp_apply] using hp

/-- All decorations `Fin 8 → Fin (t+1)`, enumerated base-`(t+1)`. -/
def allDecs (t : ℕ) : List (Fin 8 → Fin (t + 1)) :=
  (List.range ((t + 1) ^ 8)).map fun n =>
    fun p => ⟨n / (t + 1) ^ p.val % (t + 1), Nat.mod_lt _ (Nat.succ_pos t)⟩

/-- Numeric key of the pattern shown in orientation `o` (lexicographic
order on the 8 colors = numeric order, all lists have length 8). -/
def decKey (t : ℕ) (d : Fin 8 → Fin (t + 1)) (o : Fin 24) : ℕ :=
  (List.finRange 8).foldl (fun acc p => acc * (t + 1) + (d (rot o p)).val) 0

/-- The canonical key: minimum over the rotation orbit (matches
`corner3d.py`'s `canonical`). -/
def canonicalKey (t : ℕ) (d : Fin 8 → Fin (t + 1)) : ℕ :=
  (List.finRange 24).foldl
    (fun acc o => min acc (decKey t d o)) (decKey t d 0)

/-- `(number of canonical decorations, number of achiral canonicals)`. -/
def censusStats (t : ℕ) : ℕ × ℕ :=
  let keys := (allDecs t).map fun d => (canonicalKey t d, achiralB d)
  let canons := (keys.map Prod.fst).eraseDups
  let ach := ((keys.filter Prod.snd).map Prod.fst).eraseDups
  (canons.length, ach.length)

theorem census_T2 : censusStats 1 = (23, 21) := by native_decide
theorem census_T3 : censusStats 2 = (333, 201) := by native_decide

end Corner3D

#print axioms Corner3D.tileable_of_achiral
#print axioms Corner3D.achiral_of_periodic2
#print axioms Corner3D.corner3d_achiral_periodic
#print axioms Corner3D.dec10_chiral
