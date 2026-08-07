/-
# Corner-marked Wang squares: tileable ⟺ achiral (K=1)

A corner decoration `d : Fin 4 → α` colors the four corners of a square
tile. A tiling is a vertex coloring `ℓ : ℤ × ℤ → α` such that every unit
square's corner pattern is a rotation of `d` — equivalently (the form the
Python probes use): an orientation field ω : ℤ² → C4 with all four
incident corner colors equal at every lattice vertex. No reflections:
a physical tile has no mirror image.

**Theorem** (`corner2d_tileable_iff_achiral`): a decoration tiles ℤ² iff
it is achiral — its mirror image is a rotation of itself. Moreover every
achiral decoration admits a period-(2,2) tiling
(`tileable_of_achiral`), and every periodic corner tiling needs at most
period 2.

Proof of the hard direction (`achiral_of_tileable`): pair-reversal.
Every square realizes the directed adjacent-pair multiset of `d` on its
four clockwise edges; each lattice edge is read in *opposite* cyclic
directions by its two incident squares, so every realized directed pair
has its reverse realized; hence the pair support is reversal-closed
(`revClosed_of_isTiling`). A length-4 necklace with reversal-closed
directed-pair support is achiral (`necklace`, reduced to a finite check
on equality patterns `Fin 4 → Fin 4`, `necklaceFin`, by `decide`).

Context: Phase B of the corner-cubes project — see
monotile/DESIGN-corner-chirality.md and monotile/RESULTS-corner-k1.md.
Empirical status (monotile/corner2d.py): T=2 (6 canonical), T=3 (24),
T=4 (70): achiral ⟺ periodic, zero mismatches.

Trust base: Lean kernel + `decide` on finite types only. No axioms,
no native_decide, no external evidence.
-/
import Mathlib

set_option maxRecDepth 1000000

namespace Corner2D

variable {α : Type*} [DecidableEq α]

/-- Vertex colorings of the square lattice. -/
abbrev Coloring (α : Type*) := ℤ × ℤ → α

/-- A corner decoration: colors on the four corners of the tile. -/
abbrev Dec (α : Type*) := Fin 4 → α

/-- Corners of the unit square, clockwise from the lower-left:
0 = (0,0), 1 = (1,0), 2 = (1,1), 3 = (0,1). -/
def cornerVec : Fin 4 → ℤ × ℤ := ![ (0, 0), (1, 0), (1, 1), (0, 1) ]

/-- The square across edge `m` of a cell: 0 below, 1 right, 2 above,
3 left. -/
def step : Fin 4 → ℤ × ℤ := ![ (0, -1), (1, 0), (0, 1), (-1, 0) ]

/-- The pattern shown on the unit square with lower-left corner `c`. -/
def squarePat (ℓ : Coloring α) (c : ℤ × ℤ) : Fin 4 → α :=
  fun p => ℓ (c + cornerVec p)

/-- Quarter-turn rotation on corner positions. -/
def rot (k : Fin 4) : Fin 4 → Fin 4 := (· + k)

/-- Reflection across the vertical midline on corner positions. -/
def mirror : Fin 4 → Fin 4 := (1 - ·)

/-- The tiling predicate: every unit square shows a rotation of `d`. -/
def IsTiling (d : Dec α) (ℓ : Coloring α) : Prop :=
  ∀ c : ℤ × ℤ, ∃ k : Fin 4, squarePat ℓ c = d ∘ rot k

/-- `d` is achiral: its mirror image is a rotation of itself. -/
def Achiral (d : Dec α) : Prop :=
  ∃ k : Fin 4, d ∘ mirror = d ∘ rot k

/-- Reversal-closure of the directed adjacent-pair support. -/
def RevClosed (d : Dec α) : Prop :=
  ∀ i : Fin 4, ∃ j : Fin 4, d j = d (i + 1) ∧ d (j + 1) = d i

/-- Period-(2,2) colorings. -/
def Periodic2 (ℓ : Coloring α) : Prop :=
  ∀ v : ℤ × ℤ, ℓ (v.1 + 2, v.2) = ℓ v ∧ ℓ (v.1, v.2 + 2) = ℓ v

/-! ## Finite arithmetic and geometry facts (all by `decide`) -/

theorem fin4_sub_add : ∀ a b : Fin 4, a - b + b = a := by decide
theorem fin4_arith1 : ∀ a b : Fin 4, (a - b + 1) + b = a + 1 := by decide
theorem fin4_arith2 : ∀ a b : Fin 4, (a + 2 + b) + 1 = a + 3 + b := by decide

/-- The square across edge `m` reads the shared edge reversed:
its corner `m + 2` is our corner `m + 1`. -/
theorem step_corner_two : ∀ m : Fin 4,
    step m + cornerVec (m + 2) = cornerVec (m + 1) := by decide

/-- Its corner `m + 3` is our corner `m`. -/
theorem step_corner_three : ∀ m : Fin 4,
    step m + cornerVec (m + 3) = cornerVec m := by decide

/-! ## The pair-reversal argument -/

theorem revClosed_of_isTiling (d : Dec α) (ℓ : Coloring α)
    (hT : IsTiling d ℓ) : RevClosed d := by
  intro i
  obtain ⟨k, hk⟩ := hT (0, 0)
  obtain ⟨k', hk'⟩ := hT (step (i - k))
  have e1 := congrFun hk (i - k + 1)
  have e2 := congrFun hk' (i - k + 2)
  have e0 := congrFun hk (i - k)
  have e3 := congrFun hk' (i - k + 3)
  have g2 := step_corner_two (i - k)
  have g3 := step_corner_three (i - k)
  have zadd : ∀ v : ℤ × ℤ, (0, 0) + v = v := fun v => zero_add v
  simp only [squarePat, Function.comp_apply, rot, zadd] at e0 e1 e2 e3
  rw [g2] at e2
  rw [g3] at e3
  -- e1 : ℓ (cornerVec (i-k+1)) = d (i-k+1+k);  e2 : same LHS = d (i-k+2+k')
  -- e0 : ℓ (cornerVec (i-k))   = d (i-k+k);    e3 : ℓ(cornerVec(i-k)) = d (i-k+3+k')
  refine ⟨(i - k) + 2 + k', ?_, ?_⟩
  · have ee : d (i - k + 1 + k) = d (i - k + 2 + k') := e1.symm.trans e2
    conv_rhs => rw [← fin4_arith1 i k]
    exact ee.symm
  · have ee : d (i - k + k) = d (i - k + 3 + k') := e0.symm.trans e3
    rw [show ((i - k) + 2 + k') + 1 = (i - k) + 3 + k' from fin4_arith2 (i - k) k']
    conv_rhs => rw [← fin4_sub_add i k]
    exact ee.symm

/-! ## The necklace lemma -/

/-- The equality pattern of a decoration: first-occurrence indices. -/
def normPat (d : Dec α) : Fin 4 → Fin 4 :=
  fun a => if d a = d 0 then 0 else if d a = d 1 then 1
    else if d a = d 2 then 2 else 3

theorem normPat_spec (d : Dec α) (a : Fin 4) : d (normPat d a) = d a := by
  fin_cases a <;> unfold normPat <;> split_ifs with h1 h2 h3 <;> simp_all

theorem normPat_inj (d : Dec α) {a b : Fin 4}
    (h : normPat d a = normPat d b) : d a = d b := by
  rw [← normPat_spec d a, ← normPat_spec d b, h]

theorem normPat_congr (d : Dec α) {a b : Fin 4}
    (h : d a = d b) : normPat d a = normPat d b := by
  unfold normPat
  rw [h]

/-- The finite core: reversal-closed length-4 necklaces over a 4-letter
alphabet are achiral. Checked by kernel `decide` over all 4^4 = 256
equality patterns. -/
theorem necklaceFin : ∀ e : Fin 4 → Fin 4,
    (∀ i : Fin 4, ∃ j : Fin 4, e j = e (i + 1) ∧ e (j + 1) = e i) →
    ∃ k : Fin 4, e ∘ mirror = e ∘ rot k := by decide

/-- The necklace lemma: reversal-closed support implies achirality. -/
theorem necklace (d : Dec α) (h : RevClosed d) : Achiral d := by
  have h' : ∀ i : Fin 4, ∃ j : Fin 4,
      normPat d j = normPat d (i + 1) ∧ normPat d (j + 1) = normPat d i := by
    intro i
    obtain ⟨j, h1, h2⟩ := h i
    exact ⟨j, normPat_congr d h1, normPat_congr d h2⟩
  obtain ⟨k, hk⟩ := necklaceFin (normPat d) h'
  refine ⟨k, ?_⟩
  funext p
  have hp := congrFun hk p
  simp only [Function.comp_apply, rot] at hp
  exact normPat_inj d hp

/-! ## Assembly: the hard direction -/

theorem achiral_of_tileable (d : Dec α)
    (h : ∃ ℓ : Coloring α, IsTiling d ℓ) : Achiral d := by
  obtain ⟨ℓ, hT⟩ := h
  exact necklace d (revClosed_of_isTiling d ℓ hT)

/-! ## The easy direction: achiral ⟹ period-2 witness -/

/-- The position of a vertex's parity class in the corner numbering:
(x,y) mod 2 ↦ 0,1,2,3 for (0,0),(1,0),(1,1),(0,1). -/
def sqIdxZ : ℤ → ℤ → Fin 4 :=
  fun x y => if x % 2 = 0 then (if y % 2 = 0 then 0 else 3)
    else (if y % 2 = 0 then 1 else 2)

/-- The explicit period-2 witness coloring. -/
def wit (d : Dec α) : Coloring α := fun v => d (sqIdxZ v.1 v.2)

theorem pattern_eq (d : Dec α) (c : ℤ × ℤ) :
    squarePat (wit d) c =
      d ∘ (fun p => sqIdxZ (c.1 + (cornerVec p).1) (c.2 + (cornerVec p).2)) := rfl

/-- The four parity-shift maps on corner positions. -/
theorem shiftMap_00 (c : ℤ × ℤ) (h1 : c.1 % 2 = 0) (h2 : c.2 % 2 = 0) :
    (fun p => sqIdxZ (c.1 + (cornerVec p).1) (c.2 + (cornerVec p).2))
      = rot 0 := by
  funext p
  fin_cases p <;>
    simp [cornerVec, sqIdxZ, h1, h2, Int.add_emod, rot]

theorem shiftMap_11 (c : ℤ × ℤ) (h1 : c.1 % 2 = 1) (h2 : c.2 % 2 = 1) :
    (fun p => sqIdxZ (c.1 + (cornerVec p).1) (c.2 + (cornerVec p).2))
      = rot 2 := by
  funext p
  fin_cases p <;>
    simp [cornerVec, sqIdxZ, h1, h2, Int.add_emod, rot]

theorem shiftMap_10 (c : ℤ × ℤ) (h1 : c.1 % 2 = 1) (h2 : c.2 % 2 = 0) :
    (fun p => sqIdxZ (c.1 + (cornerVec p).1) (c.2 + (cornerVec p).2))
      = mirror := by
  funext p
  fin_cases p <;>
    simp [cornerVec, sqIdxZ, h1, h2, Int.add_emod, mirror]

theorem shiftMap_01 (c : ℤ × ℤ) (h1 : c.1 % 2 = 0) (h2 : c.2 % 2 = 1) :
    (fun p => sqIdxZ (c.1 + (cornerVec p).1) (c.2 + (cornerVec p).2))
      = mirror ∘ rot 2 := by
  funext p
  fin_cases p <;>
    simp [cornerVec, sqIdxZ, h1, h2, Int.add_emod, mirror, rot]

theorem tileable_of_achiral (d : Dec α) (h : Achiral d) :
    ∃ ℓ : Coloring α, IsTiling d ℓ ∧ Periodic2 ℓ := by
  obtain ⟨k0, hk0⟩ := h
  have hk0' : ∀ q : Fin 4, d (mirror q) = d (q + k0) := fun q => congrFun hk0 q
  refine ⟨wit d, fun c => ?_, fun v => ⟨?_, ?_⟩⟩
  · rcases Int.emod_two_eq_zero_or_one c.1 with h1 | h1 <;>
      rcases Int.emod_two_eq_zero_or_one c.2 with h2 | h2
    · exact ⟨0, by rw [pattern_eq, shiftMap_00 c h1 h2]⟩
    · refine ⟨k0 + 2, ?_⟩
      rw [pattern_eq, shiftMap_01 c h1 h2]
      funext p
      simp only [Function.comp_apply, rot]
      rw [hk0']
      congr 1
      rw [add_assoc, add_comm (2 : Fin 4) k0]
    · exact ⟨k0, by rw [pattern_eq, shiftMap_10 c h1 h2]; exact hk0⟩
    · exact ⟨2, by rw [pattern_eq, shiftMap_11 c h1 h2]⟩
  · have hp : (v.1 + 2) % 2 = v.1 % 2 := by omega
    unfold wit sqIdxZ
    rw [hp]
  · have hp : (v.2 + 2) % 2 = v.2 % 2 := by omega
    unfold wit sqIdxZ
    rw [hp]

/-! ## Main theorem -/

/-- A corner decoration tiles ℤ² iff it is achiral. -/
theorem corner2d_tileable_iff_achiral (d : Dec α) :
    (∃ ℓ : Coloring α, IsTiling d ℓ) ↔ Achiral d :=
  ⟨achiral_of_tileable d,
   fun h => (tileable_of_achiral d h).elim (fun ℓ hℓ => ⟨ℓ, hℓ.1⟩)⟩

/-- Strengthened: tileable ⟺ achiral ⟺ period-(2,2) witness exists. -/
theorem corner2d_tileable_iff_period2 (d : Dec α) :
    (∃ ℓ : Coloring α, IsTiling d ℓ) ↔
      ∃ ℓ : Coloring α, IsTiling d ℓ ∧ Periodic2 ℓ :=
  ⟨fun h => tileable_of_achiral d (achiral_of_tileable d h),
   fun h => h.elim (fun ℓ hℓ => ⟨ℓ, hℓ.1⟩)⟩

end Corner2D
