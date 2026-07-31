/-
Instantiating the color density lemma (`LeanFlocq/ColorDensity.lean`) with
the real 3D arena geometry, and the fall of color canon 755 by pure
counting — no SAT solver, no certificate.

Contents:

  * `shownTable` / `shown`: for each of the 24 orientations and each of the
    6 world directions, the base face type shown. Exported from monotile's
    arena geometry (the same derivation as `color_density_check.py`'s
    `SIGMA`), cross-checked 0/1728 mismatches against the `AnyK3DGeom`
    triple tables by `table_shown_coherence` (kernel computation).
  * `pairOf held`: the allowed-adjacency relation on face types induced by
    an 84-bit equation profile.
  * `boxTilingOf`: any ℤ³ orientation field tiling `relOfHeld held`
    restricts to a `ColorDensity.BoxTiling` of any `L³` box.
  * `not_isTiling_of_deficient`: a profile with a deficient face-type class
    (`A` pairs only into `B`, `|A| > |B|`) has an empty SFT.
  * Canon 755 (`color3d_canonical.json` index 755): `A = {3, 5}`, `B = {4}`,
    deficiency and symmetry discharged by `native_decide`;
    `color755_empty` — **canon 755 cannot tile ℤ³, by pure counting.**
-/

import LeanFlocq.ColorDensity
import LeanFlocq.AnyK3D

namespace AnyK3D

open ColorDensity

/-! ## The shown-face table -/

/-- `shownTable[o*6 + w]`: base face type shown by orientation `o` on world
direction `w`, where `w = 2*ax` is `+ax` and `w = 2*ax+1` is `-ax`.
Exported from monotile's arena geometry (`color_density_check.py`'s SIGMA,
ARENA_K=4; the geometry is K-independent at the face level). -/
def shownTable : Array Nat := #[
  0, 1, 2, 3, 4, 5,
  0, 1, 3, 2, 5, 4,
  1, 0, 2, 3, 5, 4,
  1, 0, 3, 2, 4, 5,
  0, 1, 4, 5, 3, 2,
  0, 1, 5, 4, 2, 3,
  1, 0, 4, 5, 2, 3,
  1, 0, 5, 4, 3, 2,
  2, 3, 0, 1, 5, 4,
  2, 3, 1, 0, 4, 5,
  3, 2, 0, 1, 4, 5,
  3, 2, 1, 0, 5, 4,
  2, 3, 4, 5, 0, 1,
  2, 3, 5, 4, 1, 0,
  3, 2, 4, 5, 1, 0,
  3, 2, 5, 4, 0, 1,
  4, 5, 0, 1, 2, 3,
  4, 5, 1, 0, 3, 2,
  5, 4, 0, 1, 3, 2,
  5, 4, 1, 0, 2, 3,
  4, 5, 2, 3, 1, 0,
  4, 5, 3, 2, 0, 1,
  5, 4, 2, 3, 0, 1,
  5, 4, 3, 2, 1, 0
]

/-- The face type shown by orientation `o` on world direction `w`. -/
def shown (o : Fin 24) (w : Fin 6) : Fin 6 :=
  f6 (shownTable.getD (o.val * 6 + w.val) 0)

/-- Every orientation shows each base face type exactly once. -/
theorem shown_bijective : ∀ o : Fin 24, Function.Bijective (shown o) := by
  native_decide

/-- World direction index: `(ax, +) ↦ 2·ax`, `(ax, −) ↦ 2·ax + 1`. -/
def dirIdx : Dir → Fin 6
  | (ax, true) => ⟨2 * ax.val, by have := ax.isLt; omega⟩
  | (ax, false) => ⟨2 * ax.val + 1, by have := ax.isLt; omega⟩

theorem dirIdx_injective : Function.Injective dirIdx := by
  intro d₁ d₂ h
  obtain ⟨ax₁, s₁⟩ := d₁
  obtain ⟨ax₂, s₂⟩ := d₂
  cases s₁ with
  | true =>
    cases s₂ with
    | true =>
      have hv : 2 * ax₁.val = 2 * ax₂.val := congrArg Fin.val h
      have hax : ax₁ = ax₂ := Fin.ext (by omega)
      subst hax; rfl
    | false =>
      have hv : 2 * ax₁.val = 2 * ax₂.val + 1 := congrArg Fin.val h
      omega
  | false =>
    cases s₂ with
    | true =>
      have hv : 2 * ax₁.val + 1 = 2 * ax₂.val := congrArg Fin.val h
      omega
    | false =>
      have hv : 2 * ax₁.val + 1 = 2 * ax₂.val + 1 := congrArg Fin.val h
      have hax : ax₁ = ax₂ := Fin.ext (by omega)
      subst hax; rfl

theorem dirIdx_bijective : Function.Bijective dirIdx :=
  (Fintype.bijective_iff_injective_and_card dirIdx).mpr ⟨dirIdx_injective, by decide⟩

/-- The face type shown by orientation `o` on direction `d`. -/
def faceOf (o : Fin 24) : Dir → Fin 6 := shown o ∘ dirIdx

theorem faceOf_bijective (o : Fin 24) : Function.Bijective (faceOf o) :=
  (shown_bijective o).comp dirIdx_bijective

/-- The exported triple tables agree with the shown-face table: for the
adjacency `(ax, o1, o2)`, `o1` shows `tFaceA` on `+ax` and `o2` shows
`tFaceB` on `−ax`. Kernel-checked on all 1728 triples. -/
theorem table_shown_coherence : ∀ (ax : Fin 3) (o1 o2 : Fin 24),
    tfa (tIdx ax o1 o2) = faceOf o1 (ax, true) ∧
    tfb (tIdx ax o1 o2) = faceOf o2 (ax, false) := by
  native_decide

/-! ## The pair relation and the box restriction -/

/-- The allowed-adjacency relation on face types induced by an equation
profile: types `g`, `h` may touch iff some compatible orientation triple
showing `(g, h)` has its face equation held. -/
@[reducible]
def pairOf (held : Fin 84 → Bool) (g h : Fin 6) : Prop :=
  ∃ (ax : Fin 3) (o1 o2 : Fin 24),
    held (teq ax o1 o2) = true ∧
    tfa (tIdx ax o1 o2) = g ∧ tfb (tIdx ax o1 o2) = h

/-- Embed a box cell in ℤ³. -/
def embed {L : ℕ} (c : Cell L) : ℤ × ℤ × ℤ :=
  (((c (0:Fin 3) : ℕ) : ℤ), ((c (1:Fin 3) : ℕ) : ℤ), ((c (2:Fin 3) : ℕ) : ℤ))

theorem embed_update_succ_of_zero {L : ℕ} (c : Cell L) (ax : Fin 3)
    (h : (c ax : ℕ) + 1 < L) (hax : ax = 0) :
    embed (Function.update c ax ⟨(c ax : ℕ) + 1, h⟩)
      = ((embed c).1 + 1, (embed c).2.1, (embed c).2.2) := by
  subst hax
  have e0 := Function.update_self (0:Fin 3) ⟨(c (0:Fin 3) : ℕ) + 1, h⟩ c
  have e1 := Function.update_of_ne (show (1:Fin 3) ≠ 0 by decide) ⟨(c (0:Fin 3) : ℕ) + 1, h⟩ c
  have e2 := Function.update_of_ne (show (2:Fin 3) ≠ 0 by decide) ⟨(c (0:Fin 3) : ℕ) + 1, h⟩ c
  unfold embed
  rw [e0, e1, e2]
  congr 1

theorem embed_update_succ_of_one {L : ℕ} (c : Cell L) (ax : Fin 3)
    (h : (c ax : ℕ) + 1 < L) (hax : ax = 1) :
    embed (Function.update c ax ⟨(c ax : ℕ) + 1, h⟩)
      = ((embed c).1, (embed c).2.1 + 1, (embed c).2.2) := by
  subst hax
  have e0 := Function.update_of_ne (show (0:Fin 3) ≠ 1 by decide) ⟨(c (1:Fin 3) : ℕ) + 1, h⟩ c
  have e1 := Function.update_self (1:Fin 3) ⟨(c (1:Fin 3) : ℕ) + 1, h⟩ c
  have e2 := Function.update_of_ne (show (2:Fin 3) ≠ 1 by decide) ⟨(c (1:Fin 3) : ℕ) + 1, h⟩ c
  unfold embed
  rw [e0, e1, e2]
  congr 1

theorem embed_update_succ_of_two {L : ℕ} (c : Cell L) (ax : Fin 3)
    (h : (c ax : ℕ) + 1 < L) (hax : ax = 2) :
    embed (Function.update c ax ⟨(c ax : ℕ) + 1, h⟩)
      = ((embed c).1, (embed c).2.1, (embed c).2.2 + 1) := by
  subst hax
  have e0 := Function.update_of_ne (show (0:Fin 3) ≠ 2 by decide) ⟨(c (2:Fin 3) : ℕ) + 1, h⟩ c
  have e1 := Function.update_of_ne (show (1:Fin 3) ≠ 2 by decide) ⟨(c (2:Fin 3) : ℕ) + 1, h⟩ c
  have e2 := Function.update_self (2:Fin 3) ⟨(c (2:Fin 3) : ℕ) + 1, h⟩ c
  unfold embed
  rw [e0, e1, e2]
  congr 1

/-- Any ℤ³ tiling of the orientation SFT restricts to a box tiling of any
side: cells show face types bijectively, and SFT compatibility becomes
face-type compatibility via the shown-face table. -/
def boxTilingOf (held : Fin 84 → Bool) {L : ℕ}
    (ω : ℤ × ℤ × ℤ → Fin 24) (hω : IsTiling (relOfHeld held) ω) :
    BoxTiling (Fin 6) L (pairOf held) where
  face c d := faceOf (ω (embed c)) d
  face_bij c := faceOf_bijective (ω (embed c))
  compat c ax h := by
    fin_cases ax
    · refine ⟨0, ω (embed c), ω ((embed c).1 + 1, (embed c).2.1, (embed c).2.2),
        (hω (embed c)).1, (table_shown_coherence 0 _ _).1, ?_⟩
      rw [embed_update_succ_of_zero c _ h rfl]
      exact (table_shown_coherence 0 _ _).2
    · refine ⟨1, ω (embed c), ω ((embed c).1, (embed c).2.1 + 1, (embed c).2.2),
        (hω (embed c)).2.1, (table_shown_coherence 1 _ _).1, ?_⟩
      rw [embed_update_succ_of_one c _ h rfl]
      exact (table_shown_coherence 1 _ _).2
    · refine ⟨2, ω (embed c), ω ((embed c).1, (embed c).2.1, (embed c).2.2 + 1),
        (hω (embed c)).2.2, (table_shown_coherence 2 _ _).1, ?_⟩
      rw [embed_update_succ_of_two c _ h rfl]
      exact (table_shown_coherence 2 _ _).2

/-- A profile with a deficient face-type class has an empty orientation SFT:
no decoration with this compatibility relation tiles ℤ³. -/
theorem not_isTiling_of_deficient (held : Fin 84 → Bool) (A B : Finset (Fin 6))
    (hsymm : ∀ g h, pairOf held g h → pairOf held h g)
    (hpair : ∀ g ∈ A, ∀ h, pairOf held g h → h ∈ B)
    (hAB : B.card < A.card) :
    ¬ ∃ ω, IsTiling (relOfHeld held) ω := by
  rintro ⟨ω, hω⟩
  have hd : 1 ≤ A.card - B.card := Nat.sub_pos_of_lt hAB
  have hb : 6 < (A.card - B.card) * 7 := by
    have h7 : 7 ≤ (A.card - B.card) * 7 := by
      calc 7 = 1 * 7 := rfl
        _ ≤ (A.card - B.card) * 7 := Nat.mul_le_mul_right 7 hd
    omega
  exact ColorDensity.not_tileable_of_deficit hsymm hpair hAB hb
    ⟨boxTilingOf held ω hω⟩

/-! ## Canon 755 -/

/-- The 84-bit equation profile of color canon 755
(`monotile/color3d_canonical.json`, index 755). -/
def held755arr : Array Bool := #[
  true, true, true, true, true, true, true, true, true, true, true, true,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, true, true, true, true, true, true, true,
  false, false, false, false, false, false, false, false, false, false, false, false,
  true, true, true, true,
  false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false,
  true, true, true, true,
  false, false, false, false, false, false, false, false,
  true, true, true, true,
  false, false, false, false
]

def held755 (i : Fin 84) : Bool := held755arr.getD i.val false

/-- Canon 755's pair relation is symmetric (checked on all 36 type pairs
against all 1728 triples). -/
theorem pair755_symm : ∀ g h, pairOf held755 g h → pairOf held755 h g := by
  native_decide

/-- Faces 3 and 5 pair only into `{4}` (checked by kernel computation). -/
theorem pair755_deficient : ∀ g ∈ ({3, 5} : Finset (Fin 6)), ∀ h,
    pairOf held755 g h → h ∈ ({4} : Finset (Fin 6)) := by
  native_decide

/-- **Canon 755 cannot tile ℤ³** — pure counting via the density lemma:
`A = {3, 5}`, `B = {4}`, deficit 1, so no box of side ≥ 7 is tileable.
No SAT solver, no certificate. -/
theorem color755_empty : ¬ ∃ ω, IsTiling (relOfHeld held755) ω :=
  not_isTiling_of_deficient held755 {3, 5} {4}
    pair755_symm pair755_deficient (by decide)

/-- The box-level form: the 7³ box is already untileable. -/
theorem color755_box7 : ¬ Nonempty (BoxTiling (Fin 6) 7 (pairOf held755)) :=
  ColorDensity.not_tileable_of_deficit pair755_symm pair755_deficient
    (by decide) (by decide)

end AnyK3D
