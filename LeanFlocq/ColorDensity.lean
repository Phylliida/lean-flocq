/-
The color density lemma — the counting obstruction behind the fall of
canon 755 (see `monotile/RESULTS-color-density-lemma.md`, 2026-07-28).

A Wang-cube decoration assigns one of finitely many *face types* to each of
the 6 faces of the cube; a placed cube presents exactly one face of each type
(rotations permute the directions). Adjacent cubes in a tiling must show
*compatible* face types across their shared face, where compatibility is a
symmetric relation `pair` on face types induced by the rulebook.

**Lemma (density obstruction).** If the face types split into classes `A`
and `B` with `|A| > |B|` such that every type in `A` is compatible only with
types in `B`, then any tileable box of side `L > 0` satisfies

    (|A| - |B|) * L ≤ 6,

so no box with `6 < (|A| - |B|) * L` is tileable; in particular a decoration
with a deficient face-type class cannot tile boxes of arbitrary side, hence
cannot tile space. (Canon 755: `A = {3, 5}`, `B = {4}`, deficit 1, so every
box of side ≥ 7 fails by pure counting — no solver required.)

*Proof sketch.* In a tiled `L³` box there are `|A| · L³` type-A incidences
(bijectivity: each cell shows each type exactly once). Every interior type-A
face is matched across its adjacency to a type-B face, and distinct
adjacencies consume distinct B-faces, so at most `|B| · L³` type-A faces are
interior. The remaining `≥ (|A| - |B|) · L³` unmatched type-A faces must sit
on the boundary, which has only `6 · L²` outward slots. Cancel `L²`.

Note: the campaign write-up states the bound as `L ≤ 6·|B| / (|A| - |B|)`;
the counting argument proves the sharper `(|A| - |B|) · L ≤ 6` (the two agree
when `|B| = 1`, as for canon 755).

This is a standalone leaf module; it imports only Mathlib.
-/

import Mathlib

namespace ColorDensity

/-- The six face directions of a cube: an axis and a sign. -/
abbrev Dir := Fin 3 × Bool

/-- Cells of the `L³` box. -/
abbrev Cell (L : ℕ) := Fin 3 → Fin L

/-- The outward neighbour of cell `c` in direction `d` exists inside the box. -/
@[reducible]
def Interior (L : ℕ) (c : Cell L) (d : Dir) : Prop :=
  match d with
  | (ax, true) => (c ax : ℕ) + 1 < L
  | (ax, false) => 0 < (c ax : ℕ)

instance (L : ℕ) (c : Cell L) (d : Dir) : Decidable (Interior L c d) := by
  obtain ⟨ax, s⟩ := d
  cases s <;> infer_instance

/-- A tiling of the `L³` box by cubes carrying face types: every cell shows
each face type exactly once, and interior adjacent faces are compatible. -/
structure BoxTiling (α : Type*) [Fintype α] (L : ℕ) (pair : α → α → Prop) where
  face : Cell L → Dir → α
  face_bij : ∀ c, Function.Bijective (face c)
  compat : ∀ (c : Cell L) (ax : Fin 3) (h : (c ax : ℕ) + 1 < L),
    pair (face c (ax, true))
      (face (Function.update c ax ⟨(c ax : ℕ) + 1, h⟩) (ax, false))

/-- The partner incidence across an interior adjacency: the neighbouring cell
and the opposite direction. -/
def partner {L : ℕ} (c : Cell L) : (d : Dir) → Interior L c d → Cell L × Dir
  | (ax, true), h =>
    (Function.update c ax ⟨(c ax : ℕ) + 1, h⟩, (ax, false))
  | (ax, false), h =>
    (Function.update c ax ⟨(c ax : ℕ) - 1,
      (Nat.sub_lt h Nat.one_pos).trans (c ax).isLt⟩, (ax, true))

/-- Totalized partner map (identity off the interior). -/
def tpartner {L : ℕ} (ci : Cell L × Dir) : Cell L × Dir :=
  if h : Interior L ci.1 ci.2 then partner ci.1 ci.2 h else ci

/-- Boundary data of an incidence: its direction and its two tangential
coordinates. -/
def boundaryMap {L : ℕ} (ci : Cell L × Dir) : Dir × (Fin 2 → Fin L) :=
  (ci.2, fun j => ci.1 (ci.2.1.succAbove j))

/-! ## Counting incidences -/

/-- Incidences (cell, direction) showing a type from `S`. -/
def incid {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ} {pair : α → α → Prop}
    (t : BoxTiling α L pair) (S : Finset α) : Finset (Cell L × Dir) :=
  Finset.univ.filter (fun ci => t.face ci.1 ci.2 ∈ S)

/-- Each cell shows exactly `|S|` faces with type in `S`. -/
theorem card_filter_face {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}
    {pair : α → α → Prop} (t : BoxTiling α L pair) (c : Cell L) (S : Finset α) :
    (Finset.univ.filter (fun d => t.face c d ∈ S)).card = S.card := by
  refine Finset.card_bij (fun d _ => t.face c d) ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact hd.2
  · intro d₁ _ d₂ _ h
    exact (t.face_bij c).1 h
  · intro a ha
    obtain ⟨d, rfl⟩ := (t.face_bij c).2 a
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

/-- There are `L³ · |S|` incidences with type in `S`. -/
theorem card_incid {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}
    {pair : α → α → Prop} (t : BoxTiling α L pair) (S : Finset α) :
    (incid t S).card = L ^ 3 * S.card := by
  classical
  have hfiber : ∀ c : Cell L,
      ((incid t S).filter (fun ci => ci.1 = c)).card
        = (Finset.univ.filter (fun d => t.face c d ∈ S)).card := by
    intro c
    refine Finset.card_bij (fun ci _ => ci.2) ?_ ?_ ?_
    · intro ci hci
      rw [Finset.mem_filter, incid, Finset.mem_filter] at hci
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hci.2 ▸ hci.1.2⟩
    · intro ci₁ hci₁ ci₂ hci₂ h
      rw [Finset.mem_filter] at hci₁ hci₂
      exact Prod.ext (hci₁.2.trans hci₂.2.symm) h
    · intro a ha
      rw [Finset.mem_filter] at ha
      refine ⟨(c, a), ?_, rfl⟩
      rw [Finset.mem_filter, incid, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, ha.2⟩, rfl⟩
  calc (incid t S).card
      = ∑ c : Cell L, ((incid t S).filter (fun ci => ci.1 = c)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
    _ = ∑ c : Cell L, S.card :=
        Finset.sum_congr rfl fun c _ => (hfiber c).trans (card_filter_face t c S)
    _ = L ^ 3 * S.card := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        congr 1
        simp only [Cell, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
          Finset.card_univ]

/-! ## The partner map -/

/-- Interior A-incidences charge to B-incidences: the partner face is
compatible with an A-face, hence lies in `B`. -/
theorem face_partner_mem {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}
    {pair : α → α → Prop} (hsymm : ∀ g h, pair g h → pair h g)
    {A B : Finset α} (hpair : ∀ g ∈ A, ∀ h, pair g h → h ∈ B)
    (t : BoxTiling α L pair) {c : Cell L} {d : Dir} (h : Interior L c d)
    (hd : t.face c d ∈ A) :
    t.face (partner c d h).1 (partner c d h).2 ∈ B := by
  obtain ⟨ax, s⟩ := d
  cases s with
  | true =>
    exact hpair _ hd _ (t.compat c ax h)
  | false =>
    show t.face (Function.update c ax ⟨(c ax : ℕ) - 1,
      (Nat.sub_lt h Nat.one_pos).trans (c ax).isLt⟩) (ax, true) ∈ B
    have h1 : (0 : ℕ) < (c ax : ℕ) := h
    have hv1 : ((Function.update c ax ⟨(c ax : ℕ) - 1,
          (Nat.sub_lt h1 Nat.one_pos).trans (c ax).isLt⟩ : Cell L) ax : ℕ) + 1 < L := by
      rw [Function.update_self]
      show (c ax : ℕ) - 1 + 1 < L
      omega
    have hup : Function.update
        (Function.update c ax ⟨(c ax : ℕ) - 1,
          (Nat.sub_lt h1 Nat.one_pos).trans (c ax).isLt⟩) ax
        ⟨((Function.update c ax ⟨(c ax : ℕ) - 1,
            (Nat.sub_lt h1 Nat.one_pos).trans (c ax).isLt⟩ : Cell L) ax : ℕ) + 1, hv1⟩
        = c := by
      funext i
      by_cases hi : i = ax
      · subst i
        simp only [Function.update_self]
        apply Fin.ext
        show (c ax : ℕ) - 1 + 1 = (c ax : ℕ)
        omega
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
    have hcomp := t.compat
      (Function.update c ax ⟨(c ax : ℕ) - 1,
        (Nat.sub_lt h1 Nat.one_pos).trans (c ax).isLt⟩) ax hv1
    rw [hup] at hcomp
    exact hpair _ hd _ (hsymm _ _ hcomp)

/-- Distinct interior incidences have distinct partners. -/
theorem partner_inj {L : ℕ} {c₁ c₂ : Cell L} {d₁ d₂ : Dir}
    (h₁ : Interior L c₁ d₁) (h₂ : Interior L c₂ d₂)
    (heq : partner c₁ d₁ h₁ = partner c₂ d₂ h₂) : c₁ = c₂ ∧ d₁ = d₂ := by
  obtain ⟨ax₁, s₁⟩ := d₁
  obtain ⟨ax₂, s₂⟩ := d₂
  cases s₁ with
  | true =>
    cases s₂ with
    | true =>
      have hdir : (ax₁, false) = (ax₂, false) := congrArg Prod.snd heq
      have hax : ax₁ = ax₂ := congrArg Prod.fst hdir
      have hcell : Function.update c₁ ax₁ ⟨(c₁ ax₁ : ℕ) + 1, h₁⟩
          = Function.update c₂ ax₂ ⟨(c₂ ax₂ : ℕ) + 1, h₂⟩ := congrArg Prod.fst heq
      subst hax
      have hcc : c₁ ax₁ = c₂ ax₁ := by
        have hv := congrFun hcell ax₁
        rw [Function.update_self, Function.update_self] at hv
        have hv' : (c₁ ax₁ : ℕ) + 1 = (c₂ ax₁ : ℕ) + 1 := congrArg Fin.val hv
        exact Fin.ext (by omega)
      refine ⟨funext fun i => ?_, rfl⟩
      by_cases hi : i = ax₁
      · subst i; exact hcc
      · have hv := congrFun hcell i
        rwa [Function.update_of_ne hi, Function.update_of_ne hi] at hv
    | false =>
      have hdir : (ax₁, false) = (ax₂, true) := congrArg Prod.snd heq
      exact Bool.noConfusion (congrArg Prod.snd hdir)
  | false =>
    cases s₂ with
    | true =>
      have hdir : (ax₁, true) = (ax₂, false) := congrArg Prod.snd heq
      exact Bool.noConfusion (congrArg Prod.snd hdir)
    | false =>
      have hdir : (ax₁, true) = (ax₂, true) := congrArg Prod.snd heq
      have hax : ax₁ = ax₂ := congrArg Prod.fst hdir
      have hcell : Function.update c₁ ax₁ ⟨(c₁ ax₁ : ℕ) - 1,
          (Nat.sub_lt h₁ Nat.one_pos).trans (c₁ ax₁).isLt⟩
          = Function.update c₂ ax₂ ⟨(c₂ ax₂ : ℕ) - 1,
            (Nat.sub_lt h₂ Nat.one_pos).trans (c₂ ax₂).isLt⟩ := congrArg Prod.fst heq
      subst hax
      have h1 : (0 : ℕ) < (c₁ ax₁ : ℕ) := h₁
      have h2 : (0 : ℕ) < (c₂ ax₁ : ℕ) := h₂
      have hcc : c₁ ax₁ = c₂ ax₁ := by
        have hv := congrFun hcell ax₁
        rw [Function.update_self, Function.update_self] at hv
        have hv' : (c₁ ax₁ : ℕ) - 1 = (c₂ ax₁ : ℕ) - 1 := congrArg Fin.val hv
        exact Fin.ext (by omega)
      refine ⟨funext fun i => ?_, rfl⟩
      by_cases hi : i = ax₁
      · subst i; exact hcc
      · have hv := congrFun hcell i
        rwa [Function.update_of_ne hi, Function.update_of_ne hi] at hv

/-! ## The boundary injection -/

/-- Boundary incidences are determined by their direction and tangential
coordinates. -/
theorem boundaryMap_inj {L : ℕ} {ci cj : Cell L × Dir}
    (hi : ¬ Interior L ci.1 ci.2) (hj : ¬ Interior L cj.1 cj.2)
    (heq : boundaryMap ci = boundaryMap cj) : ci = cj := by
  obtain ⟨c, ax, s⟩ := ci
  obtain ⟨c', ax', s'⟩ := cj
  have hdir : (ax, s) = (ax', s') := congrArg Prod.fst heq
  obtain ⟨rfl, rfl⟩ := hdir
  have htan : (fun j => c (ax.succAbove j)) = (fun j => c' (ax.succAbove j)) :=
    congrArg Prod.snd heq
  have haxval : (c ax : ℕ) = (c' ax : ℕ) := by
    cases s with
    | true =>
      have h1 : ¬ (c ax : ℕ) + 1 < L := hi
      have h2 : ¬ (c' ax : ℕ) + 1 < L := hj
      have h3 : (c ax : ℕ) < L := (c ax).isLt
      have h4 : (c' ax : ℕ) < L := (c' ax).isLt
      omega
    | false =>
      have h1 : ¬ 0 < (c ax : ℕ) := hi
      have h2 : ¬ 0 < (c' ax : ℕ) := hj
      omega
  have hceq : c = c' := by
    funext i
    by_cases hiax : i = ax
    · subst i
      exact Fin.ext haxval
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hiax
      exact congrFun htan j
  exact Prod.ext hceq rfl

/-- There are at most `6 · L²` boundary incidences. -/
theorem card_boundary_le {L : ℕ} :
    (Finset.univ.filter (fun ci : Cell L × Dir => ¬ Interior L ci.1 ci.2)).card
      ≤ 6 * L ^ 2 := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn boundaryMap
    (fun ci _ => Finset.mem_univ _) ?_) ?_
  · intro ci hci cj hcj heq
    rw [Finset.mem_coe, Finset.mem_filter] at hci hcj
    exact boundaryMap_inj hci.2 hcj.2 heq
  · rw [Finset.card_univ]
    have hcard : Fintype.card (Dir × (Fin 2 → Fin L)) = 6 * L ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_prod]
      simp only [Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
        Finset.card_univ]
    rw [hcard]

/-! ## The density lemma -/

/-- **Density obstruction.** A deficient face-type class bounds every
tileable box: `(|A| - |B|) · L ≤ 6`. -/
theorem density_obstruction {α : Type*} [Fintype α] [DecidableEq α]
    {pair : α → α → Prop} (hsymm : ∀ g h, pair g h → pair h g)
    {A B : Finset α} (hpair : ∀ g ∈ A, ∀ h, pair g h → h ∈ B)
    (hAB : B.card < A.card) {L : ℕ} (hL : 0 < L)
    (t : BoxTiling α L pair) :
    (A.card - B.card) * L ≤ 6 := by
  classical
  have hAint : ((incid t A).filter (fun ci => Interior L ci.1 ci.2)).card
      ≤ L ^ 3 * B.card := by
    calc ((incid t A).filter (fun ci => Interior L ci.1 ci.2)).card
        ≤ (incid t B).card := by
          refine Finset.card_le_card_of_injOn tpartner
            (fun ci hci => ?_) (fun ci hci cj hcj heq => ?_)
          · rw [Finset.mem_coe, Finset.mem_filter, incid, Finset.mem_filter] at hci
            rw [tpartner, dif_pos hci.2, Finset.mem_coe, incid, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, face_partner_mem hsymm hpair t hci.2 hci.1.2⟩
          · rw [Finset.mem_coe, Finset.mem_filter] at hci hcj
            rw [tpartner, dif_pos hci.2, tpartner, dif_pos hcj.2] at heq
            obtain ⟨h1, h2⟩ := partner_inj hci.2 hcj.2 heq
            exact Prod.ext h1 h2
      _ = L ^ 3 * B.card := card_incid t B
  have hAbdy : ((incid t A).filter (fun ci => ¬ Interior L ci.1 ci.2)).card
      ≤ 6 * L ^ 2 :=
    le_trans (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))
      card_boundary_le
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := incid t A) (p := fun ci => Interior L ci.1 ci.2)
  have h2 : L ^ 3 * A.card ≤ L ^ 3 * B.card + 6 * L ^ 2 := by
    calc L ^ 3 * A.card = (incid t A).card := (card_incid t A).symm
      _ = ((incid t A).filter (fun ci => Interior L ci.1 ci.2)).card
          + ((incid t A).filter (fun ci => ¬ Interior L ci.1 ci.2)).card :=
        hsplit.symm
      _ ≤ L ^ 3 * B.card + 6 * L ^ 2 := Nat.add_le_add hAint hAbdy
  have h1 : (A.card - B.card) * L ^ 3 ≤ 6 * L ^ 2 := by
    have hB_le : L ^ 3 * B.card ≤ L ^ 3 * A.card :=
      Nat.mul_le_mul_left _ (le_of_lt hAB)
    rw [Nat.sub_mul, mul_comm A.card (L ^ 3), mul_comm B.card (L ^ 3)]
    omega
  have h3 : ((A.card - B.card) * L) * L ^ 2 ≤ 6 * L ^ 2 := by
    have e : (A.card - B.card) * L ^ 3 = (A.card - B.card) * L * L ^ 2 := by ring
    rwa [e] at h1
  exact Nat.le_of_mul_le_mul_right h3 (Nat.pow_pos hL)

/-- A deficient class with `6 < (|A| - |B|) · L` kills the `L³` box. -/
theorem not_tileable_of_deficit {α : Type*} [Fintype α] [DecidableEq α]
    {pair : α → α → Prop} (hsymm : ∀ g h, pair g h → pair h g)
    {A B : Finset α} (hpair : ∀ g ∈ A, ∀ h, pair g h → h ∈ B)
    (hAB : B.card < A.card) {L : ℕ}
    (h : 6 < (A.card - B.card) * L) :
    ¬ Nonempty (BoxTiling α L pair) := by
  intro ⟨t⟩
  have hL : 0 < L := by
    cases L with
    | zero => simp at h
    | succ n => exact Nat.succ_pos n
  have hle := density_obstruction hsymm hpair hAB hL t
  omega

/-- A relation tileable at every box size has no deficient class.
Contrapositive: a deficient class (`|A| > |B|`) forces some box — in fact
every box of side `≥ 7` once the deficit is positive — to be untileable, so
the decoration cannot tile space. -/
theorem card_le_of_tileable_all {α : Type*} [Fintype α] [DecidableEq α]
    {pair : α → α → Prop} (hsymm : ∀ g h, pair g h → pair h g)
    {A B : Finset α} (hpair : ∀ g ∈ A, ∀ h, pair g h → h ∈ B)
    (h : ∀ L, 0 < L → Nonempty (BoxTiling α L pair)) :
    A.card ≤ B.card := by
  by_contra hle
  push_neg at hle
  obtain ⟨t⟩ := h 7 (by norm_num)
  have hb := density_obstruction hsymm hpair hle (by norm_num) t
  have hd : 1 ≤ A.card - B.card := Nat.sub_pos_of_lt hle
  have h7 : 7 ≤ (A.card - B.card) * 7 := by
    calc 7 = 1 * 7 := rfl
      _ ≤ (A.card - B.card) * 7 := Nat.mul_le_mul_right 7 hd
  omega

end ColorDensity
