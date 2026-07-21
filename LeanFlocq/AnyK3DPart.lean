/-
# M3b-B7 (part 1): unions, the face partition, and relEqs

Infrastructure for the profile-equality keystone and the membership
chain (DESIGN-anyk3d-endgame.md §B7/B8):

* `unionMask` — bit-or union of masks, with bit reading and permutation
  invariance (the census's class-union is order-insensitive, which is
  what licenses B4's permuted membership).
* `partOf` — the face partition of a decoration as ℕ-lists in root
  order, with the properties B4 consumes: classes nonempty and sorted,
  flatten ~ [0,…,5].
* `mem_relEqs` — membership in a class's relevant-equation array, the
  idxOf? characterization used by the same-class/cross-class split.
-/
import Mathlib
import LeanFlocq.AnyK3DBridge

set_option maxRecDepth 100000

namespace AnyK3D

open List

/-! ## unionMask -/

/-- Bit-or union of a list of masks. -/
def unionMask (l : List ℕ) : ℕ := l.foldl (· ||| ·) 0

theorem testBit_foldl_union (l : List ℕ) (acc j : ℕ) :
    ((l.foldl (· ||| ·) acc).testBit j) =
      (acc.testBit j || l.any fun m => m.testBit j) := by
  induction l generalizing acc with
  | nil => simp
  | cons m ms ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih, Nat.testBit_or, Bool.or_assoc]

theorem testBit_unionMask (l : List ℕ) (j : ℕ) :
    (unionMask l).testBit j = l.any fun m => m.testBit j := by
  have h := testBit_foldl_union l 0 j
  rwa [Nat.zero_testBit, Bool.false_or] at h

theorem unionMask_perm {l₁ l₂ : List ℕ} (h : l₁ ~ l₂) :
    unionMask l₁ = unionMask l₂ := by
  have hany : ∀ p : ℕ → Bool, l₁.any p = l₂.any p := by
    intro p
    induction h with
    | nil => rfl
    | cons x h ih => simp [List.any_cons, ih]
    | swap x y l =>
      simp only [List.any_cons]
      cases p x <;> cases p y <;> cases l.any p <;> rfl
    | trans h1 h2 ih1 ih2 => rw [ih1, ih2]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_unionMask, testBit_unionMask, hany]

/-! ## finRange sortedness -/

theorem sorted_finRange (n : ℕ) : (List.finRange n).Sorted (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last]
    show ((finRange n).map Fin.castSucc ++ [Fin.last n]).Pairwise (· < ·)
    rw [List.pairwise_append, List.pairwise_map]
    refine ⟨List.Pairwise.imp (fun h => h) ih, List.pairwise_singleton _ _,
      fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rw [hb]
    exact Fin.castSucc_lt_last i

theorem sorted_finRange_le (n : ℕ) : (List.finRange n).Sorted (· ≤ ·) :=
  List.Pairwise.imp le_of_lt (sorted_finRange n)

/-! ## partOf -/

/-- The face partition: classes (as ℕ lists) of distinct roots, in root
order. -/
def partOf (K : ℕ) (d : Dec K) : List (List ℕ) :=
  ((List.finRange 6).filter fun g => rootF K d g == g).map fun g =>
    (clsOf K d g).map Fin.val

theorem clsOf_sorted (K : ℕ) (d : Dec K) (g : Fin 6) :
    (clsOf K d g).Sorted (· ≤ ·) :=
  List.Sorted.filter _ (sorted_finRange_le 6)

theorem clsNat_sorted (K : ℕ) (d : Dec K) (g : Fin 6) :
    ((clsOf K d g).map Fin.val).Sorted (· ≤ ·) := by
  show ((clsOf K d g).map Fin.val).Pairwise (· ≤ ·)
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun h => h) (clsOf_sorted K d g)

theorem partOf_classes (K : ℕ) (d : Dec K) :
    ∀ c ∈ partOf K d, c ≠ [] ∧ c.Sorted (· ≤ ·) := by
  intro c hc
  simp only [partOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and] at hc
  obtain ⟨g, -, rfl⟩ := hc
  refine ⟨?_, clsNat_sorted K d g⟩
  intro he
  have hne := clsOf_ne_nil K d g
  simp only [List.map_eq_nil_iff] at he
  exact hne he

theorem mem_partOf_rootF (K : ℕ) (d : Dec K) (g : Fin 6) :
    (clsOf K d (rootF K d g)).map Fin.val ∈ partOf K d := by
  simp only [partOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and]
  exact ⟨rootF K d g, rootF_rootF K d g, rfl⟩

theorem mem_flatten_partOf_iff (K : ℕ) (d : Dec K) (x : ℕ) :
    x ∈ (partOf K d).flatten ↔ x ∈ (List.finRange 6).map Fin.val := by
  constructor
  · intro hx
    obtain ⟨c, hcP, hxc⟩ := List.mem_flatten.mp hx
    simp only [partOf, List.mem_map, List.mem_filter, List.mem_finRange,
      beq_iff_eq, true_and] at hcP
    obtain ⟨g, -, rfl⟩ := hcP
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hxc
    exact List.mem_map.mpr ⟨h, List.mem_finRange h, rfl⟩
  · intro hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    refine List.mem_flatten.mpr
      ⟨(clsOf K d (rootF K d h)).map Fin.val, mem_partOf_rootF K d h, ?_⟩
    refine List.mem_map.mpr ⟨h, ?_, rfl⟩
    simp only [clsOf, List.mem_filter, List.mem_finRange, decide_eq_true_eq]
    exact ⟨trivial, (rootF_rootF K d h).symm⟩

/-- The class of a face is unique: if `x` lies in two partition classes,
they coincide (both roots equal `x`'s root). -/
theorem partOf_class_unique (K : ℕ) (d : Dec K) (x : ℕ)
    {c₁ c₂ : List ℕ} (hc₁ : c₁ ∈ partOf K d) (hc₂ : c₂ ∈ partOf K d)
    (hx₁ : x ∈ c₁) (hx₂ : x ∈ c₂) : c₁ = c₂ := by
  simp only [partOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and] at hc₁ hc₂
  obtain ⟨g₁, hr₁, rfl⟩ := hc₁
  obtain ⟨g₂, hr₂, rfl⟩ := hc₂
  obtain ⟨h₁, hh₁, e₁⟩ := List.mem_map.mp hx₁
  obtain ⟨h₂, hh₂, e₂⟩ := List.mem_map.mp hx₂
  have he : h₁ = h₂ := Fin.ext (e₁.trans e₂.symm)
  have h1 := mem_clsOf_root hh₁
  have h2 := mem_clsOf_root hh₂
  rw [he] at h1
  have hr : rootF K d g₁ = rootF K d g₂ := by rw [← h1, ← h2]
  rw [← hr₁, ← hr₂, hr]

/-- A sum of ≤ 1 terms with at most one nonzero term is ≤ 1. -/
theorem sum_le_one_of {α : Type*} [BEq α] [LawfulBEq α] (l : List α) (f : α → ℕ)
    (h1 : ∀ a ∈ l, f a ≤ 1)
    (h2 : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a = 0 ∨ f b = 0)
    (hnd : l.Nodup) : (l.map f).sum ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases hx : f x = 0
    · rw [hx, Nat.zero_add]
      exact ih (fun a ha => h1 a (List.mem_cons_of_mem _ ha))
        (fun a ha b hb hab =>
          h2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)
        (List.nodup_cons.mp hnd).2
    · have hfx : f x = 1 := by
        have := h1 x List.mem_cons_self
        omega
      have hzero : ∀ b ∈ xs, f b = 0 := by
        intro b hb
        have hbne : b ≠ x := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hb)
        rcases h2 b (List.mem_cons_of_mem _ hb) x List.mem_cons_self hbne with h | h
        · exact h
        · exact absurd h hx
      have hsum : (xs.map f).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro y hy
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        exact hzero b hb
      omega

theorem nodup_flatten_partOf (K : ℕ) (d : Dec K) :
    ((partOf K d).flatten).Nodup := by
  rw [List.nodup_iff_count]
  intro x
  rw [List.count_flatten]
  apply sum_le_one_of
  · intro c hc
    simp only [partOf, List.mem_map, List.mem_filter, List.mem_finRange,
      beq_iff_eq, true_and] at hc
    obtain ⟨g, -, rfl⟩ := hc
    have hnd : ((clsOf K d g).map Fin.val).Nodup :=
      ((List.nodup_finRange 6).filter _).map (fun _ _ h => Fin.ext h)
    rw [List.nodup_iff_count] at hnd
    exact hnd x
  · intro c₁ hc₁ c₂ hc₂ hne
    by_cases hx1 : x ∈ c₁
    · by_cases hx2 : x ∈ c₂
      · exact absurd (partOf_class_unique K d x hc₁ hc₂ hx1 hx2) hne
      · exact Or.inr (List.count_eq_zero_of_not_mem hx2)
    · exact Or.inl (List.count_eq_zero_of_not_mem hx1)
  · apply List.Nodup.map_on _ ((List.nodup_finRange 6).filter _)
    intro g₁ hg₁ g₂ hg₂ h
    have hr₁ : rootF K d g₁ = g₁ := beq_iff_eq.mp (List.mem_filter.mp hg₁).2
    have hr₂ : rootF K d g₂ = g₂ := beq_iff_eq.mp (List.mem_filter.mp hg₂).2
    have hne1 := rootF_mem_clsOf K d g₁
    have hmem : (rootF K d g₁).val ∈ (clsOf K d g₂).map Fin.val := by
      rw [← h]
      exact List.mem_map.mpr ⟨rootF K d g₁, hne1, rfl⟩
    obtain ⟨h₂, hh₂, e₂⟩ := List.mem_map.mp hmem
    have he : h₂ = rootF K d g₁ := Fin.ext e₂
    have h2 := mem_clsOf_root hh₂
    rw [he, rootF_rootF] at h2
    rw [← hr₁, ← hr₂, h2]

theorem flatten_partOf_perm (K : ℕ) (d : Dec K) :
    (partOf K d).flatten ~ (List.finRange 6).map Fin.val := by
  rw [List.perm_iff_count]
  intro x
  have hn1 := nodup_flatten_partOf K d
  have hn2 : ((List.finRange 6).map Fin.val).Nodup :=
    (List.nodup_finRange 6).map (fun _ _ h => Fin.ext h)
  rw [List.nodup_iff_count] at hn1 hn2
  by_cases hx : x ∈ (partOf K d).flatten
  · have h1 : ((partOf K d).flatten).count x = 1 :=
      le_antisymm (hn1 x) (List.count_pos_iff.mpr hx)
    have hx2 : x ∈ (List.finRange 6).map Fin.val :=
      (mem_flatten_partOf_iff K d x).mp hx
    have h2 : ((List.finRange 6).map Fin.val).count x = 1 :=
      le_antisymm (hn2 x) (List.count_pos_iff.mpr hx2)
    rw [h1, h2]
  · have h1 : ((partOf K d).flatten).count x = 0 :=
      List.count_eq_zero_of_not_mem hx
    have hx2 : x ∉ (List.finRange 6).map Fin.val :=
      fun h => hx ((mem_flatten_partOf_iff K d x).mpr h)
    have h2 : ((List.finRange 6).map Fin.val).count x = 0 :=
      List.count_eq_zero_of_not_mem hx2
    rw [h1, h2]

/-! ## relEqs -/

/-- Membership in a class's relevant-equation array: the idxOf?
characterization (same-class case of the keystone split). -/
theorem mem_relEqs (members : List ℕ) (i ja jb t : ℕ) :
    (i, ja, jb, t) ∈ relEqs members ↔
      i < 84 ∧ members.idxOf? (eqFaceA.getD i 0) = some ja ∧
      members.idxOf? (eqFaceB.getD i 0) = some jb ∧ t = eqTau.getD i 0 := by
  unfold relEqs
  rw [Array.mem_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨i', hi', hi''⟩
    rw [List.mem_range] at hi'
    split at hi''
    · rename_i ja' jb' hA hB
      simp only [Option.some.injEq] at hi''
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hi''
      exact ⟨hi', hA, hB, rfl⟩
    · simp at hi''
  · rintro ⟨hi, hA, hB, rfl⟩
    exact ⟨i, by rwa [List.mem_range], by rw [hA, hB]⟩

end AnyK3D
