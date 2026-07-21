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

/-! ## B7 stage 2: table bounds, class roots, positions -/

theorem eqFaceA_lt : ∀ i < 84, eqFaceA.getD i 0 < 6 := by native_decide
theorem eqFaceB_lt : ∀ i < 84, eqFaceB.getD i 0 < 6 := by native_decide
theorem eqTau_lt : ∀ i < 84, eqTau.getD i 0 < 8 := by native_decide

theorem efa_val (i : ℕ) (hi : i < 84) : (efa ⟨i, hi⟩).val = eqFaceA.getD i 0 := by
  show (eqFaceA.getD i 0) % 6 = eqFaceA.getD i 0
  exact Nat.mod_eq_of_lt (eqFaceA_lt i hi)

theorem efb_val (i : ℕ) (hi : i < 84) : (efb ⟨i, hi⟩).val = eqFaceB.getD i 0 := by
  show (eqFaceB.getD i 0) % 6 = eqFaceB.getD i 0
  exact Nat.mod_eq_of_lt (eqFaceB_lt i hi)

theorem eta_val (i : ℕ) (hi : i < 84) : (eta ⟨i, hi⟩).val = eqTau.getD i 0 := by
  show (eqTau.getD i 0) % 8 = eqTau.getD i 0
  exact Nat.mod_eq_of_lt (eqTau_lt i hi)

/-- The chosen gains for a class (Classical choice of B5's
`exists_cls_gains`). -/
noncomputable def clsGains (K : ℕ) (d : Dec K) (g : Fin 6) : Fin 6 → Gain :=
  Classical.choose (exists_cls_gains K d g)

theorem clsGains_spec (K : ℕ) (d : Dec K) (g h : Fin 6)
    (hh : h ∈ clsOf K d g) : d h = actF (clsGains K d g h) (d (rootF K d g)) :=
  (Classical.choose_spec (exists_cls_gains K d g)).1 h hh

theorem clsGains_root (K : ℕ) (d : Dec K) (g : Fin 6) :
    clsGains K d g (rootF K d g) = ((0 : Fin 8), false) :=
  (Classical.choose_spec (exists_cls_gains K d g)).2

/-- The head of a root's class is the root (the census's position-0
convention, realized). -/
theorem clsOf_head (K : ℕ) (d : Dec K) (g : Fin 6) (hg : rootF K d g = g) :
    (clsOf K d g).getD 0 g = g := by
  obtain ⟨a, t, ha⟩ := List.exists_cons_of_ne_nil (clsOf_ne_nil K d g)
  have hsorted := clsOf_sorted K d g
  rw [ha] at hsorted
  have hle : ∀ y ∈ t, a ≤ y := (List.sorted_cons.mp hsorted).1
  have hmem := rootF_mem_clsOf K d g
  rw [ha] at hmem
  have hga : rootF K d a = g := by
    have h := mem_clsOf_root (K := K) (d := d) (g := g) (h := a)
      (by rw [ha]; exact List.mem_cons_self)
    rwa [hg] at h
  have h1 : g ≤ a := by rw [← hga]; exact rootF_le K d a
  have h2 : a ≤ g := by
    rcases List.mem_cons.mp hmem with rfl | ht
    · rw [hg]
    · have h3 := hle (rootF K d g) ht
      rwa [hg] at h3
  have haeq : a = g := by
    apply Fin.ext
    exact Nat.le_antisymm h2 h1
  rw [ha, haeq]
  rfl

/-- `classMask` stays below 2^84 when the entries' bit indices do. -/
theorem classMask_lt (re : Array (ℕ × ℕ × ℕ × ℕ)) (idx H : ℕ)
    (hre : ∀ e ∈ re.toList, e.1 < 84) : classMask re idx H < 2 ^ 84 := by
  unfold classMask
  rw [← Array.foldl_toList]
  have gen : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)), (∀ e ∈ l, e.1 < 84) →
      ∀ acc : ℕ, acc < 2 ^ 84 →
        (l.foldl (fun acc e =>
          if H.testBit (gmul16 (ginv16 (gainAt idx e.2.1))
            (gmul16 (negTau e.2.2.2) (gainAt idx e.2.2.1)))
          then acc ||| (1 <<< e.1) else acc) acc) < 2 ^ 84 := by
    intro l hl
    induction l with
    | nil => intro acc hacc; exact hacc
    | cons e es ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
      split
      · have h1 : (1 <<< e.1) < 2 ^ 84 := by
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_right (by norm_num) (hl e List.mem_cons_self)
        exact Nat.or_lt_two_pow hacc h1
      · exact hacc
  exact gen re.toList hre 0 (by norm_num)

theorem relEqs_fst_lt (members : List ℕ) :
    ∀ e ∈ (relEqs members).toList, e.1 < 84 := by
  intro e he
  obtain ⟨i, ja, jb, t⟩ := e
  exact (mem_relEqs members i ja jb t).mp (Array.mem_def.mpr he) |>.1

/-- The gain code at a member position of the class list (the position
form of B5's digit lemma). -/
theorem gainAt_clsIdx_pos (K : ℕ) (d : Dec K) (g : Fin 6)
    (h : Fin 6) (hg : rootF K d g = g) (ja : ℕ)
    (hja : ((clsOf K d g).map Fin.val).idxOf? h.val = some ja) :
    gainAt (clsIdx K d g (clsGains K d g)) ja = encG (clsGains K d g h) := by
  have hb : ja < (clsOf K d g).length := by
    obtain ⟨hb, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hja
    rwa [List.length_map] at hb
  have hget : (clsOf K d g)[ja]'hb = h := by
    obtain ⟨hb2, h2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hja
    have hv : ((clsOf K d g).map Fin.val)[ja]'hb2 = h.val := beq_iff_eq.mp h2
    rw [List.getElem_map] at hv
    exact Fin.ext hv
  cases ja with
  | zero =>
    rw [gainAt_clsIdx_zero]
    have hge : h = g := by
      have h0 := clsOf_head K d g hg
      have he : (clsOf K d g).getD 0 g = h := by
        rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_pos hb]
        exact hget
      rw [h0] at he
      exact he.symm
    have hroot : clsGains K d g g = ((0 : Fin 8), false) := by
      have h1 := clsGains_root K d g
      rwa [hg] at h1
    rw [hge, hroot]
    rfl
  | succ j' =>
    have hb' : j' < (clsOf K d g).tail.length := by
      rw [List.length_tail]; omega
    rw [gainAt_clsIdx K d g (clsGains K d g) (j' + 1) (by omega)]
    have hgd : ((clsOf K d g).tail.map fun h => encG (clsGains K d g h)).getD
        j' 0 = encG (clsGains K d g h) := by
      rw [List.getD_eq_getElem?_getD, List.getD_getElem?,
        dif_pos (by rw [List.length_map]; exact hb'), List.getElem_map,
        List.getElem_tail, hget]
    exact hgd

/-- The encoded stabilizer-chain identity (B2 assembled). -/
theorem encG_stab_chain (wg wh : Gain) (t : Fin 8) :
    encG (gmul (ginv wg) (gmul (t, true) wh)) =
      gmul16 (ginv16 (encG wg)) (gmul16 (negTau t.val) (encG wh)) := by
  rw [ginv16_encG, negTau_encG, gmul16_encG, gmul16_encG]

/-- The same-class bridge: a held equation is exactly the class's
classMask bit condition. -/
theorem held_iff_classMask_bit (K : ℕ) (d : Dec K) (g : Fin 6)
    (hg : rootF K d g = g) (i : Fin 84)
    (ha : rootF K d (efa i) = g) (hb : rootF K d (efb i) = g)
    (ja jb : ℕ)
    (hja : ((clsOf K d g).map Fin.val).idxOf? (efa i).val = some ja)
    (hjb : ((clsOf K d g).map Fin.val).idxOf? (efb i).val = some jb) :
    eqHolds K d (efa i) (efb i) (eta i) = true ↔
      (stabMask (d g)).testBit
        (gmul16 (ginv16 (gainAt (clsIdx K d g (clsGains K d g)) ja))
          (gmul16 (negTau (eta i).val)
            (gainAt (clsIdx K d g (clsGains K d g)) jb))) = true := by
  rw [gainAt_clsIdx_pos K d g (efa i) hg ja hja,
    gainAt_clsIdx_pos K d g (efb i) hg jb hjb,
    ← encG_stab_chain]
  have hga : d (efa i) = actF (clsGains K d g (efa i)) (d g) := by
    have hmem : efa i ∈ clsOf K d g := by
      simp only [clsOf, List.mem_filter, List.mem_finRange, decide_eq_true_eq]
      exact ⟨trivial, by rw [ha, hg]⟩
    have h := clsGains_spec K d g (efa i) hmem
    rwa [hg] at h
  have hgb : d (efb i) = actF (clsGains K d g (efb i)) (d g) := by
    have hmem : efb i ∈ clsOf K d g := by
      simp only [clsOf, List.mem_filter, List.mem_finRange, decide_eq_true_eq]
      exact ⟨trivial, by rw [hb, hg]⟩
    have h := clsGains_spec K d g (efb i) hmem
    rwa [hg] at h
  rw [eqHolds_iff_stab K d (efa i) (efb i) (eta i) (d g)
    (clsGains K d g (efa i)) (clsGains K d g (efb i)) hga hgb,
    testBit_stabMask (d g) _ (encG_lt _), decG_encG, decide_eq_true_eq]

/-! ## B7 stage 3: the keystone -/

theorem clsOf_nodup (K : ℕ) (d : Dec K) (g : Fin 6) : (clsOf K d g).Nodup :=
  (List.nodup_finRange 6).filter _

/-- Position of a face in its class: the idxOf? form the census's
`relEqs` needs. -/
theorem idxOf?_clsOf (K : ℕ) (d : Dec K) (g h : Fin 6)
    (hh : h ∈ clsOf K d g) :
    ∃ ja, ((clsOf K d g).map Fin.val).idxOf? h.val = some ja := by
  obtain ⟨ja, hja, hget⟩ := List.mem_iff_getElem.mp hh
  have hb : ja < ((clsOf K d g).map Fin.val).length := by
    rw [List.length_map]; exact hja
  refine ⟨ja, List.findIdx?_eq_some_iff_getElem.mpr ⟨hb, ?_, ?_⟩⟩
  · have hv : ((clsOf K d g).map Fin.val)[ja]'hb = h.val := by
      rw [List.getElem_map, hget]
    exact beq_iff_eq.mpr hv
  · intro j hji hc
    have hbj : j < (clsOf K d g).length := Nat.lt_trans hji hja
    have hjb : j < ((clsOf K d g).map Fin.val).length := Nat.lt_trans hji hb
    have hv : (clsOf K d g)[j]'hbj = h := by
      have hv' : ((clsOf K d g).map Fin.val)[j]'hjb = h.val :=
        beq_iff_eq.mp hc
      rw [List.getElem_map] at hv'
      exact Fin.ext hv'
    have e1 : (clsOf K d g)[j]? = some h :=
      List.getElem?_eq_some_iff.mpr ⟨hbj, hv⟩
    have e2 : (clsOf K d g)[ja]? = some h :=
      List.getElem?_eq_some_iff.mpr ⟨hja, hget⟩
    have hij : j = ja :=
      List.getElem?_inj hbj (clsOf_nodup K d g) (e1.trans e2.symm)
    exact absurd hij (Nat.ne_of_lt hji)

/-- Membership from a position (the converse direction). -/
theorem mem_clsOf_of_idxOf? (K : ℕ) (d : Dec K) (g h : Fin 6) (p : ℕ)
    (hp : ((clsOf K d g).map Fin.val).idxOf? h.val = some p) :
    h ∈ clsOf K d g := by
  obtain ⟨hb2, h2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hp
  have hb3 : p < (clsOf K d g).length := by rwa [List.length_map] at hb2
  have hv : (clsOf K d g)[p]'hb3 = h := by
    have hv' : ((clsOf K d g).map Fin.val)[p]'hb2 = h.val := beq_iff_eq.mp h2
    rw [List.getElem_map] at hv'
    exact Fin.ext hv'
  rw [← hv]
  exact List.getElem_mem hb3

/-- **The profile equality.** A decoration's 84-bit held profile is
exactly the union over its face classes of the census's class masks —
the completeness keystone. -/
theorem profileMask_eq_union (K : ℕ) (d : Dec K) :
    profileMask (heldOf K d) =
      unionMask (((List.finRange 6).filter fun g => rootF K d g == g).map
        fun g =>
          classMask (relEqs ((clsOf K d g).map Fin.val))
            (clsIdx K d g (clsGains K d g)) (stabMask (d g))) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 84
  · rw [testBit_profileMask (heldOf K d) j hj, testBit_unionMask,
      Bool.eq_iff_iff]
    constructor
    · -- held → some class's mask carries the bit
      intro hheld
      have hrel : related K d (efa ⟨j, hj⟩) (efb ⟨j, hj⟩) :=
        ⟨(eta ⟨j, hj⟩, true), (eqHolds_iff_act K d _ _ _).mp hheld⟩
      have hroots : rootF K d (efa ⟨j, hj⟩) = rootF K d (efb ⟨j, hj⟩) :=
        rootF_eq_iff_related.mpr hrel
      set g := rootF K d (efa ⟨j, hj⟩) with hg_def
      have hg : rootF K d g = g := rootF_rootF K d _
      have hroots2 : rootF K d (efb ⟨j, hj⟩) = g := hroots.symm
      have hmemA : efa ⟨j, hj⟩ ∈ clsOf K d g := by
        simp only [clsOf, List.mem_filter, List.mem_finRange,
          decide_eq_true_eq]
        refine ⟨trivial, ?_⟩
        rw [hg_def]
        exact (rootF_rootF K d _).symm
      have hmemB : efb ⟨j, hj⟩ ∈ clsOf K d g := by
        simp only [clsOf, List.mem_filter, List.mem_finRange,
          decide_eq_true_eq]
        refine ⟨trivial, ?_⟩
        rw [hroots2, hg]
      obtain ⟨ja, hja⟩ := idxOf?_clsOf K d g (efa ⟨j, hj⟩) hmemA
      obtain ⟨jb, hjb⟩ := idxOf?_clsOf K d g (efb ⟨j, hj⟩) hmemB
      rw [List.any_eq_true]
      refine ⟨_, List.mem_map.mpr
          ⟨g, List.mem_filter.mpr ⟨List.mem_finRange _, beq_iff_eq.mpr hg⟩,
           rfl⟩, ?_⟩
      rw [testBit_classMask]
      rw [List.any_eq_true]
      have hbit2 := (held_iff_classMask_bit K d g hg ⟨j, hj⟩ hg_def.symm
          hroots2 ja jb hja hjb).mp hheld
      rw [eta_val j hj] at hbit2
      exact ⟨(j, ja, jb, eqTau.getD j 0),
        Array.mem_def.mp ((mem_relEqs ((clsOf K d g).map Fin.val) j ja jb
            (eqTau.getD j 0)).mpr
          ⟨hj, efa_val j hj ▸ hja, efb_val j hj ▸ hjb, rfl⟩),
        by rw [Bool.and_eq_true]; exact ⟨hbit2, by simp⟩⟩
    · -- some class's mask carries the bit → held
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨m, hm, hbit⟩ := hany
      obtain ⟨g, hgP, rfl⟩ := List.mem_map.mp hm
      have hg : rootF K d g = g := beq_iff_eq.mp (List.mem_filter.mp hgP).2
      rw [testBit_classMask, List.any_eq_true] at hbit
      obtain ⟨⟨i, ja, jb, t⟩, hentry, hcond⟩ := hbit
      rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hcond, hbitj⟩ := hcond
      obtain ⟨hi, hja, hjb, ht⟩ :=
        (mem_relEqs ((clsOf K d g).map Fin.val) i ja jb t).mp
          (Array.mem_def.mpr hentry)
      subst hbitj
      subst ht
      have hja' : ((clsOf K d g).map Fin.val).idxOf? (efa ⟨i, hi⟩).val =
          some ja := by rw [← efa_val i hi] at hja; exact hja
      have hjb' : ((clsOf K d g).map Fin.val).idxOf? (efb ⟨i, hi⟩).val =
          some jb := by rw [← efb_val i hi] at hjb; exact hjb
      have hra : rootF K d (efa ⟨i, hi⟩) = g := by
        have h := mem_clsOf_root (mem_clsOf_of_idxOf? K d g _ _ hja')
        rwa [hg] at h
      have hrb : rootF K d (efb ⟨i, hi⟩) = g := by
        have h := mem_clsOf_root (mem_clsOf_of_idxOf? K d g _ _ hjb')
        rwa [hg] at h
      dsimp only at hcond
      rw [← eta_val i hi] at hcond
      exact (held_iff_classMask_bit K d g hg ⟨i, hi⟩ hra hrb ja jb
        hja' hjb').mpr hcond
  · rw [testBit_profileMask_ge (heldOf K d) j (by omega)]
    rw [testBit_unionMask, eq_comm, List.any_eq_false]
    intro m hm
    obtain ⟨g, hgP, rfl⟩ := List.mem_map.mp hm
    have h84 : 84 ≤ j := by omega
    have hb : (classMask (relEqs ((clsOf K d g).map Fin.val))
        (clsIdx K d g (clsGains K d g)) (stabMask (d g))).testBit j = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le
          (classMask_lt _ _ _ (relEqs_fst_lt _))
          (Nat.pow_le_pow_right (by norm_num) h84))
    simp [hb]

end AnyK3D
