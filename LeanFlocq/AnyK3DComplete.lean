/-
# M3b-B8: the membership chain → census_complete

The final links of census completeness (DESIGN-anyk3d-endgame.md §B8):

* push/dedup fold membership lemmas for the census's accumulators;
* `mem_classOptionsFast` — a realized class mask (B6's stabilizer mask
  + B5's tuple index) is enumerated by `classOptionsFast`;
* `mem_censusFast` — the union of per-class masks over an
  enumerator-realizable partition (B4) is in `censusFast`;
* **`census_complete`** — the assembly via B7's profile equality.
-/
import Mathlib
import LeanFlocq.AnyK3DPart

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AnyK3D

open List

/-! ## push/dedup fold membership -/

theorem mem_foldl_push_id_subset (l : List ℕ) (acc : Array ℕ) (y : ℕ)
    (hy : y ∈ acc.toList) :
    y ∈ (l.foldl (fun a m => a.push m) acc).toList := by
  induction l generalizing acc with
  | nil => exact hy
  | cons b bs ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [Array.toList_push]
    exact List.mem_append_left _ hy

theorem mem_foldl_push_id (l : List ℕ) (acc : Array ℕ) (y : ℕ)
    (hy : y ∈ l) :
    y ∈ (l.foldl (fun a m => a.push m) acc).toList := by
  induction l generalizing acc with
  | nil => simp at hy
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hb
    · apply mem_foldl_push_id_subset
      rw [Array.toList_push]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ih _ hb

theorem mem_foldl_push_gen_subset {β : Type*} (l : List ℕ) (f : ℕ → β)
    (acc : Array β) (y : β) (hy : y ∈ acc.toList) :
    y ∈ (l.foldl (fun acc b => acc.push (f b)) acc).toList := by
  induction l generalizing acc with
  | nil => exact hy
  | cons b bs ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [Array.toList_push]
    exact List.mem_append_left _ hy

theorem mem_foldl_push_gen {β : Type*} (l : List ℕ) (f : ℕ → β) (acc : Array β)
    (a : ℕ) (ha : a ∈ l) :
    f a ∈ (l.foldl (fun acc b => acc.push (f b)) acc).toList := by
  induction l generalizing acc with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | hb
    · apply mem_foldl_push_gen_subset
      rw [Array.toList_push]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact ih _ hb

theorem mem_foldl_dedup (l : List ℕ) (x : ℕ) (acc : Array ℕ) :
    x ∈ acc.toList ∨ x ∈ l →
      x ∈ (l.foldl (fun acc y => if acc.back? = some y then acc
        else acc.push y) acc).toList := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    intro h
    simp only [List.foldl_cons]
    split
    · rename_i hb
      apply ih
      rcases h with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | hys
        · exact Or.inl (Array.mem_def.mp (Array.mem_of_back? hb))
        · exact Or.inr hys
    · rename_i hb
      apply ih
      rcases h with h | h
      · exact Or.inl (by
          rw [Array.toList_push]
          exact List.mem_append_left _ h)
      · rcases List.mem_cons.mp h with rfl | hys
        · exact Or.inl (by
            rw [Array.toList_push]
            exact List.mem_append_right _ (List.mem_singleton_self _))
        · exact Or.inr hys

theorem mem_dedupSorted {a : Array ℕ} {x : ℕ} (h : x ∈ a.toList) :
    x ∈ (dedupSorted a).toList := by
  unfold dedupSorted
  have hm : x ∈ a.toList.mergeSort (· ≤ ·) := List.mem_mergeSort.mpr h
  exact mem_foldl_dedup _ x #[] (Or.inr hm)

/-! ## mem_classOptionsFast -/

/-- The realized class mask is enumerated: B6's stabilizer mask is a
census subgroup and B5's tuple index fits the range, so
`classOptionsFast members` contains the class's mask. -/
theorem mem_classOptionsFast (members : List ℕ) (idx H : ℕ)
    (hH : H ∈ subMasks.toList) (hidx : idx < 16 ^ (members.length - 1)) :
    classMask (relEqs members) idx H ∈ (classOptionsFast members).toList := by
  unfold classOptionsFast
  apply mem_dedupSorted
  rw [← Array.foldl_toList]
  -- the inner fold introduces classMask for idx at H's position
  have hinner : ∀ acc : Array ℕ, classMask (relEqs members) idx H ∈
      ((List.range (16 ^ (members.length - 1))).foldl
        (fun acc i => acc.push (classMask (relEqs members) i H)) acc).toList := by
    intro acc
    exact mem_foldl_push_gen _ _ acc idx (List.mem_range.mpr hidx)
  -- preservation: membership in the accumulator survives later folds
  have hpres : ∀ (Hs : List ℕ) (acc : Array ℕ),
      classMask (relEqs members) idx H ∈ acc.toList →
      classMask (relEqs members) idx H ∈
        (Hs.foldl
          (fun acc H' => (List.range (16 ^ (members.length - 1))).foldl
            (fun acc i => acc.push (classMask (relEqs members) i H')) acc)
          acc).toList := by
    intro Hs acc h
    induction Hs generalizing acc with
    | nil => exact h
    | cons H' Hs' ih =>
      simp only [List.foldl_cons]
      apply ih
      clear ih
      induction (List.range (16 ^ (members.length - 1)) : List ℕ)
        generalizing acc with
      | nil => exact h
      | cons i is ih2 =>
        simp only [List.foldl_cons]
        apply ih2
        rw [Array.toList_push]
        exact List.mem_append_left _ h
  -- chain: H ∈ subMasks, introduced at H, preserved after
  have houter : ∀ (Hs : List ℕ) (acc : Array ℕ), H ∈ Hs →
      classMask (relEqs members) idx H ∈
        (Hs.foldl
          (fun acc H' => (List.range (16 ^ (members.length - 1))).foldl
            (fun acc i => acc.push (classMask (relEqs members) i H')) acc)
          acc).toList := by
    intro Hs acc hHs
    induction Hs generalizing acc with
    | nil => simp at hHs
    | cons H' Hs' ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hHs with rfl | hHs'
      · exact hpres Hs' _ (hinner acc)
      · exact ih _ hHs'
  exact houter subMasks.toList #[] hH

/-! ## mem_censusFast -/

/-- Every union of per-class options (left fold) lies in the partition's
combination list. -/
theorem mem_combos (part : List (List ℕ)) (choice : List ℕ → ℕ) :
    ∀ (accList : List ℕ) (init : ℕ),
      (∀ cls ∈ part, choice cls ∈ (classOptionsFast cls).toList) →
      init ∈ accList →
      (part.foldl (fun m cls => m ||| choice cls) init) ∈
        (part.foldl (fun (accList : List ℕ) cls =>
          accList.flatMap fun m =>
            ((classOptionsFast cls).map (m ||| ·)).toList) accList) := by
  induction part with
  | nil => intro accList init _ hin; exact hin
  | cons cls rest ih =>
    intro accList init h hin
    simp only [List.foldl_cons]
    refine ih _ _ (fun cls' hcls' => h cls' (List.mem_cons_of_mem _ hcls')) ?_
    rw [List.mem_flatMap]
    refine ⟨init, hin, ?_⟩
    have hopt := h cls List.mem_cons_self
    have hthis : (init ||| choice cls) ∈
        ((classOptionsFast cls).toList.map (init ||| ·)) :=
      List.mem_map.mpr ⟨choice cls, hopt, rfl⟩
    rwa [Array.toList_map]

/-- The census union membership: a partition's option-union is in
`censusFast`. -/
theorem census_pres (u : ℕ) (ps : List (List (List ℕ))) :
    ∀ acc : Array ℕ, u ∈ acc.toList →
      u ∈ (ps.foldl (fun acc p =>
        (p.foldl (fun accList cls =>
          accList.flatMap fun m =>
            ((classOptionsFast cls).map (m ||| ·)).toList) [0]).foldl
          (fun a m => a.push m) acc) acc).toList := by
  induction ps with
  | nil => intro acc h; exact h
  | cons q qs ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (mem_foldl_push_id_subset _ _ _ h)

theorem mem_censusFast (part : List (List ℕ))
    (hp : part ∈ partitionsN [0, 1, 2, 3, 4, 5])
    (choice : List ℕ → ℕ)
    (h : ∀ cls ∈ part, choice cls ∈ (classOptionsFast cls).toList) :
    ((part.map choice).foldl (· ||| ·) 0) ∈ censusFast.toList := by
  rw [List.foldl_map]
  show (part.foldl (fun x y => x ||| choice y) 0) ∈ censusFast.toList
  unfold censusFast
  apply mem_dedupSorted
  -- the union is in part's combos
  have hcomb : (part.foldl (fun x y => x ||| choice y) 0) ∈
      (part.foldl (fun accList cls =>
        accList.flatMap fun m =>
          ((classOptionsFast cls).map (m ||| ·)).toList) [0]) := by
    apply mem_combos part choice [0] 0 h
    exact List.mem_singleton_self _
  -- combos gets pushed at part's position in parts; preserved after
  have hmem : ∀ acc : Array ℕ,
      (part.foldl (fun x y => x ||| choice y) 0) ∈
        ((part.foldl (fun accList cls =>
          accList.flatMap fun m =>
            ((classOptionsFast cls).map (m ||| ·)).toList) [0]).foldl
          (fun a m => a.push m) acc).toList :=
    fun acc => mem_foldl_push_id _ acc _ hcomb
  -- chain over parts
  have hfinal : ∀ (ps : List (List (List ℕ))) (acc : Array ℕ),
      part ∈ ps →
        (part.foldl (fun x y => x ||| choice y) 0) ∈
          (ps.foldl (fun acc p =>
            (p.foldl (fun accList cls =>
              accList.flatMap fun m =>
                ((classOptionsFast cls).map (m ||| ·)).toList) [0]).foldl
              (fun a m => a.push m) acc) acc).toList := by
    intro ps acc hpps
    induction ps generalizing acc with
    | nil => simp at hpps
    | cons p ps ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hpps with rfl | hpps
      · exact census_pres _ ps _ (hmem acc)
      · exact ih _ hpps
  exact hfinal _ #[] hp

/-! ## Per-class data and census_complete -/

/-- The root of a partition class (its least face, as a Fin 6). -/
def rootOf (K : ℕ) (_d : Dec K) (cls : List ℕ) : Fin 6 :=
  ⟨cls.getD 0 0 % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The class mask of a partition class (the semantic realization of
`classOptionsFast`'s members). -/
noncomputable def maskOfClass (K : ℕ) (d : Dec K) (cls : List ℕ) : ℕ :=
  classMask (relEqs cls)
    (clsIdx K d (rootOf K d cls) (clsGains K d (rootOf K d cls)))
    (stabMask (d (rootOf K d cls)))

theorem maskOfClass_eq (K : ℕ) (d : Dec K) (g : Fin 6)
    (hg : rootF K d g = g) :
    maskOfClass K d ((clsOf K d g).map Fin.val) =
      classMask (relEqs ((clsOf K d g).map Fin.val))
        (clsIdx K d g (clsGains K d g)) (stabMask (d g)) := by
  unfold maskOfClass rootOf
  have hroot : (⟨((clsOf K d g).map Fin.val).getD 0 0 % 6,
      Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = g := by
    apply Fin.ext
    show ((clsOf K d g).map Fin.val).getD 0 0 % 6 = g.val
    have h1 := clsOf_head K d g hg
    have hne : clsOf K d g ≠ [] := clsOf_ne_nil K d g
    have h2 : ((clsOf K d g).map Fin.val).getD 0 0 = g.val := by
      obtain ⟨a, ts, ha⟩ := List.exists_cons_of_ne_nil hne
      rw [ha] at h1
      have h3 : ((a :: ts).map Fin.val).getD 0 0 = ((a :: ts).getD 0 g).val := by
        simp [List.map_cons]
      rw [ha]
      rw [h3, h1]
    rw [h2, Nat.mod_eq_of_lt g.isLt]
  rw [hroot]

/-- **Census completeness** (M3b capstone): every decoration's profile
is enumerated by the census. -/
theorem census_complete (K : ℕ) (hK : 1 ≤ K) (d : Dec K) :
    profileMask (heldOf K d) ∈ censusFast.toList := by
  rw [profileMask_eq_union K d]
  -- B4: some permutation of partOf is enumerator-realizable
  obtain ⟨P', hP'perm, hP'mem⟩ := exists_perm_mem_partitionsN [0, 1, 2, 3, 4, 5]
    (by decide : ([0, 1, 2, 3, 4, 5] : List ℕ).Sorted (· ≤ ·))
    (partOf K d) (partOf_classes K d) (flatten_partOf_perm K d)
  -- the union is perm-invariant; reassociate to P'
  have hU : unionMask (((List.finRange 6).filter fun g =>
        rootF K d g == g).map fun g =>
          classMask (relEqs ((clsOf K d g).map Fin.val))
            (clsIdx K d g (clsGains K d g)) (stabMask (d g))) =
      unionMask (P'.map (maskOfClass K d)) := by
    apply unionMask_perm
    -- P' ~ partOf; map both sides by the class-mask function
    have h1 : ((List.finRange 6).filter fun g => rootF K d g == g).map
          (fun g => classMask (relEqs ((clsOf K d g).map Fin.val))
            (clsIdx K d g (clsGains K d g)) (stabMask (d g))) =
        (partOf K d).map (maskOfClass K d) := by
      unfold partOf
      rw [List.map_map]
      apply List.map_congr_left
      intro g hg
      have hgr : rootF K d g = g :=
        beq_iff_eq.mp (List.mem_filter.mp hg).2
      exact (maskOfClass_eq K d g hgr).symm
    rw [h1]
    exact (hP'perm.map _).symm
  rw [hU]
  -- per-class options
  apply mem_censusFast P' hP'mem (maskOfClass K d)
  intro cls hcls
  -- cls ∈ P' ~ partOf, so cls is a class of some root
  have hclsP : cls ∈ partOf K d := hP'perm.subset hcls
  simp only [partOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and] at hclsP
  obtain ⟨g, hgr, rfl⟩ := hclsP
  rw [maskOfClass_eq K d g hgr]
  apply mem_classOptionsFast
  · exact stabMask_mem_subMasks hK (d g)
  · have hlen : ((clsOf K d g).map Fin.val).length =
        (clsOf K d g).length := List.length_map Fin.val
    rw [hlen]
    exact clsIdx_lt K d g (clsGains K d g)

end AnyK3D
