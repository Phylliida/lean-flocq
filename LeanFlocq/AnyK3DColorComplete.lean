/-
# Color M3b-B8: the membership chain → color_census_complete

The equal-color analogue of `AnyK3DComplete.lean`. The generic
fold/dedup membership lemmas are reused; the census-specific ones are
cloned for `classOptionsFastC`/`censusFastC`:

* `mem_classOptionsFastC` — a realized class mask (color B6's
  stabilizer mask + B5's tuple index) is enumerated by
  `classOptionsFastC`;
* `mem_censusFastC` — the union of per-class masks over an
  enumerator-realizable partition (B4) is in `censusFastC`;
* **`color_census_complete`** — the assembly via B7's profile equality.

Unlike bump/dent, NO `1 ≤ K` hypothesis is needed: the color census
enumerates ALL subgroups of the gain group, so the stabilizer mask of
any face pattern (any K, any palette T) is enumerated by pure algebra.
-/
import Mathlib
import LeanFlocq.AnyK3DColorPart
import LeanFlocq.AnyK3DComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AnyK3D

open List

/-! ## mem_classOptionsFastC -/

/-- The realized class mask is enumerated: color B6's stabilizer mask is
a census subgroup and B5's tuple index fits the range, so
`classOptionsFastC members` contains the class's mask. -/
theorem mem_classOptionsFastC (members : List ℕ) (idx H : ℕ)
    (hH : H ∈ subMasksC.toList) (hidx : idx < 8 ^ (members.length - 1)) :
    classMaskC (relEqs members) idx H ∈
      (classOptionsFastC members).toList := by
  unfold classOptionsFastC
  apply mem_dedupSorted
  rw [← Array.foldl_toList]
  -- the inner fold introduces classMaskC for idx at H's position
  have hinner : ∀ acc : Array ℕ, classMaskC (relEqs members) idx H ∈
      ((List.range (8 ^ (members.length - 1))).foldl
        (fun acc i => acc.push (classMaskC (relEqs members) i H))
        acc).toList := by
    intro acc
    exact mem_foldl_push_gen _ _ acc idx (List.mem_range.mpr hidx)
  -- preservation: membership in the accumulator survives later folds
  have hpres : ∀ (Hs : List ℕ) (acc : Array ℕ),
      classMaskC (relEqs members) idx H ∈ acc.toList →
      classMaskC (relEqs members) idx H ∈
        (Hs.foldl
          (fun acc H' => (List.range (8 ^ (members.length - 1))).foldl
            (fun acc i => acc.push (classMaskC (relEqs members) i H')) acc)
          acc).toList := by
    intro Hs acc h
    induction Hs generalizing acc with
    | nil => exact h
    | cons H' Hs' ih =>
      simp only [List.foldl_cons]
      apply ih
      clear ih
      induction (List.range (8 ^ (members.length - 1)) : List ℕ)
        generalizing acc with
      | nil => exact h
      | cons i is ih2 =>
        simp only [List.foldl_cons]
        apply ih2
        rw [Array.toList_push]
        exact List.mem_append_left _ h
  -- chain: H ∈ subMasksC, introduced at H, preserved after
  have houter : ∀ (Hs : List ℕ) (acc : Array ℕ), H ∈ Hs →
      classMaskC (relEqs members) idx H ∈
        (Hs.foldl
          (fun acc H' => (List.range (8 ^ (members.length - 1))).foldl
            (fun acc i => acc.push (classMaskC (relEqs members) i H')) acc)
          acc).toList := by
    intro Hs acc hHs
    induction Hs generalizing acc with
    | nil => simp at hHs
    | cons H' Hs' ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hHs with rfl | hHs'
      · exact hpres Hs' _ (hinner acc)
      · exact ih _ hHs'
  exact houter subMasksC.toList #[] hH

/-! ## mem_censusFastC -/

/-- Every union of per-class options (left fold) lies in the partition's
combination list. -/
theorem mem_combosC (part : List (List ℕ)) (choice : List ℕ → ℕ) :
    ∀ (accList : List ℕ) (init : ℕ),
      (∀ cls ∈ part, choice cls ∈ (classOptionsFastC cls).toList) →
      init ∈ accList →
      (part.foldl (fun m cls => m ||| choice cls) init) ∈
        (part.foldl (fun (accList : List ℕ) cls =>
          accList.flatMap fun m =>
            ((classOptionsFastC cls).map (m ||| ·)).toList) accList) := by
  induction part with
  | nil => intro accList init _ hin; exact hin
  | cons cls rest ih =>
    intro accList init h hin
    simp only [List.foldl_cons]
    refine ih _ _ (fun cls' hcls' => h cls' (List.mem_cons_of_mem _ hcls'))
      ?_
    rw [List.mem_flatMap]
    refine ⟨init, hin, ?_⟩
    have hopt := h cls List.mem_cons_self
    have hthis : (init ||| choice cls) ∈
        ((classOptionsFastC cls).toList.map (init ||| ·)) :=
      List.mem_map.mpr ⟨choice cls, hopt, rfl⟩
    rwa [Array.toList_map]

/-- The census union membership: a partition's option-union is in
`censusFastC`. -/
theorem census_presC (u : ℕ) (ps : List (List (List ℕ))) :
    ∀ acc : Array ℕ, u ∈ acc.toList →
      u ∈ (ps.foldl (fun acc p =>
        (p.foldl (fun accList cls =>
          accList.flatMap fun m =>
            ((classOptionsFastC cls).map (m ||| ·)).toList) [0]).foldl
          (fun a m => a.push m) acc) acc).toList := by
  induction ps with
  | nil => intro acc h; exact h
  | cons q qs ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (mem_foldl_push_id_subset _ _ _ h)

theorem mem_censusFastC (part : List (List ℕ))
    (hp : part ∈ partitionsN [0, 1, 2, 3, 4, 5])
    (choice : List ℕ → ℕ)
    (h : ∀ cls ∈ part, choice cls ∈ (classOptionsFastC cls).toList) :
    ((part.map choice).foldl (· ||| ·) 0) ∈ censusFastC.toList := by
  rw [List.foldl_map]
  show (part.foldl (fun x y => x ||| choice y) 0) ∈ censusFastC.toList
  unfold censusFastC
  apply mem_dedupSorted
  -- the union is in part's combos
  have hcomb : (part.foldl (fun x y => x ||| choice y) 0) ∈
      (part.foldl (fun accList cls =>
        accList.flatMap fun m =>
          ((classOptionsFastC cls).map (m ||| ·)).toList) [0]) := by
    apply mem_combosC part choice [0] 0 h
    exact List.mem_singleton_self _
  -- combos gets pushed at part's position in parts; preserved after
  have hmem : ∀ acc : Array ℕ,
      (part.foldl (fun x y => x ||| choice y) 0) ∈
        ((part.foldl (fun accList cls =>
          accList.flatMap fun m =>
            ((classOptionsFastC cls).map (m ||| ·)).toList) [0]).foldl
          (fun a m => a.push m) acc).toList :=
    fun acc => mem_foldl_push_id _ acc _ hcomb
  -- chain over parts
  have hfinal : ∀ (ps : List (List (List ℕ))) (acc : Array ℕ),
      part ∈ ps →
        (part.foldl (fun x y => x ||| choice y) 0) ∈
          (ps.foldl (fun acc p =>
            (p.foldl (fun accList cls =>
              accList.flatMap fun m =>
                ((classOptionsFastC cls).map (m ||| ·)).toList) [0]).foldl
              (fun a m => a.push m) acc) acc).toList := by
    intro ps acc hpps
    induction ps generalizing acc with
    | nil => simp at hpps
    | cons p ps ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hpps with rfl | hpps
      · exact census_presC _ ps _ (hmem acc)
      · exact ih _ hpps
  exact hfinal _ #[] hp

/-! ## Per-class data and color_census_complete -/

/-- The root of a partition class (its least face, as a Fin 6). -/
def crootOf (T K : ℕ) (_d : CDec T K) (cls : List ℕ) : Fin 6 :=
  ⟨cls.getD 0 0 % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The class mask of a partition class (the semantic realization of
`classOptionsFastC`'s members). -/
noncomputable def cmaskOfClass (T K : ℕ) (d : CDec T K) (cls : List ℕ) :
    ℕ :=
  classMaskC (relEqs cls)
    (cclsIdx T K d (crootOf T K d cls) (cclsGains T K d (crootOf T K d cls)))
    (stabMaskC (d (crootOf T K d cls)))

theorem cmaskOfClass_eq (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (hg : crootF T K d g = g) :
    cmaskOfClass T K d ((cclsOf T K d g).map Fin.val) =
      classMaskC (relEqs ((cclsOf T K d g).map Fin.val))
        (cclsIdx T K d g (cclsGains T K d g)) (stabMaskC (d g)) := by
  unfold cmaskOfClass crootOf
  have hroot : (⟨((cclsOf T K d g).map Fin.val).getD 0 0 % 6,
      Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = g := by
    apply Fin.ext
    show ((cclsOf T K d g).map Fin.val).getD 0 0 % 6 = g.val
    have h1 := cclsOf_head T K d g hg
    have hne := cclsOf_ne_nil T K d g
    have h2 : ((cclsOf T K d g).map Fin.val).getD 0 0 = g.val := by
      obtain ⟨a, ts, ha⟩ := List.exists_cons_of_ne_nil hne
      rw [ha] at h1
      have h3 : ((a :: ts).map Fin.val).getD 0 0 = ((a :: ts).getD 0 g).val := by
        simp [List.map_cons]
      rw [ha]
      rw [h3, h1]
    rw [h2, Nat.mod_eq_of_lt g.isLt]
  rw [hroot]

/-- **Color census completeness** (the M3b capstone of the color
track): every equal-color decoration's profile is enumerated by the
color census — any grid K, any palette T. -/
theorem color_census_complete (T K : ℕ) (d : CDec T K) :
    profileMask (cheldOf T K d) ∈ censusFastC.toList := by
  rw [cprofileMask_eq_union T K d]
  -- B4: some permutation of cpartOf is enumerator-realizable
  obtain ⟨P', hP'perm, hP'mem⟩ := exists_perm_mem_partitionsN [0, 1, 2, 3, 4, 5]
    (by decide : ([0, 1, 2, 3, 4, 5] : List ℕ).Sorted (· ≤ ·))
    (cpartOf T K d) (cpartOf_classes T K d) (flatten_cpartOf_perm T K d)
  -- the union is perm-invariant; reassociate to P'
  have hU : unionMask (((List.finRange 6).filter fun g =>
        crootF T K d g == g).map fun g =>
          classMaskC (relEqs ((cclsOf T K d g).map Fin.val))
            (cclsIdx T K d g (cclsGains T K d g)) (stabMaskC (d g))) =
      unionMask (P'.map (cmaskOfClass T K d)) := by
    apply unionMask_perm
    -- P' ~ cpartOf; map both sides by the class-mask function
    have h1 : ((List.finRange 6).filter fun g => crootF T K d g == g).map
          (fun g => classMaskC (relEqs ((cclsOf T K d g).map Fin.val))
            (cclsIdx T K d g (cclsGains T K d g)) (stabMaskC (d g))) =
        (cpartOf T K d).map (cmaskOfClass T K d) := by
      unfold cpartOf
      rw [List.map_map]
      apply List.map_congr_left
      intro g hg
      have hgr : crootF T K d g = g :=
        beq_iff_eq.mp (List.mem_filter.mp hg).2
      exact (cmaskOfClass_eq T K d g hgr).symm
    rw [h1]
    exact (hP'perm.map _).symm
  rw [hU]
  -- per-class options
  apply mem_censusFastC P' hP'mem (cmaskOfClass T K d)
  intro cls hcls
  -- cls ∈ P' ~ cpartOf, so cls is a class of some root
  have hclsP : cls ∈ cpartOf T K d := hP'perm.subset hcls
  simp only [cpartOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and] at hclsP
  obtain ⟨g, hgr, rfl⟩ := hclsP
  rw [cmaskOfClass_eq T K d g hgr]
  apply mem_classOptionsFastC
  · exact stabMaskC_mem_subMasksC (d g)
  · have hlen : ((cclsOf T K d g).map Fin.val).length =
        (cclsOf T K d g).length := List.length_map Fin.val
    rw [hlen]
    exact cclsIdx_lt T K d g (cclsGains T K d g)

end AnyK3D
