/-
# Color M3b-B7: the face partition and the profile-equality keystone

The equal-color analogue of `AnyK3DPart.lean`. Reuses the generic
bricks (`unionMask`, `sum_le_one_of`, `mem_relEqs`, `relEqs_fst_lt`,
`efa_val`/`efb_val`/`eta_val`, `exists_perm_mem_partitionsN`) and clones
the decoration-dependent ones for `CDec T K`:

* `cpartOf` — the face partition of a color decoration as ℕ-lists in
  root order, with the properties B4 consumes: classes nonempty and
  sorted, flatten ~ [0,…,5].
* `gainAt8_cclsIdx_pos` + `encG8_stab_chain` +
  `held_iff_classMaskC_bit` — the same-class bridge: a held equation is
  exactly the class's `classMaskC` bit condition.
* **`cprofileMask_eq_union`** — the completeness keystone: a color
  decoration's 84-bit held profile is exactly the union over its face
  classes of the color census's class masks.
-/
import Mathlib
import LeanFlocq.AnyK3DColorBridge
import LeanFlocq.AnyK3DPart

set_option maxRecDepth 100000

namespace AnyK3D

open List

/-! ## cpartOf -/

/-- The face partition: classes (as ℕ lists) of distinct roots, in root
order. -/
def cpartOf (T K : ℕ) (d : CDec T K) : List (List ℕ) :=
  ((List.finRange 6).filter fun g => crootF T K d g == g).map fun g =>
    (cclsOf T K d g).map Fin.val

theorem cclsOf_sorted (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    (cclsOf T K d g).Sorted (· ≤ ·) :=
  List.Sorted.filter _ (sorted_finRange_le 6)

theorem cclsNat_sorted (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    ((cclsOf T K d g).map Fin.val).Sorted (· ≤ ·) := by
  show ((cclsOf T K d g).map Fin.val).Pairwise (· ≤ ·)
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun h => h) (cclsOf_sorted T K d g)

theorem cpartOf_classes (T K : ℕ) (d : CDec T K) :
    ∀ c ∈ cpartOf T K d, c ≠ [] ∧ c.Sorted (· ≤ ·) := by
  intro c hc
  simp only [cpartOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and] at hc
  obtain ⟨g, -, rfl⟩ := hc
  refine ⟨?_, cclsNat_sorted T K d g⟩
  intro he
  have hne := cclsOf_ne_nil T K d g
  simp only [List.map_eq_nil_iff] at he
  exact hne he

theorem mem_cpartOf_crootF (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    (cclsOf T K d (crootF T K d g)).map Fin.val ∈ cpartOf T K d := by
  simp only [cpartOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and]
  exact ⟨crootF T K d g, crootF_crootF T K d g, rfl⟩

theorem mem_flatten_cpartOf_iff (T K : ℕ) (d : CDec T K) (x : ℕ) :
    x ∈ (cpartOf T K d).flatten ↔ x ∈ (List.finRange 6).map Fin.val := by
  constructor
  · intro hx
    obtain ⟨c, hcP, hxc⟩ := List.mem_flatten.mp hx
    simp only [cpartOf, List.mem_map, List.mem_filter, List.mem_finRange,
      beq_iff_eq, true_and] at hcP
    obtain ⟨g, -, rfl⟩ := hcP
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hxc
    exact List.mem_map.mpr ⟨h, List.mem_finRange h, rfl⟩
  · intro hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
    refine List.mem_flatten.mpr
      ⟨(cclsOf T K d (crootF T K d h)).map Fin.val,
        mem_cpartOf_crootF T K d h, ?_⟩
    refine List.mem_map.mpr ⟨h, ?_, rfl⟩
    simp only [cclsOf, List.mem_filter, List.mem_finRange,
      decide_eq_true_eq]
    exact ⟨trivial, (crootF_crootF T K d h).symm⟩

/-- The class of a face is unique: if `x` lies in two partition classes,
they coincide (both roots equal `x`'s root). -/
theorem cpartOf_class_unique (T K : ℕ) (d : CDec T K) (x : ℕ)
    {c₁ c₂ : List ℕ} (hc₁ : c₁ ∈ cpartOf T K d) (hc₂ : c₂ ∈ cpartOf T K d)
    (hx₁ : x ∈ c₁) (hx₂ : x ∈ c₂) : c₁ = c₂ := by
  simp only [cpartOf, List.mem_map, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and] at hc₁ hc₂
  obtain ⟨g₁, hr₁, rfl⟩ := hc₁
  obtain ⟨g₂, hr₂, rfl⟩ := hc₂
  obtain ⟨h₁, hh₁, e₁⟩ := List.mem_map.mp hx₁
  obtain ⟨h₂, hh₂, e₂⟩ := List.mem_map.mp hx₂
  have he : h₁ = h₂ := Fin.ext (e₁.trans e₂.symm)
  have h1 := mem_cclsOf_root hh₁
  have h2 := mem_cclsOf_root hh₂
  rw [he] at h1
  have hr : crootF T K d g₁ = crootF T K d g₂ := by rw [← h1, ← h2]
  rw [← hr₁, ← hr₂, hr]

theorem nodup_flatten_cpartOf (T K : ℕ) (d : CDec T K) :
    ((cpartOf T K d).flatten).Nodup := by
  rw [List.nodup_iff_count]
  intro x
  rw [List.count_flatten]
  apply sum_le_one_of
  · intro c hc
    simp only [cpartOf, List.mem_map, List.mem_filter, List.mem_finRange,
      beq_iff_eq, true_and] at hc
    obtain ⟨g, -, rfl⟩ := hc
    have hnd : ((cclsOf T K d g).map Fin.val).Nodup :=
      ((List.nodup_finRange 6).filter _).map (fun _ _ h => Fin.ext h)
    rw [List.nodup_iff_count] at hnd
    exact hnd x
  · intro c₁ hc₁ c₂ hc₂ hne
    by_cases hx1 : x ∈ c₁
    · by_cases hx2 : x ∈ c₂
      · exact absurd (cpartOf_class_unique T K d x hc₁ hc₂ hx1 hx2) hne
      · exact Or.inr (List.count_eq_zero_of_not_mem hx2)
    · exact Or.inl (List.count_eq_zero_of_not_mem hx1)
  · apply List.Nodup.map_on _ ((List.nodup_finRange 6).filter _)
    intro g₁ hg₁ g₂ hg₂ h
    have hr₁ : crootF T K d g₁ = g₁ := beq_iff_eq.mp (List.mem_filter.mp hg₁).2
    have hr₂ : crootF T K d g₂ = g₂ := beq_iff_eq.mp (List.mem_filter.mp hg₂).2
    have hne1 := crootF_mem_cclsOf T K d g₁
    have hmem : (crootF T K d g₁).val ∈ (cclsOf T K d g₂).map Fin.val := by
      rw [← h]
      exact List.mem_map.mpr ⟨crootF T K d g₁, hne1, rfl⟩
    obtain ⟨h₂, hh₂, e₂⟩ := List.mem_map.mp hmem
    have he : h₂ = crootF T K d g₁ := Fin.ext e₂
    have h2 := mem_cclsOf_root hh₂
    rw [he, crootF_crootF] at h2
    rw [← hr₁, ← hr₂, h2]

theorem flatten_cpartOf_perm (T K : ℕ) (d : CDec T K) :
    (cpartOf T K d).flatten ~ (List.finRange 6).map Fin.val := by
  rw [List.perm_iff_count]
  intro x
  have hn1 := nodup_flatten_cpartOf T K d
  have hn2 : ((List.finRange 6).map Fin.val).Nodup :=
    (List.nodup_finRange 6).map (fun _ _ h => Fin.ext h)
  rw [List.nodup_iff_count] at hn1 hn2
  by_cases hx : x ∈ (cpartOf T K d).flatten
  · have h1 : ((cpartOf T K d).flatten).count x = 1 :=
      le_antisymm (hn1 x) (List.count_pos_iff.mpr hx)
    have hx2 : x ∈ (List.finRange 6).map Fin.val :=
      (mem_flatten_cpartOf_iff T K d x).mp hx
    have h2 : ((List.finRange 6).map Fin.val).count x = 1 :=
      le_antisymm (hn2 x) (List.count_pos_iff.mpr hx2)
    rw [h1, h2]
  · have h1 : ((cpartOf T K d).flatten).count x = 0 :=
      List.count_eq_zero_of_not_mem hx
    have hx2 : x ∉ (List.finRange 6).map Fin.val :=
      fun h => hx ((mem_flatten_cpartOf_iff T K d x).mpr h)
    have h2 : ((List.finRange 6).map Fin.val).count x = 0 :=
      List.count_eq_zero_of_not_mem hx2
    rw [h1, h2]

/-! ## B7 stage 2: class roots, positions -/

/-- The head of a root's class is the root (the census's position-0
convention, realized). -/
theorem cclsOf_head (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (hg : crootF T K d g = g) :
    (cclsOf T K d g).getD 0 g = g := by
  obtain ⟨a, t, ha⟩ := List.exists_cons_of_ne_nil (cclsOf_ne_nil T K d g)
  have hsorted := cclsOf_sorted T K d g
  rw [ha] at hsorted
  have hle : ∀ y ∈ t, a ≤ y := (List.sorted_cons.mp hsorted).1
  have hmem := crootF_mem_cclsOf T K d g
  rw [ha] at hmem
  have hga : crootF T K d a = g := by
    have h := mem_cclsOf_root (T := T) (K := K) (d := d) (g := g) (h := a)
      (by rw [ha]; exact List.mem_cons_self)
    rwa [hg] at h
  have h1 : g ≤ a := by rw [← hga]; exact crootF_le T K d a
  have h2 : a ≤ g := by
    rcases List.mem_cons.mp hmem with rfl | ht
    · rw [hg]
    · have h3 := hle (crootF T K d g) ht
      rwa [hg] at h3
  have haeq : a = g := by
    apply Fin.ext
    exact Nat.le_antisymm h2 h1
  rw [ha, haeq]
  rfl

/-- `classMaskC` stays below 2^84 when the entries' bit indices do. -/
theorem classMaskC_lt (re : Array (ℕ × ℕ × ℕ × ℕ)) (idx H : ℕ)
    (hre : ∀ e ∈ re.toList, e.1 < 84) : classMaskC re idx H < 2 ^ 84 := by
  unfold classMaskC
  rw [← Array.foldl_toList]
  have gen : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)), (∀ e ∈ l, e.1 < 84) →
      ∀ acc : ℕ, acc < 2 ^ 84 →
        (l.foldl (fun acc e =>
          if H.testBit (gmul8 (ginv8 (gainAt8 idx e.2.1))
            (gmul8 e.2.2.2 (gainAt8 idx e.2.2.1)))
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

/-- The gain code at a member position of the class list (the position
form of B5's digit lemma). -/
theorem gainAt8_cclsIdx_pos (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (h : Fin 6) (hg : crootF T K d g = g) (ja : ℕ)
    (hja : ((cclsOf T K d g).map Fin.val).idxOf? h.val = some ja) :
    gainAt8 (cclsIdx T K d g (cclsGains T K d g)) ja =
      (cclsGains T K d g h).val := by
  have hb : ja < (cclsOf T K d g).length := by
    obtain ⟨hb, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hja
    rwa [List.length_map] at hb
  have hget : (cclsOf T K d g)[ja]'hb = h := by
    obtain ⟨hb2, h2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hja
    have hv : ((cclsOf T K d g).map Fin.val)[ja]'hb2 = h.val :=
      beq_iff_eq.mp h2
    rw [List.getElem_map] at hv
    exact Fin.ext hv
  cases ja with
  | zero =>
    rw [gainAt8_cclsIdx_zero]
    have hge : h = g := by
      have h0 := cclsOf_head T K d g hg
      have he : (cclsOf T K d g).getD 0 g = h := by
        rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_pos hb]
        exact hget
      rw [h0] at he
      exact he.symm
    have hroot : cclsGains T K d g g = 0 := by
      have h1 := cclsGains_root T K d g
      rwa [hg] at h1
    rw [hge, hroot]
    rfl
  | succ j' =>
    have hb' : j' < (cclsOf T K d g).tail.length := by
      rw [List.length_tail]; omega
    rw [gainAt8_cclsIdx T K d g (cclsGains T K d g) (j' + 1) (by omega)]
    have hgd : ((cclsOf T K d g).tail.map fun h =>
            encG8 (cclsGains T K d g h)).getD
        j' 0 = encG8 (cclsGains T K d g h) := by
      rw [List.getD_eq_getElem?_getD, List.getD_getElem?,
        dif_pos (by rw [List.length_map]; exact hb'), List.getElem_map,
        List.getElem_tail, hget]
    exact hgd

/-- The encoded stabilizer-chain identity (color B2 assembled). -/
theorem encG8_stab_chain (wg wh : Fin 8) (t : Fin 8) :
    encG8 (cmul (cinv wg) (cmul t wh)) =
      gmul8 (ginv8 wg.val) (gmul8 t.val wh.val) := by
  have e : ∀ w : Fin 8, encG8 w = w.val := fun _ => rfl
  rw [← e wg, ← e wh, ← e t, ginv8_encG8, gmul8_encG8, gmul8_encG8]

/-- The same-class bridge: a held equation is exactly the class's
classMaskC bit condition. -/
theorem held_iff_classMaskC_bit (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (hg : crootF T K d g = g) (i : Fin 84)
    (ha : crootF T K d (efa i) = g) (hb : crootF T K d (efb i) = g)
    (ja jb : ℕ)
    (hja : ((cclsOf T K d g).map Fin.val).idxOf? (efa i).val = some ja)
    (hjb : ((cclsOf T K d g).map Fin.val).idxOf? (efb i).val = some jb) :
    ceqHolds T K d (efa i) (efb i) (eta i) = true ↔
      (stabMaskC (d g)).testBit
        (gmul8 (ginv8 (gainAt8 (cclsIdx T K d g (cclsGains T K d g)) ja))
          (gmul8 (eta i).val
            (gainAt8 (cclsIdx T K d g (cclsGains T K d g)) jb))) = true := by
  rw [gainAt8_cclsIdx_pos T K d g (efa i) hg ja hja,
    gainAt8_cclsIdx_pos T K d g (efb i) hg jb hjb,
    ← encG8_stab_chain]
  have hga : d (efa i) = cact (cclsGains T K d g (efa i)) (d g) := by
    have hmem : efa i ∈ cclsOf T K d g := by
      simp only [cclsOf, List.mem_filter, List.mem_finRange,
        decide_eq_true_eq]
      exact ⟨trivial, by rw [ha, hg]⟩
    have h := cclsGains_spec T K d g (efa i) hmem
    rwa [hg] at h
  have hgb : d (efb i) = cact (cclsGains T K d g (efb i)) (d g) := by
    have hmem : efb i ∈ cclsOf T K d g := by
      simp only [cclsOf, List.mem_filter, List.mem_finRange,
        decide_eq_true_eq]
      exact ⟨trivial, by rw [hb, hg]⟩
    have h := cclsGains_spec T K d g (efb i) hmem
    rwa [hg] at h
  rw [ceqHolds_iff_stab T K d (efa i) (efb i) (eta i) (d g)
    (cclsGains T K d g (efa i)) (cclsGains T K d g (efb i)) hga hgb,
    testBit_stabMaskC (d g) _ (encG8_lt _), decG8_encG8, decide_eq_true_eq]

/-! ## B7 stage 3: the keystone -/

theorem cclsOf_nodup (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    (cclsOf T K d g).Nodup :=
  (List.nodup_finRange 6).filter _

/-- Position of a face in its class: the idxOf? form the census's
`relEqs` needs. -/
theorem idxOf?_cclsOf (T K : ℕ) (d : CDec T K) (g h : Fin 6)
    (hh : h ∈ cclsOf T K d g) :
    ∃ ja, ((cclsOf T K d g).map Fin.val).idxOf? h.val = some ja := by
  obtain ⟨ja, hja, hget⟩ := List.mem_iff_getElem.mp hh
  have hb : ja < ((cclsOf T K d g).map Fin.val).length := by
    rw [List.length_map]; exact hja
  refine ⟨ja, List.findIdx?_eq_some_iff_getElem.mpr ⟨hb, ?_, ?_⟩⟩
  · have hv : ((cclsOf T K d g).map Fin.val)[ja]'hb = h.val := by
      rw [List.getElem_map, hget]
    exact beq_iff_eq.mpr hv
  · intro j hji hc
    have hbj : j < (cclsOf T K d g).length := Nat.lt_trans hji hja
    have hjb : j < ((cclsOf T K d g).map Fin.val).length :=
      Nat.lt_trans hji hb
    have hv : (cclsOf T K d g)[j]'hbj = h := by
      have hv' : ((cclsOf T K d g).map Fin.val)[j]'hjb = h.val :=
        beq_iff_eq.mp hc
      rw [List.getElem_map] at hv'
      exact Fin.ext hv'
    have e1 : (cclsOf T K d g)[j]? = some h :=
      List.getElem?_eq_some_iff.mpr ⟨hbj, hv⟩
    have e2 : (cclsOf T K d g)[ja]? = some h :=
      List.getElem?_eq_some_iff.mpr ⟨hja, hget⟩
    have hij : j = ja :=
      List.getElem?_inj hbj (cclsOf_nodup T K d g) (e1.trans e2.symm)
    exact absurd hij (Nat.ne_of_lt hji)

/-- Membership from a position (the converse direction). -/
theorem mem_cclsOf_of_idxOf? (T K : ℕ) (d : CDec T K) (g h : Fin 6)
    (p : ℕ)
    (hp : ((cclsOf T K d g).map Fin.val).idxOf? h.val = some p) :
    h ∈ cclsOf T K d g := by
  obtain ⟨hb2, h2, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hp
  have hb3 : p < (cclsOf T K d g).length := by rwa [List.length_map] at hb2
  have hv : (cclsOf T K d g)[p]'hb3 = h := by
    have hv' : ((cclsOf T K d g).map Fin.val)[p]'hb2 = h.val :=
      beq_iff_eq.mp h2
    rw [List.getElem_map] at hv'
    exact Fin.ext hv'
  rw [← hv]
  exact List.getElem_mem hb3

/-- **The profile equality.** A color decoration's 84-bit held profile
is exactly the union over its face classes of the color census's class
masks — the completeness keystone. -/
theorem cprofileMask_eq_union (T K : ℕ) (d : CDec T K) :
    profileMask (cheldOf T K d) =
      unionMask (((List.finRange 6).filter fun g =>
        crootF T K d g == g).map
        fun g =>
          classMaskC (relEqs ((cclsOf T K d g).map Fin.val))
            (cclsIdx T K d g (cclsGains T K d g)) (stabMaskC (d g))) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 84
  · rw [testBit_profileMask (cheldOf T K d) j hj, testBit_unionMask,
      Bool.eq_iff_iff]
    constructor
    · -- held → some class's mask carries the bit
      intro hheld
      have hrel : crelated T K d (efa ⟨j, hj⟩) (efb ⟨j, hj⟩) :=
        ⟨eta ⟨j, hj⟩, (ceqHolds_iff_act T K d _ _ _).mp hheld⟩
      have hroots : crootF T K d (efa ⟨j, hj⟩) = crootF T K d (efb ⟨j, hj⟩) :=
        crootF_eq_iff_crelated.mpr hrel
      set g := crootF T K d (efa ⟨j, hj⟩) with hg_def
      have hg : crootF T K d g = g := crootF_crootF T K d _
      have hroots2 : crootF T K d (efb ⟨j, hj⟩) = g := hroots.symm
      have hmemA : efa ⟨j, hj⟩ ∈ cclsOf T K d g := by
        simp only [cclsOf, List.mem_filter, List.mem_finRange,
          decide_eq_true_eq]
        refine ⟨trivial, ?_⟩
        rw [hg_def]
        exact (crootF_crootF T K d _).symm
      have hmemB : efb ⟨j, hj⟩ ∈ cclsOf T K d g := by
        simp only [cclsOf, List.mem_filter, List.mem_finRange,
          decide_eq_true_eq]
        refine ⟨trivial, ?_⟩
        rw [hroots2, hg]
      obtain ⟨ja, hja⟩ := idxOf?_cclsOf T K d g (efa ⟨j, hj⟩) hmemA
      obtain ⟨jb, hjb⟩ := idxOf?_cclsOf T K d g (efb ⟨j, hj⟩) hmemB
      rw [List.any_eq_true]
      refine ⟨_, List.mem_map.mpr
          ⟨g, List.mem_filter.mpr ⟨List.mem_finRange _, beq_iff_eq.mpr hg⟩,
           rfl⟩, ?_⟩
      rw [testBit_classMaskC]
      rw [List.any_eq_true]
      have hbit2 := (held_iff_classMaskC_bit T K d g hg ⟨j, hj⟩ hg_def.symm
          hroots2 ja jb hja hjb).mp hheld
      rw [eta_val j hj] at hbit2
      exact ⟨(j, ja, jb, eqTau.getD j 0),
        Array.mem_def.mp ((mem_relEqs ((cclsOf T K d g).map Fin.val) j ja jb
            (eqTau.getD j 0)).mpr
          ⟨hj, efa_val j hj ▸ hja, efb_val j hj ▸ hjb, rfl⟩),
        by rw [Bool.and_eq_true]; exact ⟨hbit2, by simp⟩⟩
    · -- some class's mask carries the bit → held
      intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨m, hm, hbit⟩ := hany
      obtain ⟨g, hgP, rfl⟩ := List.mem_map.mp hm
      have hg : crootF T K d g = g := beq_iff_eq.mp (List.mem_filter.mp hgP).2
      rw [testBit_classMaskC, List.any_eq_true] at hbit
      obtain ⟨⟨i, ja, jb, t⟩, hentry, hcond⟩ := hbit
      rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hcond, hbitj⟩ := hcond
      obtain ⟨hi, hja, hjb, ht⟩ :=
        (mem_relEqs ((cclsOf T K d g).map Fin.val) i ja jb t).mp
          (Array.mem_def.mpr hentry)
      subst hbitj
      subst ht
      have hja' : ((cclsOf T K d g).map Fin.val).idxOf? (efa ⟨i, hi⟩).val =
          some ja := by rw [← efa_val i hi] at hja; exact hja
      have hjb' : ((cclsOf T K d g).map Fin.val).idxOf? (efb ⟨i, hi⟩).val =
          some jb := by rw [← efb_val i hi] at hjb; exact hjb
      have hra : crootF T K d (efa ⟨i, hi⟩) = g := by
        have h := mem_cclsOf_root (mem_cclsOf_of_idxOf? T K d g _ _ hja')
        rwa [hg] at h
      have hrb : crootF T K d (efb ⟨i, hi⟩) = g := by
        have h := mem_cclsOf_root (mem_cclsOf_of_idxOf? T K d g _ _ hjb')
        rwa [hg] at h
      dsimp only at hcond
      rw [← eta_val i hi] at hcond
      exact (held_iff_classMaskC_bit T K d g hg ⟨i, hi⟩ hra hrb ja jb
        hja' hjb').mpr hcond
  · rw [testBit_profileMask_ge (cheldOf T K d) j (by omega)]
    rw [testBit_unionMask, eq_comm, List.any_eq_false]
    intro m hm
    obtain ⟨g, hgP, rfl⟩ := List.mem_map.mp hm
    have h84 : 84 ≤ j := by omega
    have hb : (classMaskC (relEqs ((cclsOf T K d g).map Fin.val))
        (cclsIdx T K d g (cclsGains T K d g)) (stabMaskC (d g))).testBit j
          = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le
          (classMaskC_lt _ _ _ (relEqs_fst_lt _))
          (Nat.pow_le_pow_right (by norm_num) h84))
    simp [hb]

end AnyK3D
