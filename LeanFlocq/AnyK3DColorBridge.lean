/-
# Color M3b: the encoding bridge + class structure (B2/B3/B5/B6 clones)

The equal-color analogue of `AnyK3DBridge.lean`. Reuses the generic
bricks (`testBit_foldl_or_gen`, `profileMask`, `relEqs`,
`exists_perm_mem_partitionsN`) and clones the decoration-dependent ones
for `CDec T K` with the 8-element gain group:

  * B2 — the encoding bridge: the census's table arithmetic (`gmul8`,
    `ginv8` over codes 0..7) agrees with the color M2 algebra (`cmul`,
    `cinv`) under `encG8`. All finite, kernel-`decide`d.
  * B3 — the face equivalence (`crelated`), orbit roots (`crootF`), and
    the orbit invariant `crootF_eq_iff_crelated`.
  * B6 — the stabilizer mask of a root face: a subgroup mask, hence a
    member of the color census's `subMasksC`. NO feasibility side
    condition (every subgroup of the color gain group is realizable) and
    NO `1 ≤ K` hypothesis (the subgroup property is pure algebra).
  * B5 — class lists (`cclsOf`), chosen gains (`exists_ccls_gains`), and
    the tuple counter (`cclsIdx`) with its base-8 digit lemmas.
-/
import Mathlib
import LeanFlocq.AnyK3DBridge
import LeanFlocq.AnyK3DColorCensus

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## B2: the encoding bridge (finite, kernel-checked) -/

theorem encG8_lt (w : Fin 8) : encG8 w < 8 := w.isLt

theorem decG8_encG8 : ∀ w : Fin 8, decG8 (encG8 w) = w := by decide

theorem encG8_decG8 : ∀ n : Fin 8, encG8 (decG8 n.val) = n.val := by decide

theorem gmul8_encG8 : ∀ a b : Fin 8,
    gmul8 (encG8 a) (encG8 b) = encG8 (cmul a b) := by decide

theorem ginv8_encG8 : ∀ a : Fin 8, ginv8 (encG8 a) = encG8 (cinv a) := by
  decide

/-- `classMaskC` bits, via the generic fold. Bit `j` is set iff some
relevant-equation entry has bit index `j` and its held-condition
passes. -/
theorem testBit_classMaskC (re : Array (ℕ × ℕ × ℕ × ℕ)) (idx H : ℕ)
    (j : ℕ) :
    (classMaskC re idx H).testBit j
      = re.toList.any fun e =>
          H.testBit (gmul8 (ginv8 (gainAt8 idx e.2.1))
            (gmul8 e.2.2.2 (gainAt8 idx e.2.2.1))) &&
          decide (e.1 = j) := by
  unfold classMaskC
  rw [← Array.foldl_toList]
  have := testBit_foldl_or_gen (fun e : ℕ × ℕ × ℕ × ℕ => e.1)
    (fun e => H.testBit (gmul8 (ginv8 (gainAt8 idx e.2.1))
      (gmul8 e.2.2.2 (gainAt8 idx e.2.2.1))))
    re.toList 0 j
  simp only [Nat.zero_testBit, Bool.false_or] at this
  rw [← this]

/-! ## B3: the face equivalence and roots -/

/-- Two faces related by some color gain. -/
def crelated (T K : ℕ) (d : CDec T K) (g h : Fin 6) : Prop :=
  ∃ w : Fin 8, d g = cact w (d h)

instance (T K : ℕ) (d : CDec T K) (g h : Fin 6) :
    Decidable (crelated T K d g h) := by
  unfold crelated; infer_instance

theorem crelated_refl (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    crelated T K d g g :=
  ⟨0, (cact_one _).symm⟩

theorem crelated_symm {T K : ℕ} {d : CDec T K} {g h : Fin 6}
    (hr : crelated T K d g h) : crelated T K d h g := by
  obtain ⟨w, hw⟩ := hr
  exact ⟨cinv w, by rw [hw, cact_inv_cact]⟩

theorem crelated_trans {T K : ℕ} {d : CDec T K} {g h k : Fin 6}
    (h1 : crelated T K d g h) (h2 : crelated T K d h k) :
    crelated T K d g k := by
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  exact ⟨cmul w1 w2, by rw [hw1, hw2, cact_cact]⟩

/-- The gain-orbit of `g`, as a finset. -/
def crootClass (T K : ℕ) (d : CDec T K) (g : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter (fun h => crelated T K d h g)

theorem crootClass_nonempty (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    (crootClass T K d g).Nonempty :=
  ⟨g, by simp [crootClass, crelated_refl]⟩

/-- The root of `g`'s orbit: its least member. -/
def crootF (T K : ℕ) (d : CDec T K) (g : Fin 6) : Fin 6 :=
  (crootClass T K d g).min' (crootClass_nonempty T K d g)

theorem mem_crootClass {T K : ℕ} {d : CDec T K} {g h : Fin 6} :
    h ∈ crootClass T K d g ↔ crelated T K d h g := by
  simp [crootClass]

theorem crelated_crootF (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    crelated T K d (crootF T K d g) g :=
  mem_crootClass.mp ((crootClass T K d g).min'_mem _)

theorem crootF_le (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    crootF T K d g ≤ g :=
  (crootClass T K d g).min'_le g (mem_crootClass.mpr (crelated_refl T K d g))

theorem crootClass_eq_of_crelated {T K : ℕ} {d : CDec T K} {g h : Fin 6}
    (hr : crelated T K d g h) : crootClass T K d g = crootClass T K d h := by
  ext x
  simp only [mem_crootClass]
  exact ⟨fun hx => crelated_trans hx hr,
         fun hx => crelated_trans hx (crelated_symm hr)⟩

theorem crootF_eq_of_crelated {T K : ℕ} {d : CDec T K} {g h : Fin 6}
    (hr : crelated T K d g h) : crootF T K d g = crootF T K d h := by
  unfold crootF
  congr 1
  exact crootClass_eq_of_crelated hr

theorem crootF_crootF (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    crootF T K d (crootF T K d g) = crootF T K d g :=
  crootF_eq_of_crelated (crelated_crootF T K d g)

/-- Roots agree exactly on related faces — the orbit invariant. -/
theorem crootF_eq_iff_crelated {T K : ℕ} {d : CDec T K} {g h : Fin 6} :
    crootF T K d g = crootF T K d h ↔ crelated T K d g h := by
  constructor
  · intro he
    exact crelated_trans (crelated_symm (crelated_crootF T K d g))
      (he ▸ crelated_crootF T K d h)
  · exact crootF_eq_of_crelated

/-- Every face is a gain-image of its root: the B5 input. -/
theorem exists_cgain_from_root (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    ∃ w : Fin 8, d g = cact w (d (crootF T K d g)) :=
  crelated_symm (crelated_crootF T K d g)

/-! ## B6: the stabilizer mask

The encoded stabilizer of a root's face-function is a subgroup mask —
hence a member of the color census's `subMasksC` enumeration (all 10
subgroups are enumerated; no feasibility filter, no `1 ≤ K`). -/

/-- The encoded stabilizer: bit `n` set iff the gain coded `n` fixes
`F`. -/
def stabMaskC {T K : ℕ} (F : Fin K → Fin K → Fin T) : ℕ :=
  (List.range 8).foldl
    (fun acc n => if decide (cact (decG8 n) F = F) then acc ||| (1 <<< n)
      else acc) 0

theorem testBit_stabMaskC {T K : ℕ} (F : Fin K → Fin K → Fin T) (n : ℕ)
    (hn : n < 8) :
    (stabMaskC F).testBit n = decide (cact (decG8 n) F = F) := by
  unfold stabMaskC
  rw [testBit_foldl_or_gen (fun m => m)
    (fun m => decide (cact (decG8 m) F = F))]
  rw [Bool.eq_iff_iff]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, -, hm, rfl⟩
    simpa using hm
  · intro h
    exact ⟨n, hn, by simpa using h, rfl⟩

/-- Or-accumulation over sub-8 bit positions stays below 256. -/
theorem foldl_or_lt8 (c : ℕ → Bool) :
    ∀ (l : List ℕ), (∀ n ∈ l, n < 8) → ∀ acc : ℕ, acc < 256 →
      l.foldl (fun a n => if c n then a ||| (1 <<< n) else a) acc < 256
  | [], _, acc, hacc => hacc
  | n :: ns, hl, acc, hacc => by
    simp only [List.foldl_cons]
    apply foldl_or_lt8 c ns (fun m hm => hl m (List.mem_cons_of_mem _ hm))
    by_cases hc : c n
    · simp only [hc, if_pos]
      have h1 : (1 <<< n) < 256 := by
        rw [Nat.one_shiftLeft]
        calc 2 ^ n ≤ 2 ^ 7 :=
              Nat.pow_le_pow_right (by norm_num)
                (by have := hl n (List.mem_cons_self ..); omega)
          _ < 256 := by norm_num
      have : acc ||| (1 <<< n) < 2 ^ 8 :=
        Nat.or_lt_two_pow (by omega) (by omega)
      omega
    · simpa [hc]

theorem stabMaskC_lt {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    stabMaskC F < 256 := by
  unfold stabMaskC
  exact foldl_or_lt8 _ _ (by simp) 0 (by norm_num)

theorem testBit_stabMaskC_ge {T K : ℕ} (F : Fin K → Fin K → Fin T) (n : ℕ)
    (hn : 8 ≤ n) : (stabMaskC F).testBit n = false := by
  have h1 : stabMaskC F < 2 ^ n :=
    lt_of_lt_of_le (stabMaskC_lt F)
      (le_trans (by norm_num : (256 : ℕ) ≤ 2 ^ 8)
        (Nat.pow_le_pow_right (by norm_num) hn))
  exact Nat.testBit_lt_two_pow h1

/-- The stabilizer mask passes the census's subgroup check. -/
theorem stabMaskC_isSubgroup {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    isSubgroupM8 (stabMaskC F) = true := by
  have hbit : ∀ n < 8, (stabMaskC F).testBit n
      = decide (cact (decG8 n) F = F) := fun n hn => testBit_stabMaskC F n hn
  unfold isSubgroupM8 maskHasAll8
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hbit 0 (by norm_num)]
    simp [show (decG8 0 : Fin 8) = 0 from rfl, cact_one]
  · intro a ha
    by_cases hA : (stabMaskC F).testBit a
    · right
      intro b hb
      by_cases hB : (stabMaskC F).testBit b
      · right
        rw [hbit a ha] at hA
        rw [hbit b hb] at hB
        simp only [decide_eq_true_eq] at hA hB
        have hab : gmul8 a b = encG8 (cmul (decG8 a) (decG8 b)) := by
          have hae : encG8 (decG8 a) = a := encG8_decG8 ⟨a, ha⟩
          have hbe : encG8 (decG8 b) = b := encG8_decG8 ⟨b, hb⟩
          conv_lhs => rw [← hae, ← hbe]
          exact gmul8_encG8 _ _
        have hlt : gmul8 a b < 8 := hab ▸ encG8_lt _
        rw [hbit _ hlt, hab]
        simp only [decide_eq_true_eq, decG8_encG8]
        rw [← cact_cact, hB, hA]
      · left; simp [hB]
    · left; simp [hA]
  · intro a ha
    by_cases hA : (stabMaskC F).testBit a
    · right
      rw [hbit a ha] at hA
      simp only [decide_eq_true_eq] at hA
      have hai : ginv8 a = encG8 (cinv (decG8 a)) := by
        have hae : encG8 (decG8 a) = a := encG8_decG8 ⟨a, ha⟩
        conv_lhs => rw [← hae]
        exact ginv8_encG8 _
      have hlt : ginv8 a < 8 := hai ▸ encG8_lt _
      rw [hbit _ hlt, hai]
      simp only [decide_eq_true_eq, decG8_encG8]
      rw [← hA, cact_inv_cact, hA]
    · left; simp [hA]

/-- The stabilizer mask is enumerated by the color census. -/
theorem stabMaskC_mem_subMasksC {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    stabMaskC F ∈ subMasksC.toList := by
  unfold subMasksC
  simp only [List.toList_toArray, List.mem_filter]
  constructor
  · exact List.mem_range.mpr (stabMaskC_lt F)
  · simp [stabMaskC_isSubgroup F]

/-! ## B5: gains and the tuple index (base 8) -/

/-- Horner packing of base-8 digits:
`idxFor8 [c₁, c₂, …] = c₁ + 8·(c₂ + 8·(…))`. -/
def idxFor8 : List ℕ → ℕ := List.foldr (fun c acc => c + 8 * acc) 0

theorem idxFor8_cons (c : ℕ) (l : List ℕ) :
    idxFor8 (c :: l) = c + 8 * idxFor8 l := rfl

theorem gainAt8_one (idx : ℕ) : gainAt8 idx 1 = idx % 8 := by
  simp [gainAt8]

theorem gainAt8_succ (idx j : ℕ) (hj : 1 ≤ j) :
    gainAt8 idx (j + 1) = gainAt8 (idx / 8) j := by
  have h1 : j + 1 ≠ 0 := by omega
  have h2 : j ≠ 0 := by omega
  simp only [gainAt8, if_neg h1, if_neg h2]
  have h3 : j + 1 - 1 = j := by omega
  rw [h3, Nat.div_div_eq_div_mul]
  have h4 : (8 : ℕ) ^ j = 8 ^ (j - 1) * 8 := by
    conv_lhs => rw [show j = (j - 1) + 1 from by omega]
    rw [pow_succ]
  rw [h4, Nat.mul_comm (8 ^ (j - 1)) 8]

theorem idxFor8_div (c : ℕ) (l : List ℕ) (hc : c < 8) :
    idxFor8 (c :: l) / 8 = idxFor8 l := by
  rw [idxFor8_cons, Nat.add_mul_div_left _ _ (by norm_num),
    Nat.div_eq_of_lt hc, Nat.zero_add]

theorem idxFor8_mod (c : ℕ) (l : List ℕ) :
    idxFor8 (c :: l) % 8 = c % 8 := by
  rw [idxFor8_cons, Nat.add_mul_mod_self_left]

/-- Digit extraction: with all digits < 8, `gainAt8 (idxFor8 l) j` reads
off the (j−1)-th digit. -/
theorem gainAt8_idxFor (l : List ℕ) (hl : ∀ c ∈ l, c < 8) (j : ℕ)
    (hj : 1 ≤ j) :
    gainAt8 (idxFor8 l) j = l.getD (j - 1) 0 := by
  revert hl
  induction l generalizing j with
  | nil =>
    simp [idxFor8, gainAt8, Nat.ne_of_gt hj]
  | cons c cs ih =>
    intro hl
    have hlt : c < 8 := hl c (List.mem_cons_self)
    have hcs : ∀ c' ∈ cs, c' < 8 :=
      fun c' hc' => hl c' (List.mem_cons_of_mem c hc')
    cases j with
    | zero => omega
    | succ j' =>
      cases j' with
      | zero =>
        rw [gainAt8_one, idxFor8_mod, Nat.mod_eq_of_lt hlt]
        rfl
      | succ j'' =>
        have h2 : j'' + 2 = (j'' + 1) + 1 := by omega
        rw [h2, gainAt8_succ _ _ (by omega : 1 ≤ j'' + 1),
          idxFor8_div c cs hlt, ih (j'' + 1) (by omega) hcs]
        rfl

/-- The packed counter is bounded by the digit count. -/
theorem idxFor8_lt (l : List ℕ) (hl : ∀ c ∈ l, c < 8) :
    idxFor8 l < 8 ^ l.length := by
  induction l with
  | nil => simp [idxFor8]
  | cons c cs ih =>
    rw [List.length_cons, pow_succ, idxFor8_cons]
    have hc := hl c (List.mem_cons_self)
    have hcs := ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
    omega

/-- The class of `g`: faces sharing its root, in face order. -/
def cclsOf (T K : ℕ) (d : CDec T K) (g : Fin 6) : List (Fin 6) :=
  (List.finRange 6).filter (fun h => crootF T K d h = crootF T K d g)

theorem crootF_mem_cclsOf (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    crootF T K d g ∈ cclsOf T K d g := by
  simp [cclsOf, crootF_crootF]

theorem cclsOf_ne_nil (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    cclsOf T K d g ≠ [] :=
  List.ne_nil_of_mem (crootF_mem_cclsOf T K d g)

theorem mem_cclsOf_root {T K : ℕ} {d : CDec T K} {g h : Fin 6}
    (hh : h ∈ cclsOf T K d g) : crootF T K d h = crootF T K d g :=
  of_decide_eq_true (List.mem_filter.mp hh).2

theorem mem_cclsOf_exists_gain {T K : ℕ} {d : CDec T K} {g h : Fin 6}
    (hh : h ∈ cclsOf T K d g) :
    ∃ w : Fin 8, d h = cact w (d (crootF T K d g)) := by
  obtain ⟨w, hw⟩ := exists_cgain_from_root T K d h
  exact ⟨w, by rwa [mem_cclsOf_root hh] at hw⟩

/-- Gains for a whole class at once, with the root pinned to the
identity gain (the census's position-0 convention). -/
theorem exists_ccls_gains (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    ∃ w : Fin 6 → Fin 8,
      (∀ h ∈ cclsOf T K d g, d h = cact (w h) (d (crootF T K d g))) ∧
      w (crootF T K d g) = 0 := by
  classical
  have hex : ∀ h : Fin 6, ∃ w : Fin 8,
      h ∈ cclsOf T K d g → d h = cact w (d (crootF T K d g)) := by
    intro h
    by_cases hh : h ∈ cclsOf T K d g
    · obtain ⟨w, hw⟩ := mem_cclsOf_exists_gain hh
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h' => absurd h' hh⟩
  choose w hw using hex
  refine ⟨Function.update w (crootF T K d g) 0, ?_, ?_⟩
  · intro h hh
    rw [Function.update_apply]
    by_cases hr : h = crootF T K d g
    · rw [if_pos hr, hr, cact_one]
    · rw [if_neg hr]
      exact hw h hh
  · rw [Function.update_apply, if_pos rfl]

/-- The chosen gains for a class (Classical choice of
`exists_ccls_gains`). -/
noncomputable def cclsGains (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    Fin 6 → Fin 8 :=
  Classical.choose (exists_ccls_gains T K d g)

theorem cclsGains_spec (T K : ℕ) (d : CDec T K) (g h : Fin 6)
    (hh : h ∈ cclsOf T K d g) :
    d h = cact (cclsGains T K d g h) (d (crootF T K d g)) :=
  (Classical.choose_spec (exists_ccls_gains T K d g)).1 h hh

theorem cclsGains_root (T K : ℕ) (d : CDec T K) (g : Fin 6) :
    cclsGains T K d g (crootF T K d g) = 0 :=
  (Classical.choose_spec (exists_ccls_gains T K d g)).2

/-- The census tuple counter for `g`'s class, given chosen gains. -/
def cclsIdx (T K : ℕ) (d : CDec T K) (g : Fin 6) (w : Fin 6 → Fin 8) : ℕ :=
  idxFor8 ((cclsOf T K d g).tail.map (fun h => encG8 (w h)))

/-- Position 0 of the tuple is the root slot: gain code 0. -/
theorem gainAt8_cclsIdx_zero (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (w : Fin 6 → Fin 8) : gainAt8 (cclsIdx T K d g w) 0 = 0 := by
  simp [gainAt8]

/-- Past the root, `gainAt8` reads off the packed gain codes. -/
theorem gainAt8_cclsIdx (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (w : Fin 6 → Fin 8) (j : ℕ) (hj : 1 ≤ j) :
    gainAt8 (cclsIdx T K d g w) j =
      ((cclsOf T K d g).tail.map (fun h => encG8 (w h))).getD (j - 1) 0 := by
  apply gainAt8_idxFor _ _ j hj
  intro c hc
  obtain ⟨h, -, rfl⟩ := List.mem_map.mp hc
  exact encG8_lt _

/-- The tuple counter fits the census's `8 ^ (members.length - 1)`
range. -/
theorem cclsIdx_lt (T K : ℕ) (d : CDec T K) (g : Fin 6)
    (w : Fin 6 → Fin 8) :
    cclsIdx T K d g w < 8 ^ ((cclsOf T K d g).length - 1) := by
  have hlen : ((cclsOf T K d g).tail.map (fun h => encG8 (w h))).length =
      (cclsOf T K d g).length - 1 := by
    rw [List.length_map, List.length_tail]
  unfold cclsIdx
  rw [← hlen]
  apply idxFor8_lt
  intro c hc
  obtain ⟨h, -, rfl⟩ := List.mem_map.mp hc
  exact encG8_lt _

end AnyK3D
