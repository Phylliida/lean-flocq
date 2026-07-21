/-
# M3b: profile masks as bits + the encoding bridge + class structure

Bricks of the completeness proof (DESIGN-anyk3d-endgame.md §1):

* B1 — bit-reading lemmas: a generic characterization of the
  or-accumulation folds used by `profileMask` (defined here) and
  `classMask` (from the census enumerator), so mask equalities can be
  proven bitwise via `Nat.eq_of_testBit_eq`.
* B2 — the encoding bridge: the census's table arithmetic (`gmul16`,
  `ginv16`, `negTau` over codes 0..15) agrees with M2's gain algebra
  (`gmul`, `ginv`) under `encG`. All finite, kernel-`decide`d.
* B3 — the face equivalence (`related`), orbit roots (`rootF`), and the
  orbit invariant `rootF_eq_iff_related`.
* B6 — the stabilizer mask of a root face: feasible subgroup, hence a
  member of the census's `subMasks`.
* B5 — class lists (`clsOf`), chosen gains (`exists_cls_gains`), and the
  tuple counter (`clsIdx`) with its base-16 digit lemmas
  (`gainAt_clsIdx`, `clsIdx_lt`).
-/
import Mathlib
import LeanFlocq.AnyK3DCensusFast

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## B1: the generic or-accumulation fold -/

/-- Bits of a fold that or-in `1 <<< f x` for each `x` passing `c`:
bit `j` of the result = bit `j` of the seed, or some listed `x` passes
`c` with `f x = j`. -/
theorem testBit_foldl_or_gen {α : Type*} (f : α → ℕ) (c : α → Bool)
    (l : List α) (acc : ℕ) (j : ℕ) :
    ((l.foldl (fun a x => if c x then a ||| (1 <<< f x) else a) acc).testBit j)
      = (acc.testBit j || l.any fun x => c x && decide (f x = j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases hx : c x
    · simp only [hx, if_pos, Nat.testBit_or, Nat.one_shiftLeft,
        Nat.testBit_two_pow]
      by_cases hj : f x = j
      · simp [hj]
      · simp [hj]
    · simp [hx]

/-- The 84-bit profile mask of a held-equation predicate. -/
def profileMask (hs : Fin 84 → Bool) : ℕ :=
  (List.finRange 84).foldl
    (fun acc i => if hs i then acc ||| (1 <<< i.val) else acc) 0

theorem testBit_profileMask (hs : Fin 84 → Bool) (j : ℕ) (hj : j < 84) :
    (profileMask hs).testBit j = hs ⟨j, hj⟩ := by
  unfold profileMask
  rw [testBit_foldl_or_gen]
  simp only [Nat.zero_testBit, Bool.false_or]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, -, hi, hij⟩
    exact (Fin.ext hij : i = ⟨j, hj⟩) ▸ hi
  · intro h
    exact ⟨⟨j, hj⟩, List.mem_finRange _, h, rfl⟩

theorem testBit_profileMask_ge (hs : Fin 84 → Bool) (j : ℕ)
    (hj : 84 ≤ j) : (profileMask hs).testBit j = false := by
  unfold profileMask
  rw [testBit_foldl_or_gen]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_false]
  intro i _
  have hi := i.isLt
  have : (i : ℕ) ≠ j := by omega
  simp [this]

/-- `classMask` bits, via the same generic fold (Array.foldl runs through
its list). Bit `j` is set iff some relevant-equation entry has bit index
`j` and its held-condition passes. -/
theorem testBit_classMask (re : Array (ℕ × ℕ × ℕ × ℕ)) (idx H : ℕ)
    (j : ℕ) :
    (classMask re idx H).testBit j
      = re.toList.any fun e =>
          H.testBit (gmul16 (ginv16 (gainAt idx e.2.1))
            (gmul16 (negTau e.2.2.2) (gainAt idx e.2.2.1))) &&
          decide (e.1 = j) := by
  unfold classMask
  rw [← Array.foldl_toList]
  have := testBit_foldl_or_gen (fun e : ℕ × ℕ × ℕ × ℕ => e.1)
    (fun e => H.testBit (gmul16 (ginv16 (gainAt idx e.2.1))
      (gmul16 (negTau e.2.2.2) (gainAt idx e.2.2.1))))
    re.toList 0 j
  simp only [Nat.zero_testBit, Bool.false_or] at this
  rw [← this]

/-! ## B2: the encoding bridge (finite, kernel-checked) -/

theorem encG_lt (w : Gain) : encG w < 16 := by
  obtain ⟨⟨c, hc⟩, s⟩ := w
  simp only [encG]
  cases s <;> simp <;> omega

theorem decG_encG : ∀ w : Gain, decG (encG w) = w := by decide

theorem gmul16_encG : ∀ a b : Gain,
    gmul16 (encG a) (encG b) = encG (gmul a b) := by decide

theorem ginv16_encG : ∀ a : Gain, ginv16 (encG a) = encG (ginv a) := by
  decide

theorem negTau_encG (t : Fin 8) : negTau t.val = encG (t, true) := rfl

/-! ## B3: the face equivalence and roots

Faces of a decoration fall into gain-orbits: `g ~ h` iff some gain carries
`d h` to `d g`. Each orbit's least face is its root; every face's
decoration is a gain-image of its root's. This is the structure the census
enumerates, realized semantically. -/

/-- Two faces related by some gain. -/
def related (K : ℕ) (d : Dec K) (g h : Fin 6) : Prop :=
  ∃ w : Gain, d g = actF w (d h)

instance (K : ℕ) (d : Dec K) (g h : Fin 6) :
    Decidable (related K d g h) := by
  unfold related; infer_instance

theorem related_refl (K : ℕ) (d : Dec K) (g : Fin 6) : related K d g g :=
  ⟨(0, false), (actF_one _).symm⟩

theorem related_symm {K : ℕ} {d : Dec K} {g h : Fin 6}
    (hr : related K d g h) : related K d h g := by
  obtain ⟨w, hw⟩ := hr
  exact ⟨ginv w, by rw [hw, actF_inv_actF]⟩

theorem related_trans {K : ℕ} {d : Dec K} {g h k : Fin 6}
    (h1 : related K d g h) (h2 : related K d h k) : related K d g k := by
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  exact ⟨gmul w1 w2, by rw [hw1, hw2, actF_actF]⟩

/-- The gain-orbit of `g`, as a finset. -/
def rootClass (K : ℕ) (d : Dec K) (g : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter (fun h => related K d h g)

theorem rootClass_nonempty (K : ℕ) (d : Dec K) (g : Fin 6) :
    (rootClass K d g).Nonempty :=
  ⟨g, by simp [rootClass, related_refl]⟩

/-- The root of `g`'s orbit: its least member. -/
def rootF (K : ℕ) (d : Dec K) (g : Fin 6) : Fin 6 :=
  (rootClass K d g).min' (rootClass_nonempty K d g)

theorem mem_rootClass {K : ℕ} {d : Dec K} {g h : Fin 6} :
    h ∈ rootClass K d g ↔ related K d h g := by
  simp [rootClass]

theorem related_rootF (K : ℕ) (d : Dec K) (g : Fin 6) :
    related K d (rootF K d g) g :=
  mem_rootClass.mp ((rootClass K d g).min'_mem _)

theorem rootF_le (K : ℕ) (d : Dec K) (g : Fin 6) : rootF K d g ≤ g :=
  (rootClass K d g).min'_le g (mem_rootClass.mpr (related_refl K d g))

theorem rootClass_eq_of_related {K : ℕ} {d : Dec K} {g h : Fin 6}
    (hr : related K d g h) : rootClass K d g = rootClass K d h := by
  ext x
  simp only [mem_rootClass]
  exact ⟨fun hx => related_trans hx hr,
         fun hx => related_trans hx (related_symm hr)⟩

theorem rootF_eq_of_related {K : ℕ} {d : Dec K} {g h : Fin 6}
    (hr : related K d g h) : rootF K d g = rootF K d h := by
  unfold rootF
  congr 1
  exact rootClass_eq_of_related hr

theorem rootF_rootF (K : ℕ) (d : Dec K) (g : Fin 6) :
    rootF K d (rootF K d g) = rootF K d g :=
  rootF_eq_of_related (related_rootF K d g)

/-- Roots agree exactly on related faces — the orbit invariant. -/
theorem rootF_eq_iff_related {K : ℕ} {d : Dec K} {g h : Fin 6} :
    rootF K d g = rootF K d h ↔ related K d g h := by
  constructor
  · intro he
    exact related_trans (related_symm (related_rootF K d g))
      (he ▸ related_rootF K d h)
  · exact rootF_eq_of_related

/-- Every face is a gain-image of its root: the B5 input. -/
theorem exists_gain_from_root (K : ℕ) (d : Dec K) (g : Fin 6) :
    ∃ w : Gain, d g = actF w (d (rootF K d g)) :=
  related_symm (related_rootF K d g)

/-! ## B6: the stabilizer mask

The encoded stabilizer of a root's face-function is a feasible subgroup
mask — hence a member of the census's `subMasks` enumeration. -/

/-- Missing half of the code bijection below 16. -/
theorem encG_decG : ∀ n : Fin 16, encG (decG n.val) = n.val := by decide

/-- The encoded stabilizer: bit `n` set iff the gain coded `n` fixes `F`. -/
def stabMask {K : ℕ} (F : Fin K → Fin K → Bool) : ℕ :=
  (List.range 16).foldl
    (fun acc n => if decide (actF (decG n) F = F) then acc ||| (1 <<< n)
      else acc) 0

theorem testBit_stabMask {K : ℕ} (F : Fin K → Fin K → Bool) (n : ℕ)
    (hn : n < 16) :
    (stabMask F).testBit n = decide (actF (decG n) F = F) := by
  unfold stabMask
  rw [testBit_foldl_or_gen (fun m => m)
    (fun m => decide (actF (decG m) F = F))]
  rw [Bool.eq_iff_iff]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, -, hm, rfl⟩
    simpa using hm
  · intro h
    exact ⟨n, hn, by simpa using h, rfl⟩

/-- Or-accumulation over sub-16 bit positions stays below 2^16. -/
theorem foldl_or_lt (c : ℕ → Bool) :
    ∀ (l : List ℕ), (∀ n ∈ l, n < 16) → ∀ acc : ℕ, acc < 65536 →
      l.foldl (fun a n => if c n then a ||| (1 <<< n) else a) acc < 65536
  | [], _, acc, hacc => hacc
  | n :: ns, hl, acc, hacc => by
    simp only [List.foldl_cons]
    apply foldl_or_lt c ns (fun m hm => hl m (List.mem_cons_of_mem _ hm))
    by_cases hc : c n
    · simp only [hc, if_pos]
      have h1 : (1 <<< n) < 65536 := by
        rw [Nat.one_shiftLeft]
        calc 2 ^ n ≤ 2 ^ 15 :=
              Nat.pow_le_pow_right (by norm_num)
                (by have := hl n (List.mem_cons_self ..); omega)
          _ < 65536 := by norm_num
      have : acc ||| (1 <<< n) < 2 ^ 16 :=
        Nat.or_lt_two_pow (by omega) (by omega)
      omega
    · simpa [hc]

theorem stabMask_lt {K : ℕ} (F : Fin K → Fin K → Bool) :
    stabMask F < 65536 := by
  unfold stabMask
  exact foldl_or_lt _ _ (by simp) 0 (by norm_num)

theorem testBit_stabMask_ge {K : ℕ} (F : Fin K → Fin K → Bool) (n : ℕ)
    (hn : 16 ≤ n) : (stabMask F).testBit n = false := by
  have h1 : stabMask F < 2 ^ n :=
    lt_of_lt_of_le (stabMask_lt F)
      (le_trans (by norm_num : (65536 : ℕ) ≤ 2 ^ 16)
        (Nat.pow_le_pow_right (by norm_num) hn))
  exact Nat.testBit_lt_two_pow h1

/-- The stabilizer mask passes the census's subgroup check. -/
theorem stabMask_isSubgroup {K : ℕ} (F : Fin K → Fin K → Bool) :
    isSubgroupM (stabMask F) = true := by
  have hbit : ∀ n < 16, (stabMask F).testBit n
      = decide (actF (decG n) F = F) := fun n hn => testBit_stabMask F n hn
  unfold isSubgroupM maskHasAll
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hbit 0 (by norm_num)]
    simp [show (decG 0 : Gain) = ((0 : Fin 8), false) from rfl, actF_one]
  · intro a ha
    by_cases hA : (stabMask F).testBit a
    · right
      intro b hb
      by_cases hB : (stabMask F).testBit b
      · right
        rw [hbit a ha] at hA
        rw [hbit b hb] at hB
        simp only [decide_eq_true_eq] at hA hB
        have hab : gmul16 a b = encG (gmul (decG a) (decG b)) := by
          have hae : encG (decG a) = a := encG_decG ⟨a, ha⟩
          have hbe : encG (decG b) = b := encG_decG ⟨b, hb⟩
          conv_lhs => rw [← hae, ← hbe]
          exact gmul16_encG _ _
        have hlt : gmul16 a b < 16 := hab ▸ encG_lt _
        rw [hbit _ hlt, hab]
        simp only [decide_eq_true_eq, decG_encG]
        rw [← actF_actF, hB, hA]
      · left; simp [hB]
    · left; simp [hA]
  · intro a ha
    by_cases hA : (stabMask F).testBit a
    · right
      rw [hbit a ha] at hA
      simp only [decide_eq_true_eq] at hA
      have hai : ginv16 a = encG (ginv (decG a)) := by
        have hae : encG (decG a) = a := encG_decG ⟨a, ha⟩
        conv_lhs => rw [← hae]
        exact ginv16_encG _
      have hlt : ginv16 a < 16 := hai ▸ encG_lt _
      rw [hbit _ hlt, hai]
      simp only [decide_eq_true_eq, decG_encG]
      rw [← hA, actF_inv_actF, hA]
    · left; simp [hA]

/-- The stabilizer mask is even-feasible on a nonempty grid. -/
theorem stabMask_feasible {K : ℕ} (hK : 1 ≤ K)
    (F : Fin K → Fin K → Bool) : feasibleM (stabMask F) = true := by
  unfold feasibleM
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [testBit_stabMask F 1 (by norm_num)]
    simp only [decide_eq_false_iff_not]
    intro h
    exact absurd rfl (realized_stab_feasible hK 0 F
      (by simpa [show (decG 1 : Gain) = ((0 : Fin 8), true) from rfl]
        using h)).1
  · rw [testBit_stabMask F 9 (by norm_num)]
    simp only [decide_eq_false_iff_not]
    intro h
    exact absurd rfl (realized_stab_feasible hK 4 F
      (by simpa [show (decG 9 : Gain) = ((4 : Fin 8), true) from rfl]
        using h)).2.1
  · rw [testBit_stabMask F 15 (by norm_num)]
    simp only [decide_eq_false_iff_not]
    intro h
    exact absurd rfl (realized_stab_feasible hK 7 F
      (by simpa [show (decG 15 : Gain) = ((7 : Fin 8), true) from rfl]
        using h)).2.2

/-- The stabilizer mask is enumerated by the census. -/
theorem stabMask_mem_subMasks {K : ℕ} (hK : 1 ≤ K)
    (F : Fin K → Fin K → Bool) : stabMask F ∈ subMasks.toList := by
  unfold subMasks
  simp only [List.toList_toArray, List.mem_filter]
  constructor
  · exact List.mem_range.mpr (stabMask_lt F)
  · simp [stabMask_isSubgroup F, stabMask_feasible hK F]

/-! ## B5: gains and the tuple index

Each face of a class is a gain-image of the class root's face (B3,
`exists_gain_from_root`). Packing the encoded gains as base-16 digits in
Horner form reproduces the census's `gainAt` extraction, so a class's
tuple counter `idx` is built semantically and shown to satisfy the
census's digit and size constraints. -/

/-- Horner packing of base-16 digits:
`idxFor [c₁, c₂, …] = c₁ + 16·(c₂ + 16·(…))`. -/
def idxFor : List ℕ → ℕ := List.foldr (fun c acc => c + 16 * acc) 0

theorem idxFor_cons (c : ℕ) (l : List ℕ) :
    idxFor (c :: l) = c + 16 * idxFor l := rfl

theorem gainAt_one (idx : ℕ) : gainAt idx 1 = idx % 16 := by
  simp [gainAt]

theorem gainAt_succ (idx j : ℕ) (hj : 1 ≤ j) :
    gainAt idx (j + 1) = gainAt (idx / 16) j := by
  have h1 : j + 1 ≠ 0 := by omega
  have h2 : j ≠ 0 := by omega
  simp only [gainAt, if_neg h1, if_neg h2]
  have h3 : j + 1 - 1 = j := by omega
  rw [h3, Nat.div_div_eq_div_mul]
  have h4 : (16 : ℕ) ^ j = 16 ^ (j - 1) * 16 := by
    conv_lhs => rw [show j = (j - 1) + 1 from by omega]
    rw [pow_succ]
  rw [h4, Nat.mul_comm (16 ^ (j - 1)) 16]

theorem idxFor_div (c : ℕ) (l : List ℕ) (hc : c < 16) :
    idxFor (c :: l) / 16 = idxFor l := by
  rw [idxFor_cons, Nat.add_mul_div_left _ _ (by norm_num),
    Nat.div_eq_of_lt hc, Nat.zero_add]

theorem idxFor_mod (c : ℕ) (l : List ℕ) :
    idxFor (c :: l) % 16 = c % 16 := by
  rw [idxFor_cons, Nat.add_mul_mod_self_left]

/-- Digit extraction: with all digits < 16, `gainAt (idxFor l) j` reads
off the (j−1)-th digit. (Position 0 is the root slot, handled
definitionally by `gainAt`.) -/
theorem gainAt_idxFor (l : List ℕ) (hl : ∀ c ∈ l, c < 16) (j : ℕ)
    (hj : 1 ≤ j) :
    gainAt (idxFor l) j = l.getD (j - 1) 0 := by
  revert hl
  induction l generalizing j with
  | nil =>
    simp [idxFor, gainAt, Nat.ne_of_gt hj]
  | cons c cs ih =>
    intro hl
    have hlt : c < 16 := hl c (List.mem_cons_self)
    have hcs : ∀ c' ∈ cs, c' < 16 :=
      fun c' hc' => hl c' (List.mem_cons_of_mem c hc')
    cases j with
    | zero => omega
    | succ j' =>
      cases j' with
      | zero =>
        rw [gainAt_one, idxFor_mod, Nat.mod_eq_of_lt hlt]
        rfl
      | succ j'' =>
        have h2 : j'' + 2 = (j'' + 1) + 1 := by omega
        rw [h2, gainAt_succ _ _ (by omega : 1 ≤ j'' + 1),
          idxFor_div c cs hlt, ih (j'' + 1) (by omega) hcs]
        rfl

/-- The packed counter is bounded by the digit count. -/
theorem idxFor_lt (l : List ℕ) (hl : ∀ c ∈ l, c < 16) :
    idxFor l < 16 ^ l.length := by
  induction l with
  | nil => simp [idxFor]
  | cons c cs ih =>
    rw [List.length_cons, pow_succ, idxFor_cons]
    have hc := hl c (List.mem_cons_self)
    have hcs := ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
    omega

/-- The class of `g`: faces sharing its root, in face order. -/
def clsOf (K : ℕ) (d : Dec K) (g : Fin 6) : List (Fin 6) :=
  (List.finRange 6).filter (fun h => rootF K d h = rootF K d g)

theorem rootF_mem_clsOf (K : ℕ) (d : Dec K) (g : Fin 6) :
    rootF K d g ∈ clsOf K d g := by
  simp [clsOf, rootF_rootF]

theorem clsOf_ne_nil (K : ℕ) (d : Dec K) (g : Fin 6) :
    clsOf K d g ≠ [] :=
  List.ne_nil_of_mem (rootF_mem_clsOf K d g)

theorem mem_clsOf_root {K : ℕ} {d : Dec K} {g h : Fin 6}
    (hh : h ∈ clsOf K d g) : rootF K d h = rootF K d g :=
  of_decide_eq_true (List.mem_filter.mp hh).2

theorem mem_clsOf_exists_gain {K : ℕ} {d : Dec K} {g h : Fin 6}
    (hh : h ∈ clsOf K d g) : ∃ w : Gain, d h = actF w (d (rootF K d g)) := by
  obtain ⟨w, hw⟩ := exists_gain_from_root K d h
  exact ⟨w, by rwa [mem_clsOf_root hh] at hw⟩

/-- Gains for a whole class at once, with the root pinned to the identity
gain (the census's position-0 convention). -/
theorem exists_cls_gains (K : ℕ) (d : Dec K) (g : Fin 6) :
    ∃ w : Fin 6 → Gain,
      (∀ h ∈ clsOf K d g, d h = actF (w h) (d (rootF K d g))) ∧
      w (rootF K d g) = ((0 : Fin 8), false) := by
  classical
  have hex : ∀ h : Fin 6, ∃ w : Gain,
      h ∈ clsOf K d g → d h = actF w (d (rootF K d g)) := by
    intro h
    by_cases hh : h ∈ clsOf K d g
    · obtain ⟨w, hw⟩ := mem_clsOf_exists_gain hh
      exact ⟨w, fun _ => hw⟩
    · exact ⟨((0 : Fin 8), false), fun h' => absurd h' hh⟩
  choose w hw using hex
  refine ⟨Function.update w (rootF K d g) ((0 : Fin 8), false), ?_, ?_⟩
  · intro h hh
    rw [Function.update_apply]
    by_cases hr : h = rootF K d g
    · rw [if_pos hr, hr, actF_one]
    · rw [if_neg hr]
      exact hw h hh
  · rw [Function.update_apply, if_pos rfl]

/-- The census tuple counter for `g`'s class, given chosen gains. -/
def clsIdx (K : ℕ) (d : Dec K) (g : Fin 6) (w : Fin 6 → Gain) : ℕ :=
  idxFor ((clsOf K d g).tail.map (fun h => encG (w h)))

/-- Position 0 of the tuple is the root slot: gain code 0. -/
theorem gainAt_clsIdx_zero (K : ℕ) (d : Dec K) (g : Fin 6)
    (w : Fin 6 → Gain) : gainAt (clsIdx K d g w) 0 = 0 := by
  simp [gainAt]

/-- Past the root, `gainAt` reads off the packed gain codes. -/
theorem gainAt_clsIdx (K : ℕ) (d : Dec K) (g : Fin 6) (w : Fin 6 → Gain)
    (j : ℕ) (hj : 1 ≤ j) :
    gainAt (clsIdx K d g w) j =
      ((clsOf K d g).tail.map (fun h => encG (w h))).getD (j - 1) 0 := by
  apply gainAt_idxFor _ _ j hj
  intro c hc
  obtain ⟨h, -, rfl⟩ := List.mem_map.mp hc
  exact encG_lt _

/-- The tuple counter fits the census's `16 ^ (members.length - 1)`
range. -/
theorem clsIdx_lt (K : ℕ) (d : Dec K) (g : Fin 6) (w : Fin 6 → Gain) :
    clsIdx K d g w < 16 ^ ((clsOf K d g).length - 1) := by
  have hlen : ((clsOf K d g).tail.map (fun h => encG (w h))).length =
      (clsOf K d g).length - 1 := by
    rw [List.length_map, List.length_tail]
  unfold clsIdx
  rw [← hlen]
  apply idxFor_lt
  intro c hc
  obtain ⟨h, -, rfl⟩ := List.mem_map.mp hc
  exact encG_lt _

/-! ## B4: partition membership

`partitionsN` enumerates set partitions by inserting the current minimum
either as a new singleton class at the front or at the head of an
existing class. The census's class union is order-insensitive, so
membership only needs *some* permutation of the semantic partition (B3's
classes) to be enumerator-realizable. We show: for sorted `l`, any
partition with sorted ascending classes and `flatten ~ l` has a
realizable permutation — the peeling recursion keeps the class
containing the current minimum in front, and re-orders freely otherwise.

(The naive "ascending heads" order does not work directly: after peeling
a non-singleton minimum class its remainder can jump ahead of a later
singleton class, e.g. `[[0,5],[1,2]]` — hence the permuted statement.) -/

open List

/-- Replacing the element at position `i` is, up to permutation, erasing
it and consing the replacement. -/
theorem perm_set_getElem {α : Type*} [BEq α] [LawfulBEq α] (l : List α)
    (i : ℕ) (hi : i < l.length) (a : α) :
    l.set i a ~ a :: l.erase l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, List.erase_cons_head,
        List.Perm.refl]
    | succ i' =>
      simp only [List.set_cons_succ, List.getElem_cons_succ]
      have hi' : i' < xs.length := by
        simpa [List.length_cons] using hi
      by_cases hxe : x = xs[i']
      · rw [hxe, List.erase_cons_head]
        exact ((List.Perm.cons _ (ih i' hi')).trans (List.Perm.swap _ _ _)).trans
          (List.Perm.cons _
            (List.perm_cons_erase (List.getElem_mem hi')).symm)
      · rw [List.erase_cons]
        simp only [beq_iff_eq, hxe, if_false]
        exact (List.Perm.cons _ (ih i' hi')).trans (List.Perm.swap _ _ _)

/-- Any ascending-class partition of a sorted list is, up to a
permutation of its classes, enumerated by `partitionsN`. -/
theorem exists_perm_mem_partitionsN :
    ∀ (l : List ℕ), l.Sorted (· ≤ ·) →
    ∀ (P : List (List ℕ)),
      (∀ c ∈ P, c ≠ [] ∧ c.Sorted (· ≤ ·)) → P.flatten ~ l →
      ∃ P', P' ~ P ∧ P' ∈ partitionsN l := by
  intro l
  induction l with
  | nil =>
    intro _ P hcls hflat
    have hfl : P.flatten = [] := List.perm_nil.mp hflat
    have hP : P = [] := by
      rcases P with _ | ⟨c, cs⟩
      · rfl
      · rw [List.flatten_cons] at hfl
        exact absurd (List.append_eq_nil_iff.mp hfl).1
          (hcls c (List.mem_cons_self ..)).1
    subst hP
    exact ⟨[], List.Perm.refl _, by simp [partitionsN]⟩
  | cons x rest ih =>
    intro hsort P hcls hflat
    have hrest_sort : rest.Sorted (· ≤ ·) := (List.sorted_cons.mp hsort).2
    have hxmin : ∀ y ∈ rest, x ≤ y := fun y hy =>
      (List.sorted_cons.mp hsort).1 y hy
    have hxl : x ∈ P.flatten :=
      hflat.symm.subset List.mem_cons_self
    obtain ⟨c₀, hc₀P, hxc₀⟩ := List.mem_flatten.mp hxl
    obtain ⟨hc₀ne, hc₀sort⟩ := hcls c₀ hc₀P
    have hxle : ∀ y ∈ c₀, x ≤ y := by
      intro y hy
      have hyl : y ∈ x :: rest :=
        hflat.subset (List.mem_flatten.mpr ⟨c₀, hc₀P, hy⟩)
      rcases List.mem_cons.mp hyl with rfl | hyr
      · exact le_refl _
      · exact hxmin y hyr
    obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hc₀ne
    have hle_hx : h ≤ x := by
      rcases List.mem_cons.mp hxc₀ with rfl | hx
      · exact le_refl _
      · exact (List.sorted_cons.mp hc₀sort).1 x hx
    have hxh : x = h := le_antisymm (hxle h (List.mem_cons_self ..)) hle_hx
    subst hxh
    have ht_sort : t.Sorted (· ≤ ·) := (List.sorted_cons.mp hc₀sort).2
    have hperm₀ : (x :: t) :: P.erase (x :: t) ~ P :=
      (List.perm_cons_erase hc₀P).symm
    by_cases ht : t = []
    · subst ht
      have hfl : (P.erase [x]).flatten ~ rest := by
        have h1 : P.flatten ~ ([x] :: P.erase [x]).flatten :=
          List.Perm.flatten hperm₀.symm
        rw [List.flatten_cons] at h1
        have h2 : P.flatten ~ x :: (P.erase [x]).flatten := by
          simpa using h1
        exact List.Perm.cons_inv (h2.symm.trans hflat)
      obtain ⟨P'', hP''perm, hP''mem⟩ := ih hrest_sort (P.erase [x])
        (fun c hc => hcls c (List.mem_of_mem_erase hc)) hfl
      refine ⟨[x] :: P'', (List.Perm.cons _ hP''perm).trans hperm₀, ?_⟩
      simp only [partitionsN]
      apply List.mem_flatMap.mpr
      exact ⟨P'', hP''mem, List.Mem.head _⟩
    · have hfl : (t :: P.erase (x :: t)).flatten ~ rest := by
        have h1 : P.flatten ~ ((x :: t) :: P.erase (x :: t)).flatten :=
          List.Perm.flatten hperm₀.symm
        rw [List.flatten_cons, List.cons_append,
          ← List.flatten_cons] at h1
        exact List.Perm.cons_inv (h1.symm.trans hflat)
      obtain ⟨P'', hP''perm, hP''mem⟩ := ih hrest_sort
        (t :: P.erase (x :: t))
        (by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨ht, ht_sort⟩
          · exact hcls c (List.mem_of_mem_erase hc)) hfl
      have htP'' : t ∈ P'' := hP''perm.symm.subset List.mem_cons_self
      have hj : P''.idxOf t < P''.length := List.idxOf_lt_length_iff.mpr htP''
      have hget : P''[P''.idxOf t] = t :=
        beq_iff_eq.mp (List.findIdx_getElem (w := hj))
      refine ⟨P''.set (P''.idxOf t) (x :: t), ?_, ?_⟩
      · have hps : P''.set (P''.idxOf t) (x :: t) ~
            (x :: t) :: P''.erase t := by
          have h := perm_set_getElem P'' (P''.idxOf t) hj (x :: t)
          rwa [hget] at h
        have herase : P''.erase t ~ P.erase (x :: t) := by
          have h := List.Perm.erase t hP''perm
          rwa [List.erase_cons_head] at h
        exact hps.trans ((List.Perm.cons _ herase).trans hperm₀)
      · simp only [partitionsN]
        apply List.mem_flatMap.mpr
        refine ⟨P'', hP''mem, List.Mem.tail _ ?_⟩
        apply List.mem_map.mpr
        refine ⟨P''.idxOf t, List.mem_range.mpr hj, ?_⟩
        have hgd : P''.getD (P''.idxOf t) [] = t := by
          rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_pos hj]
          exact hget
        rw [hgd]

end AnyK3D
