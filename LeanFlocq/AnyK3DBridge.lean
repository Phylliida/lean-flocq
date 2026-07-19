/-
# M3b (B1-B2): profile masks as bits + the encoding bridge

First two bricks of the completeness proof (DESIGN-anyk3d-endgame.md §1):

* B1 — bit-reading lemmas: a generic characterization of the
  or-accumulation folds used by `profileMask` (defined here) and
  `classMask` (from the census enumerator), so mask equalities can be
  proven bitwise via `Nat.eq_of_testBit_eq`.
* B2 — the encoding bridge: the census's table arithmetic (`gmul16`,
  `ginv16`, `negTau` over codes 0..15) agrees with M2's gain algebra
  (`gmul`, `ginv`) under `encG`. All finite, kernel-`decide`d.
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

end AnyK3D
