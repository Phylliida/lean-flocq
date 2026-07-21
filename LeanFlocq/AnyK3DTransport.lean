/-
# M4-C4: rotation transport — the simplified version

The endgame design (§C4) planned a spatial rotation of ℤ³ composed with
an orientation map, with "axis negation on ℤ³" as the flagged risk.
Ground-truthing the conjugation identity in Python (monotile/check_conj*.py)
showed the actual transport is far simpler — **no spatial rotation at
all**: rotating the decoration relabels orientations by right
multiplication (`compat (rotDec g d) ax o1 o2 = compat d ax (o1·g) (o2·g)`),
so the tiling transport is a pure orientation relabeling with the
identical periods. The load-bearing finite fact, verified for all
41,472 triples:

    EQPERM[g][teq(ax, o1, o2)] = teq(ax, rmul[g][o1], rmul[g][o2])

(`epAt_teqN` below, one `native_decide`). This also matches the census's
canonicalization action (orbits3d's eqperm), so the Route-A coverage
statement uses the same `permMask`.

Contents: Nat-level table access, the finite facts (all `native_decide`),
`permMask` (bit-reindex by eqperm), and the transport theorems:
`tiling_transport` (forward), `periodic_transport`, `permMask_inv` +
`periodic_transport_back` (backward, for the periodic branch of the M5
assembly).
-/
import Mathlib
import LeanFlocq.AnyK3DCerts
import LeanFlocq.AnyK3DFrontier

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## Nat-level table access -/

/-- The 84-equation permutation of rotation `g`. -/
def epAt (g i : ℕ) : ℕ := (eqperm.getD g #[]).getD i 0

/-- Right multiplication by rotation `g` on orientations. -/
def rmulAt (g o : ℕ) : ℕ := (rmul.getD g #[]).getD o 0

/-- The inverse rotation's index. -/
def rotInvAt (g : ℕ) : ℕ := rotInv.getD g 0

/-- Nat-level triple→equation map. -/
def teqN (a o1 o2 : ℕ) : ℕ := tEq.getD (a * 576 + o1 * 24 + o2) 0

/-! ## Finite facts (all native_decide, matching the Python checks) -/

theorem tEq_lt : ∀ i < 1728, tEq.getD i 0 < 84 := by native_decide

theorem epAt_lt : ∀ g < 24, ∀ i < 84, epAt g i < 84 := by native_decide

theorem rmulAt_lt : ∀ g < 24, ∀ o < 24, rmulAt g o < 24 := by native_decide

theorem rotInvAt_lt : ∀ g < 24, rotInvAt g < 24 := by native_decide

/-- The conjugation identity: eqperm transports the triple's equation to
the right-multiplied triple's equation (41,472 cases). -/
theorem epAt_teqN : ∀ g < 24, ∀ a < 3, ∀ o1 < 24, ∀ o2 < 24,
    epAt g (teqN a o1 o2) = teqN a (rmulAt g o1) (rmulAt g o2) := by
  native_decide

/-- eqperm is a group action: the inverse rotation inverts it. -/
theorem epAt_inv : ∀ g < 24, ∀ i < 84,
    epAt g (epAt (rotInvAt g) i) = i := by
  native_decide

/-- rmul is a group action: the inverse rotation inverts it (both
compositions). -/
theorem rmulAt_inv : ∀ g < 24, ∀ o < 24,
    rmulAt g (rmulAt (rotInvAt g) o) = o ∧
      rmulAt (rotInvAt g) (rmulAt g o) = o := by
  native_decide

theorem teqN_lt (a o1 o2 : ℕ) (ha : a < 3) (h1 : o1 < 24) (h2 : o2 < 24) :
    teqN a o1 o2 < 84 :=
  tEq_lt _ (by omega)

/-- Bridge between the Fin-level and Nat-level triple maps. -/
theorem teq_val (ax : Fin 3) (o1 o2 : Fin 24) :
    (teq ax o1 o2).val = teqN ax.val o1.val o2.val := by
  have h : tEq.getD (ax.val * 576 + o1.val * 24 + o2.val) 0 < 84 :=
    tEq_lt _ (by
      have h1 := ax.isLt; have h2 := o1.isLt; have h3 := o2.isLt; omega)
  simp only [teq, teqN, tIdx, f84]
  exact Nat.mod_eq_of_lt h

/-! ## permMask: bit-reindexing by eqperm -/

/-- Bit `i` of `permMask g m` = bit `epAt g i` of `m`. -/
def permMask (g m : ℕ) : ℕ :=
  (List.range 84).foldl
    (fun acc i => if m.testBit (epAt g i) then acc ||| (1 <<< i) else acc) 0

theorem testBit_permMask (g m : ℕ) (j : ℕ) (hj : j < 84) :
    (permMask g m).testBit j = m.testBit (epAt g j) := by
  unfold permMask
  rw [testBit_foldl_or_bits (fun i => i) (fun i => m.testBit (epAt g i))
    (List.range 84) 0 j]
  rw [Bool.eq_iff_iff]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, -, hi, rfl⟩
    exact hi
  · intro h
    exact ⟨j, hj, h, rfl⟩

theorem permMask_lt (g m : ℕ) : permMask g m < 2 ^ 84 := by
  unfold permMask
  exact foldl_or_pow_lt _ 84 _ (fun n hn => List.mem_range.mp hn) 0
    (by norm_num)

theorem testBit_permMask_ge (g m : ℕ) (j : ℕ) (hj : 84 ≤ j) :
    (permMask g m).testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (permMask_lt g m)
    (Nat.pow_le_pow_right (by norm_num) hj))

/-! ## The transport -/

/-- Relabel an orientation by the inverse rotation (right
multiplication). -/
def relabelO (g : ℕ) (hg : g < 24) (o : Fin 24) : Fin 24 :=
  ⟨rmulAt (rotInvAt g) o.val,
   rmulAt_lt (rotInvAt g) (rotInvAt_lt g hg) o.val o.isLt⟩

theorem relabelO_val (g : ℕ) (hg : g < 24) (o : Fin 24) :
    (relabelO g hg o).val = rmulAt (rotInvAt g) o.val := rfl

/-- The pointwise identity behind the transport: the permuted mask's
relation at relabeled orientations is the original relation. -/
theorem relOfMask_relabel (g : ℕ) (hg : g < 24) (m : ℕ) (ax : Fin 3)
    (o1 o2 : Fin 24) :
    relOfMask (permMask g m) ax (relabelO g hg o1) (relabelO g hg o2) =
      relOfMask m ax o1 o2 := by
  have hb1 := rmulAt_lt (rotInvAt g) (rotInvAt_lt g hg) o1.val o1.isLt
  have hb2 := rmulAt_lt (rotInvAt g) (rotInvAt_lt g hg) o2.val o2.isLt
  show (permMask g m).testBit
      (teq ax (relabelO g hg o1) (relabelO g hg o2)).val =
    m.testBit (teq ax o1 o2).val
  rw [teq_val ax (relabelO g hg o1) (relabelO g hg o2), relabelO_val,
    relabelO_val,
    testBit_permMask g m _ (teqN_lt _ _ _ ax.isLt hb1 hb2),
    epAt_teqN g hg ax.val ax.isLt _ hb1 _ hb2,
    (rmulAt_inv g hg o1.val o1.isLt).1,
    (rmulAt_inv g hg o2.val o2.isLt).1,
    ← teq_val ax o1 o2]

/-- **Transport (forward).** A tiling of a mask's relation relabels to a
tiling of the permuted mask's relation. -/
theorem tiling_transport (g : ℕ) (hg : g < 24) (m : ℕ)
    (ω : ℤ × ℤ × ℤ → Fin 24) (hω : IsTiling (relOfMask m) ω) :
    IsTiling (relOfMask (permMask g m)) (fun p => relabelO g hg (ω p)) := by
  intro p
  obtain ⟨h0, h1, h2⟩ := hω p
  refine ⟨?_, ?_, ?_⟩
  · rw [relOfMask_relabel g hg m 0 (ω p) (ω (p.1 + 1, p.2.1, p.2.2))]
    exact h0
  · rw [relOfMask_relabel g hg m 1 (ω p) (ω (p.1, p.2.1 + 1, p.2.2))]
    exact h1
  · rw [relOfMask_relabel g hg m 2 (ω p) (ω (p.1, p.2.1, p.2.2 + 1))]
    exact h2

/-- Periodic tilings transport with the *same* periods (the relabeling is
pointwise). -/
theorem periodic_transport (g : ℕ) (hg : g < 24) (m : ℕ)
    (hp : PeriodicRel (relOfMask m)) :
    PeriodicRel (relOfMask (permMask g m)) := by
  obtain ⟨ω, hω, a, b, c, ha, hb, hc, pa, pb, pc⟩ := hp
  refine ⟨fun p => relabelO g hg (ω p), tiling_transport g hg m ω hω,
    a, b, c, ha, hb, hc, ?_, ?_, ?_⟩
  · exact fun p => congrArg (relabelO g hg) (pa p)
  · exact fun p => congrArg (relabelO g hg) (pb p)
  · exact fun p => congrArg (relabelO g hg) (pc p)

/-- Permuting by `g` and then by its inverse is the identity (on masks
below `2^84`, i.e. all census masks). -/
theorem permMask_inv (g : ℕ) (hg : g < 24) (m : ℕ) (hm : m < 2 ^ 84) :
    permMask (rotInvAt g) (permMask g m) = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 84
  · rw [testBit_permMask _ _ j hj,
      testBit_permMask g m _
        (epAt_lt (rotInvAt g) (rotInvAt_lt g hg) j hj),
      epAt_inv g hg j hj]
  · rw [testBit_permMask_ge _ _ j (by omega)]
    rw [Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **Transport (backward).** For the periodic branch of the assembly:
a periodic tiling of the permuted mask comes from one of the original. -/
theorem periodic_transport_back (g : ℕ) (hg : g < 24) (m : ℕ)
    (hm : m < 2 ^ 84) (hp : PeriodicRel (relOfMask (permMask g m))) :
    PeriodicRel (relOfMask m) := by
  have h := periodic_transport (rotInvAt g) (rotInvAt_lt g hg)
    (permMask g m) hp
  rwa [permMask_inv g hg m hm] at h

end AnyK3D
