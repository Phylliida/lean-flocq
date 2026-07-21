/-
# M4 (theory half): certificates for relation masks

The mask-level certificate theory of DESIGN-anyk3d-endgame.md §2,
depending only on M1 (`AnyK3D.lean`) so it compiles off the critical path
of the M3b census-completeness work:

  * C1 — `relOfMask` (an 84-bit mask as an SFT relation), bitwise mask
    inclusion, and the monotonicity facts: tilings and periodic tilings
    transport UPWARD along mask inclusion; emptiness transports DOWNWARD.
  * C2 — rectangular-torus certificates: `rect3OK` checker +
    `rect3_sound` (a verified a×b×c wrapped grid yields a fully periodic
    ℤ³ tiling), the 2D `rect_sound` proof with a third axis. The emod
    bridges are restated (as `AnyK2D.lean` already restated them) to keep
    the import graph shallow.
  * C3 prelude — `Box3OK` + `box3OK_of_tiling`: a ℤ³ tiling restricts to
    a valid box tiling of every size (the empty-certificate soundness
    direction; the CNF layer sits on top of this).

Grid encoding matches the Python cert export (`anyk3d_periodic_certs.json`):
base-24 digits, position of torus cell (x, y, z) = (x·b + y)·c + z
(z-fastest).
-/
import Mathlib
import LeanFlocq.AnyK3D

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## C1: mask relations and monotonicity -/

/-- The relation determined by an 84-bit mask (bit `i` = equation `i`
held). Aligned with `relOfHeld` via `profileMask` (bridge-side lemma). -/
def relOfMask (m : ℕ) : Rel := fun ax o1 o2 => m.testBit (teq ax o1 o2).val

/-- Bitwise mask inclusion. -/
def maskLe (m m' : ℕ) : Prop := ∀ j, m.testBit j = true → m'.testBit j = true

theorem maskLe_refl (m : ℕ) : maskLe m m := fun _ h => h

/-- Bitwise `or`-absorption gives mask inclusion (the census coverage
statement is phrased this way). -/
theorem maskLe_of_or_eq {m m' : ℕ} (h : m ||| m' = m') : maskLe m m' := by
  intro j hj
  have hbit : (m ||| m').testBit j = m'.testBit j := by rw [h]
  rw [Nat.testBit_or, hj, Bool.true_or] at hbit
  exact hbit.symm

theorem relOfMask_mono {m m' : ℕ} (h : maskLe m m') :
    ∀ ax o1 o2, relOfMask m ax o1 o2 = true → relOfMask m' ax o1 o2 = true :=
  fun _ _ _ ht => h _ ht

/-- Tilings transport upward: a bigger mask allows more pairs. -/
theorem tiling_mono {m m' : ℕ} {ω : ℤ × ℤ × ℤ → Fin 24}
    (h : maskLe m m') (ht : IsTiling (relOfMask m) ω) :
    IsTiling (relOfMask m') ω := fun p =>
  ⟨relOfMask_mono h _ _ _ (ht p).1,
   relOfMask_mono h _ _ _ (ht p).2.1,
   relOfMask_mono h _ _ _ (ht p).2.2⟩

/-- A relation tiles ℤ³ fully periodically (three axis periods). This is
`PeriodicallyTiles` generalized from `compat K d` to an arbitrary
relation. -/
def PeriodicRel (R : Rel) : Prop :=
  ∃ ω, IsTiling R ω ∧ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1 + a, p.2.1, p.2.2) = ω p) ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1, p.2.1 + b, p.2.2) = ω p) ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1, p.2.1, p.2.2 + c) = ω p)

theorem periodicallyTiles_iff (K : ℕ) (d : Dec K) :
    PeriodicallyTiles K d ↔ PeriodicRel (compat K d) := Iff.rfl

/-- Periodic tilings transport upward too. -/
theorem periodic_mono {m m' : ℕ} (h : maskLe m m')
    (hp : PeriodicRel (relOfMask m)) : PeriodicRel (relOfMask m') := by
  obtain ⟨ω, hω, a, b, c, ha, hb, hc, pa, pb, pc⟩ := hp
  exact ⟨ω, tiling_mono h hω, a, b, c, ha, hb, hc, pa, pb, pc⟩

/-! ## C3 prelude: box validity and restriction -/

/-- A valid w×h×d box tiling (free boundary, interior adjacencies only,
all three axes). -/
def Box3OK (R : Rel) {w h dp : ℕ} (f : Fin w → Fin h → Fin dp → Fin 24) :
    Prop :=
  (∀ (x : Fin w) (y : Fin h) (z : Fin dp) (hx : x.val + 1 < w),
      R 0 (f x y z) (f ⟨x.val + 1, hx⟩ y z) = true) ∧
  (∀ (x : Fin w) (y : Fin h) (z : Fin dp) (hy : y.val + 1 < h),
      R 1 (f x y z) (f x ⟨y.val + 1, hy⟩ z) = true) ∧
  (∀ (x : Fin w) (y : Fin h) (z : Fin dp) (hz : z.val + 1 < dp),
      R 2 (f x y z) (f x y ⟨z.val + 1, hz⟩) = true)

instance (R : Rel) (w h dp : ℕ) (f : Fin w → Fin h → Fin dp → Fin 24) :
    Decidable (Box3OK R f) := by
  unfold Box3OK; infer_instance

/-- Restriction: a space tiling yields a valid box tiling of every
size. -/
theorem box3OK_of_tiling {R : Rel} {ω : ℤ × ℤ × ℤ → Fin 24}
    (hω : IsTiling R ω) (w h dp : ℕ) :
    Box3OK R (fun (x : Fin w) (y : Fin h) (z : Fin dp) =>
      ω (x.val, y.val, z.val)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z hx
    have H := (hω ((x.val : ℤ), (y.val : ℤ), (z.val : ℤ))).1
    have : ((x.val : ℤ) + 1) = ((x.val + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [this] at H
  · intro x y z hy
    have H := (hω ((x.val : ℤ), (y.val : ℤ), (z.val : ℤ))).2.1
    have : ((y.val : ℤ) + 1) = ((y.val + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [this] at H
  · intro x y z hz
    have H := (hω ((x.val : ℤ), (y.val : ℤ), (z.val : ℤ))).2.2
    have : ((z.val : ℤ) + 1) = ((z.val + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [this] at H

/-! ## C2: rectangular-torus certificates -/

/-- Orientation at torus cell (x, y, z): base-24 digit at position
(x·b + y)·c + z (z-fastest, matching the Python cert export). -/
def gLet3 (grid b c x y z : ℕ) : Fin 24 :=
  ⟨grid / 24 ^ ((x * b + y) * c + z) % 24, Nat.mod_lt _ (by norm_num)⟩

/-- Check an a×b×c torus tiling: all wrapped adjacencies allowed, on all
three axes. -/
def rect3OK (R : Rel) (a b c grid : ℕ) : Bool :=
  decide (0 < a) && decide (0 < b) && decide (0 < c) &&
  ((List.range a).all fun x => (List.range b).all fun y =>
    (List.range c).all fun z =>
      R 0 (gLet3 grid b c x y z) (gLet3 grid b c ((x + 1) % a) y z) &&
      R 1 (gLet3 grid b c x y z) (gLet3 grid b c x ((y + 1) % b) z) &&
      R 2 (gLet3 grid b c x y z) (gLet3 grid b c x y ((z + 1) % c)))

-- The two emod bridges, restated from AnyK2D.lean (kept local to avoid a
-- cross-namespace import for two lemmas).
theorem emod_lt' (x : ℤ) (a : ℕ) (ha : 0 < a) : (x % (a : ℤ)).toNat < a := by
  have h0 : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have h1 := Int.emod_nonneg x (ne_of_gt h0)
  have h2 := Int.emod_lt_of_pos x h0
  omega

theorem emod_shift_nat (x : ℤ) (a : ℕ) (ha : 0 < a) :
    ((x + 1) % (a : ℤ)).toNat = ((x % (a : ℤ)).toNat + 1) % a := by
  have h0 : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have h1 := Int.emod_nonneg x (ne_of_gt h0)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x % (a : ℤ) = (n : ℤ) :=
    ⟨(x % (a : ℤ)).toNat, (Int.toNat_of_nonneg h1).symm⟩
  have : (x + 1) % (a : ℤ) = ((n + 1 : ℕ) : ℤ) % ((a : ℕ) : ℤ) := by
    push_cast
    rw [Int.add_emod, hn, Int.add_emod (n : ℤ) 1, ← hn,
        Int.emod_emod_of_dvd _ dvd_rfl]
  rw [this, ← Int.natCast_mod, Int.toNat_natCast, hn, Int.toNat_natCast]

/-- A verified torus certificate yields a fully periodic space tiling. -/
theorem rect3_sound {R : Rel} {a b c grid : ℕ}
    (h : rect3OK R a b c grid = true) : PeriodicRel R := by
  simp only [rect3OK, Bool.and_eq_true, decide_eq_true_eq,
             List.all_eq_true] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hall⟩ := h
  refine ⟨fun p =>
    gLet3 grid b c (p.1 % (a : ℤ)).toNat (p.2.1 % (b : ℤ)).toNat
      (p.2.2 % (c : ℤ)).toNat, ?_, a, b, c, ha, hb, hc, ?_, ?_, ?_⟩
  · intro p
    have hx := emod_lt' p.1 a ha
    have hy := emod_lt' p.2.1 b hb
    have hz := emod_lt' p.2.2 c hc
    have H := hall _ (List.mem_range.mpr hx) _ (List.mem_range.mpr hy)
      _ (List.mem_range.mpr hz)
    have e1 : ((p.1 + 1) % (a : ℤ)).toNat =
        ((p.1 % (a : ℤ)).toNat + 1) % a := emod_shift_nat p.1 a ha
    have e2 : ((p.2.1 + 1) % (b : ℤ)).toNat =
        ((p.2.1 % (b : ℤ)).toNat + 1) % b := emod_shift_nat p.2.1 b hb
    have e3 : ((p.2.2 + 1) % (c : ℤ)).toNat =
        ((p.2.2 % (c : ℤ)).toNat + 1) % c := emod_shift_nat p.2.2 c hc
    dsimp only
    rw [e1, e2, e3]
    exact ⟨H.1.1, H.1.2, H.2⟩
  · intro p
    have : (p.1 + (a : ℤ)) % (a : ℤ) = p.1 % (a : ℤ) :=
      Int.add_emod_right _ _
    simp [this]
  · intro p
    have : (p.2.1 + (b : ℤ)) % (b : ℤ) = p.2.1 % (b : ℤ) :=
      Int.add_emod_right _ _
    simp [this]
  · intro p
    have : (p.2.2 + (c : ℤ)) % (c : ℤ) = p.2.2 % (c : ℤ) :=
      Int.add_emod_right _ _
    simp [this]

/-! ## Bit-fold helpers (shared with the transport layer)

Local copies of the bridge's generic or-accumulation fold lemmas, with
distinct names to keep this file's import graph shallow; dedup against
`AnyK3DBridge.lean` is a deliberate later cleanup. -/

/-- Bits of a fold that or-in `1 <<< f x` for each `x` passing `c`. -/
theorem testBit_foldl_or_bits {α : Type*} (f : α → ℕ) (c : α → Bool)
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

/-- Or-accumulation over bit positions below `B` stays below `2^B`. -/
theorem foldl_or_pow_lt (c : ℕ → Bool) (B : ℕ) :
    ∀ (l : List ℕ), (∀ n ∈ l, n < B) → ∀ acc : ℕ, acc < 2 ^ B →
      l.foldl (fun a n => if c n then a ||| (1 <<< n) else a) acc < 2 ^ B
  | [], _, acc, hacc => hacc
  | n :: ns, hl, acc, hacc => by
    simp only [List.foldl_cons]
    apply foldl_or_pow_lt c B ns (fun m hm => hl m (List.mem_cons_of_mem _ hm))
    by_cases hc : c n
    · simp only [hc, if_pos]
      have h1 : (1 <<< n) < 2 ^ B := by
        rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by norm_num)
          (hl n (List.mem_cons_self ..))
      exact Nat.or_lt_two_pow hacc h1
    · simpa [hc]

end AnyK3D
