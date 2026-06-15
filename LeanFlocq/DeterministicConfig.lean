/-
Abstract half of the Matching Collapse theorem (monotile arena-2
catalogue-completeness programme, Theorem 5(b)).

**Theorem.** Let ω : ℤ³ → α be a configuration over a finite alphabet
driven by deterministic single-step rules along each axis — three
permutations π₁, π₂, π₃ with ω(c + eᵢ) = πᵢ(ω c). Then ω is fully
periodic, with period at most |α| along each axis.

Notably ω is NOT assumed periodic: determinism alone forbids
aperiodicity. In the application, a perfect-matching pattern makes
the compatibility relation deterministic (each interface point has a
unique matched partner, and a cube rotation is determined by its
action on one face — a finite fact, formalizable separately by
`decide` over the concrete tables), so *no decoration realizing a
matching pattern admits any aperiodic tiling*, and witnesses have
index ≤ 24.

No commutativity of the πᵢ is assumed: it holds automatically *on the
range of ω* (both sides compute ω at the same cell), which is all the
proof needs.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.Perm.Basic

open Equiv

variable {α : Type*} [Fintype α]

namespace DetConfig

variable (π₁ π₂ π₃ : Equiv.Perm α) (ω : ℤ → ℤ → ℤ → α)

/-- The three deterministic step laws. -/
structure Steps : Prop where
  hx : ∀ a b c, ω (a + 1) b c = π₁ (ω a b c)
  hy : ∀ a b c, ω a (b + 1) c = π₂ (ω a b c)
  hz : ∀ a b c, ω a b (c + 1) = π₃ (ω a b c)

variable {π₁ π₂ π₃ ω}

omit [Fintype α] in
/-- A permutation power slides past one application of itself. -/
lemma pow_comm_self (σ : Equiv.Perm α) (p : ℕ) (t : α) :
    (σ ^ p) (σ t) = σ ((σ ^ p) t) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, pow_mul_comm']

omit [Fintype α] in
/-- ℕ-fold x-steps. -/
lemma pow_x (h : Steps π₁ π₂ π₃ ω) (k : ℕ) (a b c : ℤ) :
    (π₁ ^ k) (ω a b c) = ω (a + k) b c := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, ← h.hx]
      congr 1
      omega

omit [Fintype α] in
/-- Powers of π₁ commute with π₂ at every range point. -/
lemma comm_pow_y (h : Steps π₁ π₂ π₃ ω) (k : ℕ) (a b c : ℤ) :
    (π₁ ^ k) (π₂ (ω a b c)) = π₂ ((π₁ ^ k) (ω a b c)) := by
  rw [← h.hy, pow_x h, pow_x h, h.hy]

omit [Fintype α] in
/-- Powers of π₁ commute with π₃ at every range point. -/
lemma comm_pow_z (h : Steps π₁ π₂ π₃ ω) (k : ℕ) (a b c : ℤ) :
    (π₁ ^ k) (π₃ (ω a b c)) = π₃ ((π₁ ^ k) (ω a b c)) := by
  rw [← h.hz, pow_x h, pow_x h, h.hz]

omit [Fintype α] in
/-- If π₁ᵖ fixes the seed ω 0 0 0, it fixes every value of ω. -/
lemma fix_propagates (h : Steps π₁ π₂ π₃ ω) (p : ℕ)
    (hseed : (π₁ ^ p) (ω 0 0 0) = ω 0 0 0) :
    ∀ a b c, (π₁ ^ p) (ω a b c) = ω a b c := by
  have hz' : ∀ c : ℤ, (π₁ ^ p) (ω 0 0 c) = ω 0 0 c := by
    intro c
    induction c using Int.induction_on with
    | zero => exact hseed
    | succ n ih => rw [h.hz, comm_pow_z h, ih]
    | pred n ih =>
        have step : π₃ (ω 0 0 (-(n : ℤ) - 1)) = ω 0 0 (-(n : ℤ)) := by
          have e := h.hz 0 0 (-(n : ℤ) - 1)
          rw [show (-(n : ℤ) - 1 + 1) = -(n : ℤ) by omega] at e
          exact e.symm
        apply (π₃ : Equiv.Perm α).injective
        rw [← comm_pow_z h p 0 0 (-(n : ℤ) - 1), step, ih]
  have hy' : ∀ b c : ℤ, (π₁ ^ p) (ω 0 b c) = ω 0 b c := by
    intro b c
    induction b using Int.induction_on with
    | zero => exact hz' c
    | succ n ih => rw [h.hy, comm_pow_y h, ih]
    | pred n ih =>
        have step : π₂ (ω 0 (-(n : ℤ) - 1) c) = ω 0 (-(n : ℤ)) c := by
          have e := h.hy 0 (-(n : ℤ) - 1) c
          rw [show (-(n : ℤ) - 1 + 1) = -(n : ℤ) by omega] at e
          exact e.symm
        apply (π₂ : Equiv.Perm α).injective
        rw [← comm_pow_y h p 0 (-(n : ℤ) - 1) c, step, ih]
  intro a b c
  induction a using Int.induction_on with
  | zero => exact hy' b c
  | succ n ih => rw [h.hx, pow_comm_self, ih]
  | pred n ih =>
      have step : π₁ (ω (-(n : ℤ) - 1) b c) = ω (-(n : ℤ)) b c := by
        have e := h.hx (-(n : ℤ) - 1) b c
        rw [show (-(n : ℤ) - 1 + 1) = -(n : ℤ) by omega] at e
        exact e.symm
      apply (π₁ : Equiv.Perm α).injective
      rw [← pow_comm_self π₁ p (ω (-(n : ℤ) - 1) b c), step, ih]

/-- **Forced periodicity along x**: some 0 < p ≤ |α| is a period. -/
theorem periodic_x (h : Steps π₁ π₂ π₃ ω) :
    ∃ p : ℕ, 0 < p ∧ p ≤ Fintype.card α ∧
      ∀ a b c, ω (a + p) b c = ω a b c := by
  obtain ⟨m, m', hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card α + 1) => (π₁ ^ (n : ℕ)) (ω 0 0 0))
      (by simp)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  case _ =>
    exact build h m.val m'.val hlt heq (Nat.le_of_lt_succ m'.isLt)
  case _ =>
    exact build h m'.val m.val hlt heq.symm (Nat.le_of_lt_succ m.isLt)
where
  build (h : Steps π₁ π₂ π₃ ω) (m m' : ℕ) (hlt : m < m')
      (heq : (π₁ ^ m) (ω 0 0 0) = (π₁ ^ m') (ω 0 0 0))
      (hm' : m' ≤ Fintype.card α) :
      ∃ p : ℕ, 0 < p ∧ p ≤ Fintype.card α ∧
        ∀ a b c, ω (a + p) b c = ω a b c := by
    refine ⟨m' - m, Nat.sub_pos_of_lt hlt,
      le_trans (Nat.sub_le _ _) hm', ?_⟩
    have hseed : (π₁ ^ (m' - m)) (ω 0 0 0) = ω 0 0 0 := by
      apply (π₁ ^ m : Equiv.Perm α).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add,
          Nat.add_sub_cancel' (le_of_lt hlt), ← heq]
    intro a b c
    rw [← pow_x h, fix_propagates h _ hseed]

end DetConfig
