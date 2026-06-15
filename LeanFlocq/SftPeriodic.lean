/-
The load-bearing combinatorial atom of the monotile arena-2 closure
machinery (standalone leaf module; imports only Mathlib).

**Lemma.** Every nonempty one-dimensional nearest-neighbour SFT over a
finite alphabet has a periodic point, with period at most the alphabet
size — and the periodic point's transition pairs all occur as
transition pairs of the original configuration.

The final clause is the *pattern-closure* property: in the Wang-cube
application, the pair-set ("pattern") of a tiling is the union of
point-pair constraints over its realized transitions, so the periodic
point's pattern is contained in the original's. This single lemma
underlies both the Rank-2 Reduction Lemma (rank-2 invariance implies a
fully periodic tiling, via the quotient 1D SFT) and the bounded-
reduction step of the catalogue-completeness programme.

We state it for walks indexed by ℕ; a biinfinite (ℤ-indexed) valid
configuration restricts to such a walk, and the periodic ℕ-walk
extends ℤ-periodically, so this form carries the full content.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

open Nat

theorem periodic_point_of_walk {α : Type*} [Fintype α]
    (R : α → α → Prop) (f : ℕ → α) (hf : ∀ i, R (f i) (f (i + 1))) :
    ∃ (g : ℕ → α) (p : ℕ), 0 < p ∧ p ≤ Fintype.card α ∧
      (∀ i, R (g i) (g (i + 1))) ∧
      (∀ i, g (i + p) = g i) ∧
      (∀ i, ∃ m, g i = f m ∧ g (i + 1) = f (m + 1)) := by
  -- pigeonhole: among f 0, …, f (card α) two indices collide
  obtain ⟨a, b, hab, hfab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (Fintype.card α + 1) => f k)
      (by simp)
  -- order them: i < j, f i = f j
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  case _ =>
    exact build R f hf a.val b.val h hfab
      (by exact Nat.le_of_lt_succ b.isLt)
  case _ =>
    exact build R f hf b.val a.val h hfab.symm
      (by exact Nat.le_of_lt_succ a.isLt)
where
  build (R : α → α → Prop) (f : ℕ → α)
      (hf : ∀ i, R (f i) (f (i + 1))) (i j : ℕ) (hij : i < j)
      (hcol : f i = f j) (hj : j ≤ Fintype.card α) :
      ∃ (g : ℕ → α) (p : ℕ), 0 < p ∧ p ≤ Fintype.card α ∧
        (∀ k, R (g k) (g (k + 1))) ∧
        (∀ k, g (k + p) = g k) ∧
        (∀ k, ∃ m, g k = f m ∧ g (k + 1) = f (m + 1)) := by
    set p := j - i with hp
    have hp0 : 0 < p := Nat.sub_pos_of_lt hij
    refine ⟨fun k => f (i + k % p), p, hp0,
      le_trans (Nat.sub_le _ _) hj, ?_, ?_, ?_⟩
    · -- validity of each transition
      intro k
      have hlt : k % p < p := Nat.mod_lt _ hp0
      have hsucc : (k + 1) % p = (k % p + 1) % p := by
        conv_lhs => rw [← Nat.mod_add_mod]
      by_cases hwrap : k % p + 1 = p
      · -- wrap-around step: lands on f i = f j
        have h0 : (k + 1) % p = 0 := by
          rw [hsucc, hwrap, Nat.mod_self]
        have hk : i + k % p + 1 = j := by omega
        have := hf (i + k % p)
        rw [hk] at this
        simpa [h0, ← hcol] using this
      · -- interior step
        have hlt1 : k % p + 1 < p := lt_of_le_of_ne hlt hwrap
        have h1 : (k + 1) % p = k % p + 1 := by
          rw [hsucc, Nat.mod_eq_of_lt hlt1]
        simpa [h1, ← Nat.add_assoc] using hf (i + k % p)
    · -- periodicity
      intro k
      simp [Nat.add_mod_right]
    · -- pattern closure: each transition is an f-transition pair
      intro k
      have hlt : k % p < p := Nat.mod_lt _ hp0
      have hsucc : (k + 1) % p = (k % p + 1) % p := by
        conv_lhs => rw [← Nat.mod_add_mod]
      by_cases hwrap : k % p + 1 = p
      · refine ⟨i + k % p, rfl, ?_⟩
        have h0 : (k + 1) % p = 0 := by
          rw [hsucc, hwrap, Nat.mod_self]
        have hk : i + k % p + 1 = j := by omega
        show f (i + (k + 1) % p) = f (i + k % p + 1)
        rw [h0, hk, Nat.add_zero, hcol]
      · have hlt1 : k % p + 1 < p := lt_of_le_of_ne hlt hwrap
        have h1 : (k + 1) % p = k % p + 1 := by
          rw [hsucc, Nat.mod_eq_of_lt hlt1]
        refine ⟨i + k % p, rfl, ?_⟩
        show f (i + (k + 1) % p) = f (i + k % p + 1)
        rw [h1, ← Nat.add_assoc]
