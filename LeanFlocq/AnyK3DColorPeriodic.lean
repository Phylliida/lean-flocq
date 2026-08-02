/-
Periodic torus witnesses for color profiles: checker + soundness.

A witness is a plain rectangular torus: dimensions `(d1, d2, d3)` and an
orientation grid of `d1·d2·d3` cells such that every cell/axis
compatibility holds with wraparound. `torusOK` checks the witness
against a profile's relation; `torusOK_sound` lifts it to a fully
periodic ℤ³ tiling of the orientation SFT (`PeriodicRelTiles`).

Skew-lattice witnesses from the campaign are rectangularized at export
time (`color_periodic_export.py` computes diagonal periods and expands),
so no lattice machinery is needed kernel-side.
-/

import LeanFlocq.AnyK3DDensityCheck

namespace AnyK3D

open ColorDensity

/-- A relation with a fully periodic tiling of ℤ³. -/
def PeriodicRelTiles (R : Rel) : Prop :=
  ∃ ω, IsTiling R ω ∧ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1 + a, p.2.1, p.2.2) = ω p) ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1, p.2.1 + b, p.2.2) = ω p) ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1, p.2.1, p.2.2 + c) = ω p)

/-- Orientation index as `Fin 24` (wrapping; the checker also validates
`< 24` separately). -/
def f24 (n : Nat) : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by norm_num)⟩

/-- Cell index in the row-major `(d1, d2, d3)` grid. -/
def cellIdx (d2 d3 x y z : Nat) : Nat := (x * d2 + y) * d3 + z

/-- The three axis-compatibilities of one torus cell. -/
def cellOK (held : Fin 84 → Bool) (d1 d2 d3 : Nat) (grid : Array Nat)
    (x y z : Nat) : Bool :=
  let o1 := f24 (grid.getD (cellIdx d2 d3 x y z) 0)
  relOfHeld held 0 o1
    (f24 (grid.getD (cellIdx d2 d3 ((x + 1) % d1) y z) 0)) &&
  (relOfHeld held 1 o1
    (f24 (grid.getD (cellIdx d2 d3 x ((y + 1) % d2) z) 0)) &&
  relOfHeld held 2 o1
    (f24 (grid.getD (cellIdx d2 d3 x y ((z + 1) % d3)) 0)))

/-- Rectangular torus witness checker. -/
def torusOK (held : Fin 84 → Bool) (d1 d2 d3 : Nat) (grid : Array Nat) :
    Bool :=
  decide (0 < d1 ∧ 0 < d2 ∧ 0 < d3 ∧ grid.size = d1 * d2 * d3 ∧
    (∀ o ∈ grid.toList, o < 24) ∧
    (∀ x ∈ List.range d1, ∀ y ∈ List.range d2, ∀ z ∈ List.range d3,
      cellOK held d1 d2 d3 grid x y z = true))

/-! ## Extraction from `torusOK = true` -/

theorem torusOK_size_pos {held : Fin 84 → Bool} {d1 d2 d3 : Nat} {grid : Array Nat}
    (h : torusOK held d1 d2 d3 grid = true) :
    0 < d1 ∧ 0 < d2 ∧ 0 < d3 := by
  rw [torusOK, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem torusOK_size {held : Fin 84 → Bool} {d1 d2 d3 : Nat} {grid : Array Nat}
    (h : torusOK held d1 d2 d3 grid = true) :
    grid.size = d1 * d2 * d3 := by
  rw [torusOK, decide_eq_true_eq] at h
  exact h.2.2.2.1

theorem torusOK_cell {held : Fin 84 → Bool} {d1 d2 d3 : Nat} {grid : Array Nat}
    (h : torusOK held d1 d2 d3 grid = true)
    {x y z : Nat} (hx : x < d1) (hy : y < d2) (hz : z < d3) :
    relOfHeld held 0 (f24 (grid.getD (cellIdx d2 d3 x y z) 0))
        (f24 (grid.getD (cellIdx d2 d3 ((x + 1) % d1) y z) 0)) = true ∧
    relOfHeld held 1 (f24 (grid.getD (cellIdx d2 d3 x y z) 0))
        (f24 (grid.getD (cellIdx d2 d3 x ((y + 1) % d2) z) 0)) = true ∧
    relOfHeld held 2 (f24 (grid.getD (cellIdx d2 d3 x y z) 0))
        (f24 (grid.getD (cellIdx d2 d3 x y ((z + 1) % d3)) 0)) = true := by
  rw [torusOK, decide_eq_true_eq] at h
  have hc := h.2.2.2.2.2 x (List.mem_range.mpr hx)
    y (List.mem_range.mpr hy) z (List.mem_range.mpr hz)
  unfold cellOK at hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  exact hc

/-! ## Soundness -/

/-- The periodic orientation field built from a torus witness. -/
noncomputable def periodicOfTorus (grid : Array Nat) (d1 d2 d3 : Nat) :
    ℤ × ℤ × ℤ → Fin 24 :=
  fun p => f24 (grid.getD
    (cellIdx d2 d3 (p.1 % (d1 : ℤ)).toNat (p.2.1 % (d2 : ℤ)).toNat
      (p.2.2 % (d3 : ℤ)).toNat) 0)

/-- Coordinate step: the `(p+1) % d` cell coordinate is the checker's
wraparound neighbor. -/
theorem emod_succ_toNat (p : ℤ) {d : ℕ} (hd : 0 < d) :
    ((p + 1) % (d : ℤ)).toNat = ((p % (d : ℤ)).toNat + 1) % d := by
  have hnn : 0 ≤ p % (d : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hd.ne')
  have hstep : (p + 1) % (d : ℤ) = ((p % (d : ℤ)) + 1) % (d : ℤ) := by
    rw [Int.add_emod]
    conv_rhs => rw [Int.add_emod ((p % (d : ℤ))) 1, Int.emod_emod]
  rw [hstep]
  have hx : (p % (d : ℤ)) = ((p % (d : ℤ)).toNat : ℤ) :=
    (Int.toNat_of_nonneg hnn).symm
  conv_lhs => rw [hx, ← Nat.cast_add_one, ← Int.natCast_emod, Int.toNat_natCast]

/-- Adding a period does not change the cell. -/
theorem emod_add_period (p : ℤ) (d : ℕ) :
    (p + (d : ℤ)) % (d : ℤ) = p % (d : ℤ) := by
  rw [show (p + (d : ℤ)) = p + (d : ℤ) * 1 by ring]
  exact Int.add_mul_emod_self_left _ _ _

theorem periodicOfTorus_period (grid : Array Nat) (d1 d2 d3 : ℕ) :
    (∀ p : ℤ × ℤ × ℤ,
      periodicOfTorus grid d1 d2 d3 (p.1 + d1, p.2.1, p.2.2)
        = periodicOfTorus grid d1 d2 d3 p) ∧
    (∀ p : ℤ × ℤ × ℤ,
      periodicOfTorus grid d1 d2 d3 (p.1, p.2.1 + d2, p.2.2)
        = periodicOfTorus grid d1 d2 d3 p) ∧
    (∀ p : ℤ × ℤ × ℤ,
      periodicOfTorus grid d1 d2 d3 (p.1, p.2.1, p.2.2 + d3)
        = periodicOfTorus grid d1 d2 d3 p) := by
  refine ⟨fun p => ?_, fun p => ?_, fun p => ?_⟩
  · show f24 (grid.getD (cellIdx d2 d3 ((p.1 + (d1:ℤ)) % (d1:ℤ)).toNat _ _) 0)
      = f24 (grid.getD (cellIdx d2 d3 (p.1 % (d1:ℤ)).toNat _ _) 0)
    rw [emod_add_period]
  · show f24 (grid.getD (cellIdx d2 d3 _ ((p.2.1 + (d2:ℤ)) % (d2:ℤ)).toNat _) 0)
      = f24 (grid.getD (cellIdx d2 d3 _ (p.2.1 % (d2:ℤ)).toNat _) 0)
    rw [emod_add_period]
  · show f24 (grid.getD (cellIdx d2 d3 _ _ ((p.2.2 + (d3:ℤ)) % (d3:ℤ)).toNat) 0)
      = f24 (grid.getD (cellIdx d2 d3 _ _ (p.2.2 % (d3:ℤ)).toNat) 0)
    rw [emod_add_period]

/-- A verified torus witness gives a fully periodic ℤ³ tiling. -/
theorem torusOK_sound (held : Fin 84 → Bool) {d1 d2 d3 : Nat} {grid : Array Nat}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (h : torusOK held d1 d2 d3 grid = true) :
    PeriodicRelTiles (relOfHeld held) := by
  refine ⟨periodicOfTorus grid d1 d2 d3, ?_, d1, d2, d3, hd1, hd2, hd3,
    (periodicOfTorus_period grid d1 d2 d3).1,
    (periodicOfTorus_period grid d1 d2 d3).2.1,
    (periodicOfTorus_period grid d1 d2 d3).2.2⟩
  intro p
  have hd1' : (d1 : ℤ) ≠ 0 := by exact_mod_cast hd1.ne'
  have hd2' : (d2 : ℤ) ≠ 0 := by exact_mod_cast hd2.ne'
  have hd3' : (d3 : ℤ) ≠ 0 := by exact_mod_cast hd3.ne'
  have hnn1 : 0 ≤ p.1 % (d1 : ℤ) := Int.emod_nonneg _ hd1'
  have hnn2 : 0 ≤ p.2.1 % (d2 : ℤ) := Int.emod_nonneg _ hd2'
  have hnn3 : 0 ≤ p.2.2 % (d3 : ℤ) := Int.emod_nonneg _ hd3'
  have hlt1 : (p.1 % (d1 : ℤ)).toNat < d1 := by
    have h1 : p.1 % (d1 : ℤ) < (d1 : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hd1)
    exact (Int.toNat_lt hnn1).mpr h1
  have hlt2 : (p.2.1 % (d2 : ℤ)).toNat < d2 := by
    have h1 : p.2.1 % (d2 : ℤ) < (d2 : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hd2)
    exact (Int.toNat_lt hnn2).mpr h1
  have hlt3 : (p.2.2 % (d3 : ℤ)).toNat < d3 := by
    have h1 : p.2.2 % (d3 : ℤ) < (d3 : ℤ) :=
      Int.emod_lt_of_pos _ (by exact_mod_cast hd3)
    exact (Int.toNat_lt hnn3).mpr h1
  obtain ⟨hc0, hc1, hc2⟩ := torusOK_cell h hlt1 hlt2 hlt3
  refine ⟨?_, ?_, ?_⟩
  · show relOfHeld held 0 (periodicOfTorus grid d1 d2 d3 p)
      (periodicOfTorus grid d1 d2 d3 (p.1 + 1, p.2.1, p.2.2)) = true
    unfold periodicOfTorus
    rw [emod_succ_toNat _ hd1]
    exact hc0
  · show relOfHeld held 1 (periodicOfTorus grid d1 d2 d3 p)
      (periodicOfTorus grid d1 d2 d3 (p.1, p.2.1 + 1, p.2.2)) = true
    unfold periodicOfTorus
    rw [emod_succ_toNat _ hd2]
    exact hc1
  · show relOfHeld held 2 (periodicOfTorus grid d1 d2 d3 p)
      (periodicOfTorus grid d1 d2 d3 (p.1, p.2.1, p.2.2 + 1)) = true
    unfold periodicOfTorus
    rw [emod_succ_toNat _ hd3]
    exact hc2

end AnyK3D
