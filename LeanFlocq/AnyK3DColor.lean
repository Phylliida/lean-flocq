/-
# Equal-color Wang cubes, any K, palette T — M1 analogue: geometry +
factorization

The color track of `AnyK3D.lean`. A (T,K)-decoration is a cube whose 6
faces carry K×K grids of palette-T colors (`CDec T K = Fin 6 → Fin K →
Fin K → Fin T`); matching is patterns IDENTICAL through the twist (the
bump/dent track used complement). The 84 equations, the triple tables,
and the whole SFT layer (`IsTiling`, `relOfHeld`, `relOfMask`) are shared
with the bump/dent track — only the matching rule changes.

  * `ceqHolds d g h τ` (F_g = F_h ∘ τ) and the twisted symmetry lemma;
  * `ccompat` via the shared per-triple tables (`AnyK3DGeom.lean`);
  * the K-vanishing factorization `ccompat_factors`: ccompat is
    determined by the 84-bit equation profile `cheldOf` — the same
    `tables_norm` data-level check plus the K-generic symmetry lemma;
  * the SFT layer restated for color: `CTiles`, `CPeriodicallyTiles`.
-/
import Mathlib
import LeanFlocq.AnyK3D

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## Decorations and face equations -/

/-- A (T,K)-decoration: 6 faces, each a K×K grid of palette-T colors. -/
abbrev CDec (T K : ℕ) := Fin 6 → Fin K → Fin K → Fin T

/-- Face equation `F_g = F_h ∘ τ`: the two face grids are IDENTICAL
through the twist (equal-color matching). -/
def ceqHolds (T K : ℕ) (d : CDec T K) (g h : Fin 6) (c : Fin 8) : Bool :=
  decide (∀ p : Fin K × Fin K,
    d g p.1 p.2 = d h (tauApply c p).1 (tauApply c p).2)

theorem ceqHolds_symm (T K : ℕ) (d : CDec T K) (g h : Fin 6) (c : Fin 8) :
    ceqHolds T K d g h c = ceqHolds T K d h g (tauInv c) := by
  simp only [ceqHolds, decide_eq_decide]
  constructor
  · intro H p
    have h1 := H (tauApply (tauInv c) p)
    rw [tau_right_inv] at h1
    exact h1.symm
  · intro H p
    have h1 := H (tauApply c p)
    rw [tau_left_inv] at h1
    exact h1.symm

/-! ## The relation, via the shared triple tables -/

/-- The induced compatibility relation (same honest geometry; only the
matching rule differs). -/
def ccompat (T K : ℕ) (d : CDec T K) : Rel := fun ax o1 o2 =>
  ceqHolds T K d (tfa (tIdx ax o1 o2)) (tfb (tIdx ax o1 o2))
    (tta (tIdx ax o1 o2))

/-- The 84-bit equation profile of a color decoration. -/
def cheldOf (T K : ℕ) (d : CDec T K) : Fin 84 → Bool := fun i =>
  ceqHolds T K d (efa i) (efb i) (eta i)

/-- KEY FACT (K vanishes): ccompat is determined by the equation
profile. -/
theorem ccompat_factors (T K : ℕ) (d : CDec T K) :
    ccompat T K d = relOfHeld (cheldOf T K d) := by
  funext ax o1 o2
  rcases tables_norm ax o1 o2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · simp only [ccompat, relOfHeld, cheldOf, h1, h2, h3]
  · simp only [ccompat, relOfHeld, cheldOf, h1, h2, h3]
    rw [ceqHolds_symm, tauInv_tauInv]

/-! ## The SFT layer -/

/-- The color decoration tiles ℤ³ (by its rotation orbit). -/
def CTiles (T K : ℕ) (d : CDec T K) : Prop :=
  ∃ ω, IsTiling (ccompat T K d) ω

/-- The color decoration tiles ℤ³ fully periodically (three axis
periods). -/
def CPeriodicallyTiles (T K : ℕ) (d : CDec T K) : Prop :=
  ∃ ω, IsTiling (ccompat T K d) ω ∧ ∃ a b c : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1 + a, p.2.1, p.2.2) = ω p) ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1, p.2.1 + b, p.2.2) = ω p) ∧
    (∀ p : ℤ × ℤ × ℤ, ω (p.1, p.2.1, p.2.2 + c) = ω p)

end AnyK3D
