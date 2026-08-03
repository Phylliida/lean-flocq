/-
# Color M2: the gain algebra — color decorations as gain structures

The equal-color analogue of `AnyK3DGain.lean`. The gain group is the 8
grid isometries alone (`Fin 8` — signs stay +1 for equal-color matching),
acting on face-functions by `cact w F = F ∘ τ_w`. Key facts:

  * `ceqHolds_iff_act`: a face equation holds iff the faces are related
    by the corresponding twist gain — the semantic bridge that turns a
    color decoration into a (partition, gains, stabilizer) structure.
  * `cact_cact` / `cact_inv_cact`: the action composes along `cmul` and
    cancels along `cinv` (reusing M2's 64-case `tauComp` computation).
  * `ceqHolds_iff_stab`: for faces expressed through root gains, a held
    equation is exactly a stabilizer-coset membership — the induced
    held-set formula of the color census, realized semantically.

Feasibility note: unlike bump/dent (where the census filters to 18 of 35
subgroups), ALL 10 subgroups of the 8-element color gain group are
realizable as exact stabilizers of 2-color patterns (brute-force
witnesses on K = 2,3,4 grids; `monotile/check_color_subgroups.py`,
missing = 0). The color census therefore enumerates every subgroup, and
the bridge only needs that a realized stabilizer IS a subgroup — pure
algebra, no geometry.
-/
import Mathlib
import LeanFlocq.AnyK3DColor
import LeanFlocq.AnyK3DGain

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## The gain group acting on face-functions -/

/-- Action of a grid isometry on a face-function. -/
def cact (w : Fin 8) {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    Fin K → Fin K → Fin T := fun u v =>
  F (tauApply w (u, v)).1 (tauApply w (u, v)).2

/-- Group law matching the action: `cact a (cact b F) = cact (cmul a b) F`.
Note τ's compose reversed (b's isometry applies first pointwise). -/
def cmul (a b : Fin 8) : Fin 8 := tauComp b a

/-- Inverse: `tauInv` (M1's involution on codes). -/
def cinv (w : Fin 8) : Fin 8 := tauInv w

theorem cact_cact (a b : Fin 8) {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    cact a (cact b F) = cact (cmul a b) F := by
  funext u v
  simp only [cact, cmul]
  rw [← tauApply_comp]

theorem cact_one {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    cact (0 : Fin 8) F = F := by
  funext u v
  simp [cact, tauApply_zero]

theorem cact_inv_cact (w : Fin 8) {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    cact (cinv w) (cact w F) = F := by
  rw [cact_cact]
  simp only [cmul, cinv, tauComp_inv_self]
  exact cact_one F

theorem cact_cact_inv (w : Fin 8) {T K : ℕ} (F : Fin K → Fin K → Fin T) :
    cact w (cact (cinv w) F) = F := by
  rw [cact_cact]
  simp only [cmul, cinv, tauComp_self_inv]
  exact cact_one F

/-! ## The semantic bridge -/

/-- A face equation holds exactly when the faces are related by the
corresponding twist gain. -/
theorem ceqHolds_iff_act (T K : ℕ) (d : CDec T K) (g h : Fin 6)
    (c : Fin 8) :
    ceqHolds T K d g h c = true ↔ d g = cact c (d h) := by
  simp only [ceqHolds, decide_eq_true_eq]
  constructor
  · intro H
    funext u v
    exact H (u, v)
  · intro H p
    exact congrFun (congrFun H p.1) p.2

/-- Stabilizer-coset formula: for faces expressed through root gains, a
held equation is a stabilizer membership of the combined gain. This is
the color census's induced held-set, realized semantically. -/
theorem ceqHolds_iff_stab (T K : ℕ) (d : CDec T K) (g h : Fin 6) (c : Fin 8)
    (F : Fin K → Fin K → Fin T) (wg wh : Fin 8)
    (hg : d g = cact wg F) (hh : d h = cact wh F) :
    ceqHolds T K d g h c = true ↔
      cact (cmul (cinv wg) (cmul c wh)) F = F := by
  rw [ceqHolds_iff_act, hg, hh, cact_cact]
  constructor
  · intro H
    rw [← cact_cact, ← H]
    exact cact_inv_cact wg F
  · intro H
    rw [← cact_cact] at H
    have h2 := congrArg (cact wg) H
    rw [cact_cact_inv] at h2
    exact h2.symm

end AnyK3D
