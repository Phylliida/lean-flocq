/-
The color empty frontier: TRUST DEBT axiom + inheritance.

**TRUST DEBT (matching `frontierEmptyFacts` in the bump/dent track).**
`colorFrontierUnsat` asserts that the box CNFs of the 65,250
locally-maximal empty color masks are UNSAT. Evidence: every CNF was
exported by Lean's own `ExportEmptyCNF` (the encoder whose correctness
`empty_sound` is proven here), refuted by CaDiCaL, and the LRAT
certificate re-checked by the CakeML-verified `cake_lpr` checker
(`monotile/color_frontier_verified.txt`, 65,250/65,250, 0 failures,
2026-08-03). The SAT solver is untrusted; the checking is external to
Lean's kernel. The in-Lean alternative was measured non-viable
(2026-08-03 probe: stack overflow at default stack; >1 h with a 4 GB
thread stack for ONE 214 KB cert; cake_lpr does it in 0.093 s).

Everything below the axiom is kernel-checked: the 130,808 non-frontier
empty profiles inherit emptiness from their frontier superset via the
batch-`native_decide`'d `maskLe` (`AnyK3DColorEmptyCheck.lean`) and the
proven `tiling_mono`.
-/

import LeanFlocq.AnyK3DEmptyEnc
import LeanFlocq.AnyK3DColorEmptyCheck

set_option maxRecDepth 1000000

namespace AnyK3D

/-- **TRUST DEBT** — see file header. Every frontier job's box CNF is
UNSAT (cake_lpr evidence). -/
axiom colorFrontierUnsat (i : ℕ) (hi : i < frontierSize) :
    Std.Sat.CNF.Unsat (emptyCNF (frontierJob i).1 (frontierJob i).2.1
      (frontierJob i).2.2.1 (frontierJob i).2.2.2)

/-- A frontier mask has no space tiling (axiom + proven `empty_sound`). -/
theorem colorFrontierEmpty (i : ℕ) (hi : i < frontierSize) :
    ¬ ∃ ω, IsTiling (relOfMask (frontierJob i).1) ω := by
  have hpos := (List.all_eq_true.mp colorFrontierJobs_dims_pos) i
    (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpos
  exact empty_sound hpos.1.2 hpos.2 (colorFrontierUnsat i hi)

/-- A non-frontier empty profile has no space tiling (inheritance via
`maskLe` + `tiling_mono`). -/
theorem colorEmpty_of_inheritance (p : ℕ × ℕ) (hp : p ∈ colorInheritance) :
    ¬ ∃ ω, IsTiling (relOfMask p.1) ω := by
  have hv := Array.all_eq_true_iff_forall_mem.mp colorInheritance_valid p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨h84, hlt⟩, hle⟩ := hv
  have hle' := maskLe_of_maskLeB h84 hle
  have hjob := colorFrontierEmpty p.2 hlt
  rintro ⟨ω, hω⟩
  exact hjob ⟨ω, tiling_mono hle' hω⟩

end AnyK3D
