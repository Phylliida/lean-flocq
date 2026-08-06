/-
# M5: assembly — no aperiodic Wang cube at any K

The capstone (DESIGN-anyk3d-endgame.md §3):

    theorem no_aperiodic_wang_cube_anyK (K : ℕ) (d : Dec K)
        (h : Tiles K d) : PeriodicallyTiles K d

Chain: census_complete (M3b) → census_covered (M4-C4) → branch:
periodic (C2 cert + mono + transport-back) / empty (transport-forward +
C3 emptiness). The mask/held correspondence and the K = 0 case close
the geometric ends.

TRUST DEBT (being discharged): `frontierEmptyFacts` below is the
emptiness of the 3,405 maximal-empty frontier masks. Status:
  * the 34 stragglers (empty4/5/6): PROVEN — cube-and-conquer trees,
    per-leaf LRAT re-checked by cake_lpr (AnyK3DStragTrees.lean);
  * the 3,371 cheap masks (empty3): cake_lpr streaming (K=3 profile).
    Route change vs plan: in-Lean `verifyCert` probed 2026-07-20 is NOT
    viable (>4M heartbeats / >10 min for ONE 43KB cert). This axiom
    therefore STAYS as the trust surface, matching the K=3
    ConcreteTree profile: solver untrusted; every certificate
    re-checked by the CakeML-verified checker.
  * UNIFIED EVIDENCE (2026-08-06, R6): all 3,371 cheap CNFs +
    all 387 straggler leaves re-exported from the current proven
    encoder (ExportEmptyCNF; the historical cheap CNFs were
    byte-identical, the straggler bases matched up to clause order)
    and re-verified through the R2 color pipeline — cadical --lrat →
    cake_lpr, certs deleted after each check. Ledger:
    monotile/bumpdent_frontier_verified.txt (3,371 + 387, 0 failures;
    gen_bumpdent_certs.py).
-/
import Mathlib
import LeanFlocq.AnyK3DComplete
import LeanFlocq.AnyK3DCoverage
import LeanFlocq.AnyK3DPeriodicValid
import LeanFlocq.AnyK3DEmptyEnc

set_option maxRecDepth 100000

namespace AnyK3D

/-- The mask/held correspondence: the profile mask's relation is the
held-vector's relation. -/
theorem relOfMask_profileMask (hs : Fin 84 → Bool) :
    relOfMask (profileMask hs) = relOfHeld hs := by
  funext ax o1 o2
  show (profileMask hs).testBit (teq ax o1 o2).val = hs (teq ax o1 o2)
  rw [testBit_profileMask hs (teq ax o1 o2).val (teq _ _ _).isLt]

/-- The profile mask fits in 84 bits. -/
theorem profileMask_lt (hs : Fin 84 → Bool) : profileMask hs < 2 ^ 84 := by
  have gen : ∀ (l : List (Fin 84)), ∀ acc : ℕ, acc < 2 ^ 84 →
      (l.foldl (fun acc i => if hs i then acc ||| (1 <<< i.val) else acc)
        acc) < 2 ^ 84 := by
    intro l
    induction l with
    | nil => intro acc hacc; exact hacc
    | cons i is ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      split
      · have h1 : (1 <<< i.val) < 2 ^ 84 := by
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_right (by norm_num) i.isLt
        exact Nat.or_lt_two_pow hacc h1
      · exact hacc
  unfold profileMask
  exact gen (List.finRange 84) 0 (by norm_num)

/-- **TRUST DEBT** — see file header. The maximal-empty frontier masks
have no space tiling. -/
axiom frontierEmptyFacts (e : ℕ) (he : e ∈ maxEmpty.toList) :
    ¬ ∃ ω, IsTiling (relOfMask e) ω

/-- **Main theorem.** No bump-and-dent cube, at any resolution K, is an
aperiodic einstein: every K-decoration that tiles ℤ³ admits a fully
periodic tiling. -/
theorem no_aperiodic_wang_cube_anyK (K : ℕ) (d : Dec K)
    (h : Tiles K d) : PeriodicallyTiles K d := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · -- K = 0: compat is vacuously all-true; constant field, periods (1,1,1)
    refine ⟨fun _ => 0, ?_, 1, 1, 1, by norm_num, by norm_num, by norm_num,
      fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    intro p
    refine ⟨?_, ?_, ?_⟩ <;>
      · show eqHolds 0 d _ _ _ = true
        simp only [eqHolds, decide_eq_true_eq]
        intro q
        exact Fin.elim0 q.1
  · -- K ≥ 1
    set m := profileMask (heldOf K d) with hm_def
    have hm84 : m < 2 ^ 84 := profileMask_lt _
    have hmem := census_complete K hK d
    obtain ⟨g, hg, hbranch⟩ := mem_census_covered hmem
    have hfac := compat_factors K d
    have hcorr := relOfMask_profileMask (heldOf K d)
    rcases hbranch with ⟨q, hqP, hq⟩ | ⟨e, heP, he⟩
    · -- periodic branch: lift the cert up through mask inclusion and
      -- transport back along the rotation
      have hqle : maskLe q (permMask g m) := maskLe_of_or_eq hq
      obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hqP
      have hrect : rect3OK (relOfMask q) (certDims.getD i (0, 0, 0)).1
          (certDims.getD i (0, 0, 0)).2.1 (certDims.getD i (0, 0, 0)).2.2
          (certGrids.getD i 0) = true := by
        have hi' : i < minPeriodic.size := by
          rwa [Array.length_toList] at hi
        have hv := periodic_certs_valid i hi'
        have hget : minPeriodic.getD i 0 = q := by
          rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dif_pos hi']
          exact hqi
        rwa [hget] at hv
      have hpQ := periodic_mono hqle (rect3_sound hrect)
      have hpM := periodic_transport_back g hg m hm84 hpQ
      rw [periodicallyTiles_iff, hfac, ← hcorr]
      exact hpM
    · -- empty branch: transport the tiling forward into a
      -- contradiction with the frontier emptiness
      obtain ⟨ω, hω⟩ := h
      have hele : maskLe (permMask g m) e := maskLe_of_or_eq he
      have hω' : IsTiling (relOfMask (permMask g m))
          (fun p => relabelO g hg (ω p)) := by
        apply tiling_transport g hg m ω
        rwa [hfac, ← hcorr] at hω
      have hω'' := tiling_mono hele hω'
      exact absurd ⟨_, hω''⟩ (frontierEmptyFacts e heP)

end AnyK3D
