/-
# Color M5: assembly — no aperiodic equal-color Wang cube, any K, any palette

The capstone of the color track (the analogue of `AnyK3DMain.lean`):

    theorem no_aperiodic_equal_color_wang_cube (T K : ℕ) (d : CDec T K)
        (h : CTiles T K d) : CPeriodicallyTiles T K d

Chain: `color_census_complete` (color M3b) → `mem_censusFastC_covered`
(the coverage computation) → `colorVerdict_of_mem` → branch:
periodic (`periodic_transport_back`) / empty (`tiling_transport`
forward into the verdict's emptiness). The mask/held correspondence and
the K = 0 / T = 0 edge cases close the geometric ends.

TRUST DEBT (inherited from the color empty tier): the empty branch
rests on `colorFrontierUnsat` (65,250 frontier box CNFs UNSAT, every
LRAT cert re-checked by the CakeML-verified `cake_lpr`) — the same
trust profile as the bump/dent track's `frontierEmptyFacts`. Everything
else is kernel-checked (with `native_decide`'s accepted base).
-/
import LeanFlocq.AnyK3DColorCoverageCheck
import LeanFlocq.AnyK3DColorCoverage

set_option maxRecDepth 1000000

namespace AnyK3D

/-- The mask/held correspondence: the profile mask's relation is the
held-vector's relation (restated locally to keep the color track's
import graph self-contained). -/
theorem relOfMask_profileMaskC (hs : Fin 84 → Bool) :
    relOfMask (profileMask hs) = relOfHeld hs := by
  funext ax o1 o2
  show (profileMask hs).testBit (teq ax o1 o2).val = hs (teq ax o1 o2)
  rw [testBit_profileMask hs (teq ax o1 o2).val (teq _ _ _).isLt]

/-- The profile mask fits in 84 bits (restated locally). -/
theorem profileMask_lt_C (hs : Fin 84 → Bool) : profileMask hs < 2 ^ 84 := by
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

theorem cperiodicallyTiles_iff (T K : ℕ) (d : CDec T K) :
    CPeriodicallyTiles T K d ↔ PeriodicRel (ccompat T K d) := Iff.rfl

/-- **Main theorem (color track).** No equal-color Wang cube — any grid
K, any palette T — is an aperiodic einstein: every equal-color
decoration that tiles ℤ³ admits a fully periodic tiling. -/
theorem no_aperiodic_equal_color_wang_cube (T K : ℕ) (d : CDec T K)
    (h : CTiles T K d) : CPeriodicallyTiles T K d := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · -- K = 0: ccompat is vacuously all-true; constant field, periods (1,1,1)
    refine ⟨fun _ => 0, ?_, 1, 1, 1, by norm_num, by norm_num, by norm_num,
      fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    intro p
    refine ⟨?_, ?_, ?_⟩ <;>
      · show ceqHolds T 0 d _ _ _ = true
        simp only [ceqHolds, decide_eq_true_eq]
        intro q
        exact Fin.elim0 q.1
  · -- K ≥ 1
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · -- T = 0, K ≥ 1: no decoration exists
      exact (d 0 ⟨0, hK⟩ ⟨0, hK⟩).elim0
    · -- T ≥ 1, K ≥ 1
      set m := profileMask (cheldOf T K d) with hm_def
      have hm84 : m < 2 ^ 84 := profileMask_lt_C _
      have hmem := color_census_complete T K d
      obtain ⟨g, hg, hcan⟩ := mem_censusFastC_covered hmem
      have hfac := ccompat_factors T K d
      have hcorr := relOfMask_profileMaskC (cheldOf T K d)
      rcases colorVerdict_of_mem hcan with hper | hemp
      · -- periodic branch: transport the periodic tiling back along the
        -- rotation
        have hpM := periodic_transport_back g hg m hm84 hper
        rw [cperiodicallyTiles_iff, hfac, ← hcorr]
        exact hpM
      · -- empty branch: transport the tiling forward into a
        -- contradiction with the verdict's emptiness
        obtain ⟨ω, hω⟩ := h
        have hω' : IsTiling (relOfMask (permMask g m))
            (fun p => relabelO g hg (ω p)) := by
          apply tiling_transport g hg m ω
          rwa [hfac, ← hcorr] at hω
        exact absurd ⟨_, hω'⟩ hemp

end AnyK3D
