/-
Port of `flocq/src/Core/Round_NE.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Round to nearest, ties to even — IEEE 754's default rounding mode.
Builds on `Znearest` with the choice function "round up at a tie iff
the floor is odd," which produces an even canonical mantissa.
-/

import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.Ulp

namespace LeanFlocq

/-- The round-to-nearest-even integer rounder: at a tie, pick the side that
makes the result even. Concretely, the choice returns `true` (= round up to
ceil) when `⌊x⌋` is odd. -/
noncomputable def ZnearestE : ℝ → ℤ :=
  Znearest (fun n => decide (¬ Even n))

/-- `round_NE β fexp x` is the round-to-nearest-even of `x` in the given format. -/
noncomputable def round_NE (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) : ℝ :=
  round beta fexp ZnearestE x

/-- The "even canonical mantissa" tie-breaking property: `f` is the F2R of a
canonical float whose mantissa is even. -/
def NE_prop (beta : radix) (fexp : ℤ → ℤ) (_x f : ℝ) : Prop :=
  ∃ g : float beta, f = F2R g ∧ canonical beta fexp g ∧ Even g.Fnum

/-- `f` is *the* round-to-nearest-even of `x` in the format `F`: it rounds
to the nearest, and at a tie it picks the even one (or there's no tie at all). -/
def Rnd_NE_pt (beta : radix) (fexp : ℤ → ℤ) (x f : ℝ) : Prop :=
  Rnd_NG_pt (generic_format beta fexp) (NE_prop beta fexp) x f

/-- The round-NE function lands at a `Rnd_N_pt` (without yet checking the
parity tie-breaking). Immediate from `round_N_pt` with the round-up-on-odd-floor
choice. -/
theorem round_NE_pt_N (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp) (x : ℝ) :
    Rnd_N_pt (generic_format beta fexp) x (round_NE beta fexp x) := by
  unfold round_NE ZnearestE
  exact round_N_pt beta fexp hValid _ x

/-! ### `Exists_NE`: the typeclass enabling round-to-nearest-even

The DN_UP parity theorem requires either `β` is odd, or `fexp` "doesn't get
stuck" in any narrow ways: in the small regime it stabilizes at one
exponent, and in the large regime it grows enough that the canonical
mantissa picks up extra factors of `β`. This is captured by `Exists_NE`. -/
class Exists_NE (beta : radix) (fexp : ℤ → ℤ) : Prop where
  cond : Odd beta.val ∨
    ∀ e : ℤ,
      (fexp e < e → fexp (e + 1) < e) ∧
      (e ≤ fexp e → fexp (fexp e + 1) = fexp e)

/-- The DN/UP parity property restricted to positive `x ∉ F`: the canonical
up-rounded mantissa flips parity from the down-rounded one. -/
def DN_UP_parity_pos_prop (beta : radix) (fexp : ℤ → ℤ) : Prop :=
  ∀ (x : ℝ) (xd xu : float beta),
    0 < x → ¬ generic_format beta fexp x →
    canonical beta fexp xd → canonical beta fexp xu →
    F2R xd = round beta fexp (fun y : ℝ => ⌊y⌋) x →
    F2R xu = round beta fexp (fun y : ℝ => ⌈y⌉) x →
    (Even xu.Fnum ↔ ¬ Even xd.Fnum)

/-- The DN/UP parity property for general `x ∉ F`. -/
def DN_UP_parity_prop (beta : radix) (fexp : ℤ → ℤ) : Prop :=
  ∀ (x : ℝ) (xd xu : float beta),
    ¬ generic_format beta fexp x →
    canonical beta fexp xd → canonical beta fexp xu →
    F2R xd = round beta fexp (fun y : ℝ => ⌊y⌋) x →
    F2R xu = round beta fexp (fun y : ℝ => ⌈y⌉) x →
    (Even xu.Fnum ↔ ¬ Even xd.Fnum)

/-- General DN/UP parity reduces to the positive case via opp-symmetry on
canonical floats. -/
theorem DN_UP_parity_aux (beta : radix) (fexp : ℤ → ℤ)
    (Hpos : DN_UP_parity_pos_prop beta fexp) : DN_UP_parity_prop beta fexp := by
  intro x xd xu Hfx Hd Hu Hxd Hxu
  rcases lt_trichotomy 0 x with hx | hx | hx
  · -- 0 < x: direct application.
    exact Hpos x xd xu hx Hfx Hd Hu Hxd Hxu
  · -- x = 0: contradicts ¬ generic_format x.
    exfalso; apply Hfx
    rw [← hx]; exact generic_format_0 beta fexp
  · -- x < 0: apply Hpos at -x with negated mantissas.
    have hx' : 0 < -x := by linarith
    obtain ⟨md, ed⟩ := xd
    obtain ⟨mu, eu⟩ := xu
    -- The canonical of (-md, ed) at (-x): F2R = -F2R xd = round_DN(-x) via round_UP_opp.
    have F_neg_x_n_F : ¬ generic_format beta fexp (-x) := by
      intro h
      apply Hfx
      rw [show x = -(-x) from (neg_neg x).symm]
      exact generic_format_opp beta fexp h
    have Hd_neg : canonical beta fexp ⟨-md, ed⟩ := canonical_opp beta fexp md ed Hd
    have Hu_neg : canonical beta fexp ⟨-mu, eu⟩ := canonical_opp beta fexp mu eu Hu
    have h_round_DN_neg : round beta fexp (fun y : ℝ => ⌊y⌋) (-x)
        = -(round beta fexp (fun y : ℝ => ⌈y⌉) x) := round_DN_opp beta fexp x
    have h_round_UP_neg : round beta fexp (fun y : ℝ => ⌈y⌉) (-x)
        = -(round beta fexp (fun y : ℝ => ⌊y⌋) x) := round_UP_opp beta fexp x
    have Hxd' : F2R (beta := beta) ⟨-mu, eu⟩
        = round beta fexp (fun y : ℝ => ⌊y⌋) (-x) := by
      rw [F2R_Zopp, h_round_DN_neg, ← Hxu]
    have Hxu' : F2R (beta := beta) ⟨-md, ed⟩
        = round beta fexp (fun y : ℝ => ⌈y⌉) (-x) := by
      rw [F2R_Zopp, h_round_UP_neg, ← Hxd]
    have h_par := Hpos (-x) ⟨-mu, eu⟩ ⟨-md, ed⟩ hx' F_neg_x_n_F Hu_neg Hd_neg Hxd' Hxu'
    -- h_par : Even (-md) ↔ ¬ Even (-mu); want Even mu ↔ ¬ Even md.
    show Even mu ↔ ¬ Even md
    have h_even_neg_mu : Even (-mu) ↔ Even mu := by simp
    have h_even_neg_md : Even (-md) ↔ Even md := by simp
    rw [h_even_neg_mu, h_even_neg_md] at h_par
    tauto

/-- The DN/UP parity property for positive `x ∉ F`, given `Exists_NE`. -/
theorem DN_UP_parity_generic_pos (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    [hNE : Exists_NE beta fexp] : DN_UP_parity_pos_prop beta fexp := by
  intro x xd xu H0x Hfx Hd Hu Hxd Hxu
  set ex := mag beta x with hex_def
  have hx_ne : x ≠ 0 := ne_of_gt H0x
  have hex_lo : bpow beta (ex - 1) ≤ x := by
    have := bpow_mag_le beta hx_ne
    rwa [abs_of_pos H0x] at this
  have hex_hi : x < bpow beta ex := by
    have := bpow_mag_gt beta x
    rwa [abs_of_pos H0x] at this
  rcases le_or_gt ex (fexp ex) with Hxe | Hxe
  · -- Small x: ex ≤ fexp ex.
    -- xd.Fnum = 0 (round_DN x = 0); xu.Fnum = β^d where d = fexp ex - fexp(fexp ex + 1).
    -- d ≥ 0 by Valid_exp; in fact d = 0 (NE second clause) or β is odd (NE first clause).
    have h_DN0 : round beta fexp (fun y : ℝ => ⌊y⌋) x = 0 :=
      round_DN_small_pos beta fexp ⟨hex_lo, hex_hi⟩ Hxe
    have h_UP_bpow : round beta fexp (fun y : ℝ => ⌈y⌉) x = bpow beta (fexp ex) :=
      round_UP_small_pos beta fexp ⟨hex_lo, hex_hi⟩ Hxe
    have hxd_F2R : F2R xd = 0 := by rw [Hxd, h_DN0]
    have hxd_Fnum : xd.Fnum = 0 := by
      obtain ⟨md, ed⟩ := xd
      exact eq_0_F2R hxd_F2R
    have hxu_F2R : F2R xu = bpow beta (fexp ex) := by rw [Hxu, h_UP_bpow]
    have hxu_Fexp : xu.Fexp = fexp (fexp ex + 1) := by
      have h_can_eq : xu.Fexp = cexp beta fexp (F2R xu) := Hu
      unfold cexp at h_can_eq
      rw [hxu_F2R, mag_bpow] at h_can_eq
      exact h_can_eq
    have h_F2R_eq : (xu.Fnum : ℝ) * bpow beta xu.Fexp = bpow beta (fexp ex) := hxu_F2R
    rw [hxu_Fexp] at h_F2R_eq
    have h_small := (hValid ex).2 Hxe
    have h_le : fexp (fexp ex + 1) ≤ fexp ex := h_small.1
    set d := fexp ex - fexp (fexp ex + 1) with hd_def
    have hd_nn : 0 ≤ d := by simp [hd_def]; linarith
    have h_pow_eq : bpow beta (fexp ex)
        = bpow beta d * bpow beta (fexp (fexp ex + 1)) := by
      rw [← bpow_plus]; congr 1; simp [hd_def]
    have h_xu_Fnum_real : (xu.Fnum : ℝ) = bpow beta d := by
      have h_bpow_pos : 0 < bpow beta (fexp (fexp ex + 1)) := bpow_gt_0 _ _
      have h_eq2 : (xu.Fnum : ℝ) * bpow beta (fexp (fexp ex + 1))
          = bpow beta d * bpow beta (fexp (fexp ex + 1)) := by
        rw [h_F2R_eq, h_pow_eq]
      exact mul_right_cancel₀ (ne_of_gt h_bpow_pos) h_eq2
    have h_bpow_int : bpow beta d = ((beta.val ^ d.toNat : ℤ) : ℝ) :=
      (IZR_Zpower beta hd_nn).symm
    have h_xu_Fnum_int : xu.Fnum = (beta.val : ℤ) ^ d.toNat := by
      have h_real : ((xu.Fnum : ℤ) : ℝ) = ((beta.val ^ d.toNat : ℤ) : ℝ) := by
        rw [h_xu_Fnum_real, h_bpow_int]
      exact_mod_cast h_real
    -- Final parity argument: xd.Fnum = 0 (Even), xu.Fnum = β^d.toNat (Odd).
    have h_xd_even : Even xd.Fnum := by rw [hxd_Fnum]; exact ⟨0, by ring⟩
    have h_xu_odd : Odd xu.Fnum := by
      rcases hNE.cond with hβ_odd | hNE2
      · -- β odd: β^k odd.
        rw [h_xu_Fnum_int]; exact hβ_odd.pow
      · -- NE second clause: fexp(fexp ex + 1) = fexp ex, so d = 0.
        have hexp_eq : fexp (fexp ex + 1) = fexp ex := (hNE2 ex).2 Hxe
        have hd_zero : d = 0 := by simp [hd_def, hexp_eq]
        have hd_toNat_zero : d.toNat = 0 := by rw [hd_zero]; rfl
        rw [h_xu_Fnum_int, hd_toNat_zero, pow_zero]
        exact odd_one
    have h_xu_not_even : ¬ Even xu.Fnum := Int.not_even_iff_odd.mpr h_xu_odd
    constructor
    · intro h; exact absurd h h_xu_not_even
    · intro _; exact absurd h_xd_even (by simp_all)
  · -- Large x: fexp ex < ex. Three sub-cases on F2R xu vs bpow ex.
    have Hxe2 : fexp (ex + 1) ≤ ex := (hValid ex).1 Hxe
    have h_ulp_x : ulp beta fexp x = bpow beta (fexp ex) := by
      rw [ulp_neq_0 beta fexp hx_ne]
      unfold cexp; rfl
    have h_Hud : F2R xu = F2R xd + ulp beta fexp x := by
      rw [Hxu, Hxd]; exact round_UP_DN_ulp beta fexp Hfx
    have h_xd_lo : bpow beta (ex - 1) ≤ F2R xd := by
      rw [Hxd]
      exact (round_bounded_large_pos beta fexp _ Hxe ⟨hex_lo, hex_hi⟩).1
    have h_xu_hi : F2R xu ≤ bpow beta ex := by
      rw [Hxu]
      exact (round_bounded_large_pos beta fexp _ Hxe ⟨hex_lo, hex_hi⟩).2
    have h_xd_hi : F2R xd < bpow beta ex := by
      have h_xd_le : F2R xd ≤ x := by
        rw [Hxd]; exact (round_DN_pt beta fexp hValid x).2.1
      linarith
    rcases lt_trichotomy (F2R xu) (bpow beta ex) with Hu2 | Hu2 | Hu2
    · -- F2R xu < bpow ex: same exponent regime, xu.Fnum = xd.Fnum + 1.
      have h_xu_lo : bpow beta (ex - 1) ≤ F2R xu := by
        have h_xu_ge : x ≤ F2R xu := by
          rw [Hxu]; exact (round_UP_pt beta fexp hValid x).2.1
        linarith
      have h_mag_xd : mag beta (F2R xd) = ex :=
        mag_unique_pos beta h_xd_lo h_xd_hi
      have h_mag_xu : mag beta (F2R xu) = ex :=
        mag_unique_pos beta h_xu_lo Hu2
      have hxd_Fexp : xd.Fexp = fexp ex := by
        have h_can : xd.Fexp = cexp beta fexp (F2R xd) := Hd
        unfold cexp at h_can; rw [h_mag_xd] at h_can; exact h_can
      have hxu_Fexp : xu.Fexp = fexp ex := by
        have h_can : xu.Fexp = cexp beta fexp (F2R xu) := Hu
        unfold cexp at h_can; rw [h_mag_xu] at h_can; exact h_can
      have h_F2R_eq : (xu.Fnum : ℝ) * bpow beta (fexp ex)
          = (xd.Fnum : ℝ) * bpow beta (fexp ex) + bpow beta (fexp ex) := by
        have h1 : F2R xu = (xu.Fnum : ℝ) * bpow beta xu.Fexp := rfl
        have h2 : F2R xd = (xd.Fnum : ℝ) * bpow beta xd.Fexp := rfl
        rw [h1, hxu_Fexp, h2, hxd_Fexp, h_ulp_x] at h_Hud
        exact h_Hud
      have h_bpow_pos : 0 < bpow beta (fexp ex) := bpow_gt_0 _ _
      have h_Fnum_real : (xu.Fnum : ℝ) = (xd.Fnum : ℝ) + 1 := by
        have h_eq : (xu.Fnum : ℝ) * bpow beta (fexp ex)
            = ((xd.Fnum : ℝ) + 1) * bpow beta (fexp ex) := by
          rw [h_F2R_eq]; ring
        exact mul_right_cancel₀ (ne_of_gt h_bpow_pos) h_eq
      have h_Fnum_int : xu.Fnum = xd.Fnum + 1 := by exact_mod_cast h_Fnum_real
      rw [h_Fnum_int]
      exact Int.even_add_one
    · -- F2R xu = bpow ex: boundary case.
      -- xu canonical with F2R xu = bpow ex, so xu = ⟨β^(ex - fexp(ex+1)), fexp(ex+1)⟩.
      have hxu_F2R : F2R xu = bpow beta ex := Hu2
      have hxu_Fexp : xu.Fexp = fexp (ex + 1) := by
        have h_can : xu.Fexp = cexp beta fexp (F2R xu) := Hu
        unfold cexp at h_can
        rw [hxu_F2R, mag_bpow] at h_can
        exact h_can
      set k1 := ex - fexp (ex + 1) with hk1_def
      have hk1_nn : 0 ≤ k1 := by simp [hk1_def]; linarith
      have h_xu_F2R_eq : (xu.Fnum : ℝ) * bpow beta (fexp (ex + 1)) = bpow beta ex := by
        have : F2R xu = (xu.Fnum : ℝ) * bpow beta xu.Fexp := rfl
        rw [hxu_Fexp] at this
        rw [← this, hxu_F2R]
      have h_xu_Fnum_real : (xu.Fnum : ℝ) = bpow beta k1 := by
        have h_pow_eq : bpow beta ex
            = bpow beta k1 * bpow beta (fexp (ex + 1)) := by
          rw [← bpow_plus]; congr 1; simp [hk1_def]
        have h_bpow_pos : 0 < bpow beta (fexp (ex + 1)) := bpow_gt_0 _ _
        have h_eq2 : (xu.Fnum : ℝ) * bpow beta (fexp (ex + 1))
            = bpow beta k1 * bpow beta (fexp (ex + 1)) := by
          rw [h_xu_F2R_eq, h_pow_eq]
        exact mul_right_cancel₀ (ne_of_gt h_bpow_pos) h_eq2
      have h_xu_Fnum_int : xu.Fnum = (beta.val : ℤ) ^ k1.toNat := by
        have h_real : ((xu.Fnum : ℤ) : ℝ) = ((beta.val ^ k1.toNat : ℤ) : ℝ) := by
          rw [h_xu_Fnum_real, ← IZR_Zpower beta hk1_nn]
        exact_mod_cast h_real
      -- Now xd: F2R xd = bpow ex - bpow(fexp ex). mag(F2R xd) = ex. xd.Fexp = fexp ex.
      set k2 := ex - fexp ex with hk2_def
      have hk2_pos : 0 < k2 := by simp [hk2_def]; linarith
      have hk2_nn : 0 ≤ k2 := le_of_lt hk2_pos
      have hxd_F2R : F2R xd = bpow beta ex - bpow beta (fexp ex) := by
        rw [show F2R xd = F2R xu - ulp beta fexp x from by linarith,
            hxu_F2R, h_ulp_x]
      -- bpow(ex-1) ≤ bpow ex - bpow(fexp ex) < bpow ex
      have h_fexp_le : fexp ex ≤ ex - 1 := by linarith
      have h_bpow_fexp_le : bpow beta (fexp ex) ≤ bpow beta (ex - 1) :=
        bpow_le beta h_fexp_le
      have h_xd_lo' : bpow beta (ex - 1) ≤ F2R xd := by
        rw [hxd_F2R]
        have h_step : bpow beta (ex - 1) + bpow beta (ex - 1) ≤ bpow beta ex := by
          have h_eq : bpow beta ex = (beta.val : ℝ) * bpow beta (ex - 1) := by
            have : bpow beta ex = bpow beta ((ex - 1) + 1) := by congr 1; ring
            rw [this, bpow_plus]
            show bpow beta (ex - 1) * bpow beta 1 = (beta.val : ℝ) * bpow beta (ex - 1)
            rw [bpow_one]; ring
          have h_two_le_beta : (2 : ℝ) ≤ (beta.val : ℝ) := by
            have := beta.prop; exact_mod_cast this
          have h_pos : 0 < bpow beta (ex - 1) := bpow_gt_0 _ _
          rw [h_eq]
          have : (2 : ℝ) * bpow beta (ex - 1) ≤ (beta.val : ℝ) * bpow beta (ex - 1) :=
            mul_le_mul_of_nonneg_right h_two_le_beta (le_of_lt h_pos)
          linarith
        linarith
      have h_xd_hi' : F2R xd < bpow beta ex := by
        rw [hxd_F2R]
        have : 0 < bpow beta (fexp ex) := bpow_gt_0 _ _
        linarith
      have h_mag_xd : mag beta (F2R xd) = ex :=
        mag_unique_pos beta h_xd_lo' h_xd_hi'
      have hxd_Fexp : xd.Fexp = fexp ex := by
        have h_can : xd.Fexp = cexp beta fexp (F2R xd) := Hd
        unfold cexp at h_can; rw [h_mag_xd] at h_can; exact h_can
      have h_xd_F2R_eq : (xd.Fnum : ℝ) * bpow beta (fexp ex)
          = bpow beta ex - bpow beta (fexp ex) := by
        have : F2R xd = (xd.Fnum : ℝ) * bpow beta xd.Fexp := rfl
        rw [hxd_Fexp] at this
        rw [← this]; exact hxd_F2R
      have h_xd_Fnum_real : (xd.Fnum : ℝ) = bpow beta k2 - 1 := by
        have h_pow_eq : bpow beta ex
            = bpow beta k2 * bpow beta (fexp ex) := by
          rw [← bpow_plus]; congr 1; simp [hk2_def]
        have h_bpow_pos : 0 < bpow beta (fexp ex) := bpow_gt_0 _ _
        have h_eq2 : (xd.Fnum : ℝ) * bpow beta (fexp ex)
            = (bpow beta k2 - 1) * bpow beta (fexp ex) := by
          rw [h_xd_F2R_eq, h_pow_eq]; ring
        exact mul_right_cancel₀ (ne_of_gt h_bpow_pos) h_eq2
      have h_xd_Fnum_int : xd.Fnum = (beta.val : ℤ) ^ k2.toNat - 1 := by
        have h_pow_real : bpow beta k2 = (((beta.val : ℤ) ^ k2.toNat : ℤ) : ℝ) :=
          (IZR_Zpower beta hk2_nn).symm
        have h_real : ((xd.Fnum : ℤ) : ℝ)
            = ((((beta.val : ℤ) ^ k2.toNat - 1 : ℤ) : ℤ) : ℝ) := by
          rw [h_xd_Fnum_real, h_pow_real]; push_cast; ring
        exact_mod_cast h_real
      -- Final parity: Even xu.Fnum ↔ ¬ Even xd.Fnum.
      -- xu.Fnum = β^k1.toNat, xd.Fnum = β^k2.toNat - 1.
      have hk2_toNat_ne : k2.toNat ≠ 0 := by
        have : k2.toNat = k2 := Int.toNat_of_nonneg hk2_nn
        omega
      rw [h_xu_Fnum_int, h_xd_Fnum_int, Int.even_sub_one, not_not]
      rcases hNE.cond with hβ_odd | hNE2
      · -- β odd: both powers odd, both Even = false.
        have h1 : ¬ Even ((beta.val : ℤ) ^ k1.toNat) :=
          Int.not_even_iff_odd.mpr hβ_odd.pow
        have h2 : ¬ Even ((beta.val : ℤ) ^ k2.toNat) :=
          Int.not_even_iff_odd.mpr hβ_odd.pow
        tauto
      · -- NE clause 2: fexp(ex+1) < ex (since fexp ex < ex). So k1 ≥ 1.
        have hk1_pos : 0 < k1 := by
          have := (hNE2 ex).1 Hxe
          simp [hk1_def]; linarith
        have hk1_toNat_ne : k1.toNat ≠ 0 := by
          have : k1.toNat = k1 := Int.toNat_of_nonneg hk1_nn
          omega
        rw [Int.even_pow' hk1_toNat_ne, Int.even_pow' hk2_toNat_ne]
    · -- F2R xu > bpow ex: contradiction with h_xu_hi.
      exfalso; linarith

/-- The full DN/UP parity theorem: for any `x ∉ F`, the canonical up-rounded
mantissa has opposite parity from the down-rounded one. -/
theorem DN_UP_parity_generic (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    [Exists_NE beta fexp] : DN_UP_parity_prop beta fexp :=
  DN_UP_parity_aux beta fexp (DN_UP_parity_generic_pos beta fexp hValid)

end LeanFlocq
