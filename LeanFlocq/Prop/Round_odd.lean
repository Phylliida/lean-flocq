/-
Lean port of Coq Flocq's `Prop/Round_odd.v` — round-to-odd rounding mode.

Round-to-odd is the rounding mode where, for non-integers, the result is the
odd integer between ⌊x⌋ and ⌈x⌉. It is used to prove no-double-rounding
results: rounding through an intermediate format with round-to-odd, then to
the target with round-to-nearest-even, gives the same answer as rounding
directly with round-to-nearest-even (under a precision-gap condition).

Original Coq is © 2013–2018 Sylvie Boldo and Guillaume Melquiond, LGPL v3+.
-/
import LeanFlocq.Core.Defs
import LeanFlocq.Core.Raux
import LeanFlocq.Core.Float_prop
import LeanFlocq.Core.Generic_fmt
import LeanFlocq.Core.Round_NE
import LeanFlocq.Core.Ulp
import LeanFlocq.Calc.Operations

namespace LeanFlocq

open Classical in
/-- The round-to-odd integer rounding function.

If `x` is an integer, return it. Otherwise:
- If `⌊x⌋` is even, round up to `⌈x⌉` (which is `⌊x⌋ + 1`, hence odd).
- If `⌊x⌋` is odd, return `⌊x⌋`.

The result is always odd unless `x` itself is an integer. -/
noncomputable def Zrnd_odd (x : ℝ) : ℤ :=
  if x = (⌊x⌋ : ℝ) then ⌊x⌋
  else if Even ⌊x⌋ then ⌈x⌉ else ⌊x⌋

/-- When `x` is not an integer, `⌈x⌉ = ⌊x⌋ + 1`. -/
private theorem ceil_eq_floor_succ_of_ne {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    ⌈x⌉ = ⌊x⌋ + 1 := by
  have h_floor_le : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h_floor_lt : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne h_floor_le (Ne.symm hx)
  have h_lt_succ : x < (⌊x⌋ + 1 : ℝ) := by
    have := Int.lt_floor_add_one x; push_cast; linarith
  -- ⌈x⌉ ≥ ⌊x⌋ + 1 (since x > ⌊x⌋ means ⌈x⌉ > ⌊x⌋, so ⌈x⌉ ≥ ⌊x⌋ + 1)
  have h_ceil_gt : ⌊x⌋ < ⌈x⌉ := by
    have h_floor_lt_ceil_cast : (⌊x⌋ : ℝ) < (⌈x⌉ : ℝ) :=
      lt_of_lt_of_le h_floor_lt (Int.le_ceil x)
    exact_mod_cast h_floor_lt_ceil_cast
  -- ⌈x⌉ ≤ ⌊x⌋ + 1 (since x < ⌊x⌋ + 1 = (⌊x⌋ + 1 : ℝ))
  have h_ceil_le : ⌈x⌉ ≤ ⌊x⌋ + 1 := by
    apply Int.ceil_le.mpr
    push_cast; linarith
  omega

/-- `Zrnd_odd` is a valid rounding function: monotone and identity on integers. -/
instance valid_rnd_odd : Valid_rnd Zrnd_odd where
  Zrnd_le := by
    intro x y Hxy
    have h_floor_le_rnd_y : ⌊x⌋ ≤ Zrnd_odd y := by
      have h_floor_mono : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_le_floor Hxy
      show ⌊x⌋ ≤ (if y = (⌊y⌋ : ℝ) then ⌊y⌋
                  else if Even ⌊y⌋ then ⌈y⌉ else ⌊y⌋)
      by_cases h_y_int : y = (⌊y⌋ : ℝ)
      · rw [if_pos h_y_int]; exact h_floor_mono
      · rw [if_neg h_y_int]
        by_cases h_even : Even ⌊y⌋
        · rw [if_pos h_even]
          have : ⌊y⌋ ≤ ⌈y⌉ := by
            have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
            have h2 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
            exact_mod_cast (le_trans h1 h2)
          linarith
        · rw [if_neg h_even]; exact h_floor_mono
    show (if x = (⌊x⌋ : ℝ) then ⌊x⌋ else if Even ⌊x⌋ then ⌈x⌉ else ⌊x⌋)
       ≤ Zrnd_odd y
    by_cases h_x_int : x = (⌊x⌋ : ℝ)
    · rw [if_pos h_x_int]; exact h_floor_le_rnd_y
    · rw [if_neg h_x_int]
      by_cases h_even_x : Even ⌊x⌋
      · rw [if_pos h_even_x]
        show ⌈x⌉ ≤ (if y = (⌊y⌋ : ℝ) then ⌊y⌋
                    else if Even ⌊y⌋ then ⌈y⌉ else ⌊y⌋)
        by_cases h_y_int : y = (⌊y⌋ : ℝ)
        · rw [if_pos h_y_int]
          apply Int.ceil_le.mpr
          rw [← h_y_int]; exact Hxy
        · rw [if_neg h_y_int]
          by_cases h_even_y : Even ⌊y⌋
          · rw [if_pos h_even_y]
            exact Int.ceil_le_ceil Hxy
          · rw [if_neg h_even_y]
            have h0 : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_le_floor Hxy
            rcases lt_or_eq_of_le h0 with h_lt | h_eq
            · have h_ceil_eq : ⌈x⌉ = ⌊x⌋ + 1 := ceil_eq_floor_succ_of_ne h_x_int
              omega
            · exfalso; rw [← h_eq] at h_even_y; exact h_even_y h_even_x
      · rw [if_neg h_even_x]; exact h_floor_le_rnd_y
  Zrnd_intCast := by
    intro n
    show (if (n : ℝ) = (⌊(n : ℝ)⌋ : ℝ) then ⌊(n : ℝ)⌋
          else if Even ⌊(n : ℝ)⌋ then ⌈(n : ℝ)⌉ else ⌊(n : ℝ)⌋) = n
    have h : (n : ℝ) = (⌊(n : ℝ)⌋ : ℝ) := by rw [Int.floor_intCast]
    rw [if_pos h, Int.floor_intCast]

/-- For non-integer `x`, `Zrnd_odd x` is odd. -/
theorem Zrnd_odd_Zodd {x : ℝ} (Hx : x ≠ (⌊x⌋ : ℝ)) : ¬ Even (Zrnd_odd x) := by
  show ¬ Even (if x = (⌊x⌋ : ℝ) then ⌊x⌋
               else if Even ⌊x⌋ then ⌈x⌉ else ⌊x⌋)
  rw [if_neg Hx]
  by_cases h_even : Even ⌊x⌋
  · rw [if_pos h_even]
    have h_ceil_eq : ⌈x⌉ = ⌊x⌋ + 1 := ceil_eq_floor_succ_of_ne Hx
    rw [h_ceil_eq]
    -- Even (⌊x⌋ + 1) ↔ ¬ Even ⌊x⌋. Since Even ⌊x⌋, ¬ Even (⌊x⌋ + 1).
    intro h_even_succ
    have h_odd_succ : Odd (⌊x⌋ + 1) := Even.add_one h_even
    rw [← Int.not_even_iff_odd] at h_odd_succ
    exact h_odd_succ h_even_succ
  · rw [if_neg h_even]; exact h_even

/-- `⌊n + y⌋ = n + ⌊y⌋` for integer `n`. -/
theorem Zfloor_plus (n : ℤ) (y : ℝ) : ⌊(n : ℝ) + y⌋ = n + ⌊y⌋ :=
  Int.floor_intCast_add n y

/-- `⌈n + y⌉ = n + ⌈y⌉` for integer `n`. -/
theorem Zceil_plus (n : ℤ) (y : ℝ) : ⌈(n : ℝ) + y⌉ = n + ⌈y⌉ := by
  rw [add_comm ((n : ℝ)) y, Int.ceil_add_intCast, add_comm ⌈y⌉ n]

/-- The natural-abs parity preserves the integer parity. -/
theorem Zeven_abs (z : ℤ) : Even z.natAbs ↔ Even z :=
  Int.natAbs_even

/-! ### Rnd_odd_pt predicate and basic properties -/

/-- `f` is the round-to-odd of `x` in the format. -/
def Rnd_odd_pt (beta : radix) (fexp : ℤ → ℤ) (x f : ℝ) : Prop :=
  generic_format beta fexp f ∧
  (f = x ∨
   ((Rnd_DN_pt (generic_format beta fexp) x f ∨
     Rnd_UP_pt (generic_format beta fexp) x f) ∧
    ∃ g : float beta, f = F2R g ∧ canonical beta fexp g ∧ ¬ Even g.Fnum))

/-- A rounding function `rnd : ℝ → ℝ` is round-to-odd. -/
def Rnd_odd (beta : radix) (fexp : ℤ → ℤ) (rnd : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, Rnd_odd_pt beta fexp x (rnd x)

/-- Negation symmetry: if `-f` is the round-to-odd of `-x`, then `f` is the
round-to-odd of `x`. -/
theorem Rnd_odd_pt_opp_inv (beta : radix) (fexp : ℤ → ℤ)
    {x f : ℝ} (h : Rnd_odd_pt beta fexp (-x) (-f)) :
    Rnd_odd_pt beta fexp x f := by
  obtain ⟨H1, H2⟩ := h
  refine ⟨?_, ?_⟩
  · -- f ∈ format from -f ∈ format.
    rw [show f = -(-f) from (neg_neg f).symm]
    exact generic_format_opp beta fexp H1
  · rcases H2 with h_eq | ⟨h_dn_up, g, hg1, hg2, hg3⟩
    · -- -f = -x ⟹ f = x.
      left
      rw [show f = -(-f) from (neg_neg f).symm, h_eq]; ring
    · -- DN/UP case.
      right
      refine ⟨?_, ?_⟩
      · rcases h_dn_up with h_dn | h_up
        · -- Rnd_DN_pt F (-x) (-f). Want Rnd_UP_pt F x f.
          -- Rnd_UP_pt_opp takes DN at (x', f') and gives UP at (-x', -f').
          -- With x' = -x, f' = -f: gives UP at (x, f). ✓
          have h := Rnd_UP_pt_opp (generic_format beta fexp)
            (fun y hy => generic_format_opp beta fexp hy) h_dn
          rw [neg_neg, neg_neg] at h
          right; exact h
        · -- Rnd_UP_pt F (-x) (-f). Want Rnd_DN_pt F x f.
          have h := Rnd_DN_pt_opp (generic_format beta fexp)
            (fun y hy => generic_format_opp beta fexp hy) h_up
          rw [neg_neg, neg_neg] at h
          left; exact h
      · -- canonical odd witness for f: negate g.
        refine ⟨⟨-g.Fnum, g.Fexp⟩, ?_, ?_, ?_⟩
        · -- f = F2R ⟨-g.Fnum, g.Fexp⟩ = -F2R g.
          show f = F2R (beta := beta) ⟨-g.Fnum, g.Fexp⟩
          rw [F2R_Zopp]
          rw [show f = -(-f) from (neg_neg f).symm, hg1]
        · -- canonical of negated float
          exact canonical_opp beta fexp g.Fnum g.Fexp hg2
        · -- ¬ Even (-g.Fnum)
          show ¬ Even (-g.Fnum)
          rwa [even_neg]

/-! ### Negation symmetry for the round_odd rounding -/

/-- `round (Zrnd_odd) (-x) = -round (Zrnd_odd) x`. -/
theorem round_odd_opp (beta : radix) (fexp : ℤ → ℤ) (x : ℝ) :
    round beta fexp Zrnd_odd (-x) = -round beta fexp Zrnd_odd x := by
  unfold round
  rw [scaled_mantissa_opp, cexp_opp, ← F2R_Zopp]
  -- Show the two F2R expressions agree by matching mantissas.
  set r := scaled_mantissa beta fexp x with hr_def
  set ex := cexp beta fexp x with hex_def
  show F2R (beta := beta) ⟨Zrnd_odd (-r), ex⟩
     = F2R (beta := beta) ⟨-Zrnd_odd r, ex⟩
  congr 2
  show Zrnd_odd (-r) = -Zrnd_odd r
  unfold Zrnd_odd
  by_cases h_neg_r_int : -r = (⌊-r⌋ : ℝ)
  · -- -r is integer ⟹ r is integer.
    have h_r_int : r = (⌊r⌋ : ℝ) := by
      have h_neg_neg : -(-r) = -((⌊-r⌋ : ℝ)) := by rw [← h_neg_r_int]
      rw [neg_neg] at h_neg_neg
      rw [h_neg_neg, ← Int.cast_neg]
      congr 1
      -- ⌊r⌋ = -⌊-r⌋ when r is integer (and -r is integer).
      have : r = -((⌊-r⌋ : ℝ)) := h_neg_neg
      rw [this]
      rw [show (-((⌊-r⌋ : ℝ)) : ℝ) = ((-⌊-r⌋ : ℤ) : ℝ) from by push_cast; ring]
      rw [Int.floor_intCast]
    rw [if_pos h_neg_r_int, if_pos h_r_int]
    -- ⌊-r⌋ = -⌊r⌋ when r is integer. From -r = ⌊-r⌋ and r = ⌊r⌋: ⌊-r⌋ = -r = -⌊r⌋.
    have : (⌊-r⌋ : ℝ) = -(⌊r⌋ : ℝ) := by rw [← h_neg_r_int, ← h_r_int]
    exact_mod_cast this
  · -- -r is not integer ⟹ r is not integer.
    have h_r_not_int : r ≠ (⌊r⌋ : ℝ) := by
      intro h_r_int
      apply h_neg_r_int
      rw [h_r_int]
      rw [show -((⌊r⌋ : ℝ)) = ((-⌊r⌋ : ℤ) : ℝ) from by push_cast; ring]
      rw [Int.floor_intCast]
    rw [if_neg h_neg_r_int, if_neg h_r_not_int]
    -- For non-integer r: ⌊-r⌋ = -⌈r⌉ and ⌈-r⌉ = -⌊r⌋.
    have h_floor_neg : ⌊-r⌋ = -⌈r⌉ := Int.floor_neg
    have h_ceil_neg : ⌈-r⌉ = -⌊r⌋ := Int.ceil_neg
    have h_ceil_succ : ⌈r⌉ = ⌊r⌋ + 1 := ceil_eq_floor_succ_of_ne h_r_not_int
    -- Establish parity correspondence as an iff.
    have h_parity : Even ⌊-r⌋ ↔ ¬ Even ⌊r⌋ := by
      rw [h_floor_neg, even_neg, h_ceil_succ]
      constructor
      · intro h_e h_e2
        have h_odd : Odd (⌊r⌋ + 1) := Even.add_one h_e2
        exact (Int.not_even_iff_odd.mpr h_odd) h_e
      · intro h_ne
        have h_odd : Odd ⌊r⌋ := Int.not_even_iff_odd.mp h_ne
        obtain ⟨k, hk⟩ := h_odd
        refine ⟨k + 1, ?_⟩; omega
    by_cases h_even_r : Even ⌊r⌋
    · -- Even ⌊r⌋: ¬ Even ⌊-r⌋, take floor branch on LHS, ceil branch on RHS.
      have h_not_even_neg : ¬ Even ⌊-r⌋ := fun h => (h_parity.mp h) h_even_r
      rw [if_neg h_not_even_neg, if_pos h_even_r, h_floor_neg, h_ceil_succ]
    · -- ¬ Even ⌊r⌋: Even ⌊-r⌋, take ceil branch on LHS, floor branch on RHS.
      have h_even_neg : Even ⌊-r⌋ := h_parity.mpr h_even_r
      rw [if_pos h_even_neg, if_neg h_even_r, h_ceil_neg]

/-- When `x` is an integer with even floor, `Zrnd_odd (x + y) = x + Zrnd_odd y`. -/
theorem Zrnd_odd_plus {x y : ℝ} (Hx : x = (⌊x⌋ : ℝ)) (H : Even ⌊x⌋) :
    ((Zrnd_odd (x + y) : ℝ)) = x + (Zrnd_odd y : ℝ) := by
  unfold Zrnd_odd
  have h_floor_sum : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ := by
    nth_rewrite 1 [Hx]; exact Zfloor_plus _ y
  have h_even_sum : Even ⌊x + y⌋ ↔ Even ⌊y⌋ := by
    rw [h_floor_sum, Int.even_add]
    exact ⟨fun h => h.mp H, fun h => ⟨fun _ => h, fun _ => H⟩⟩
  by_cases h_y_int : y = (⌊y⌋ : ℝ)
  · -- y integer ⟹ x + y integer.
    have h_sum_int : x + y = (⌊x + y⌋ : ℝ) := by
      rw [h_floor_sum]
      push_cast
      rw [← Hx, ← h_y_int]
    rw [if_pos h_sum_int, if_pos h_y_int, h_floor_sum]
    push_cast
    rw [← Hx]
  · -- y not integer ⟹ x + y not integer.
    have h_sum_not_int : x + y ≠ (⌊x + y⌋ : ℝ) := by
      rw [h_floor_sum]
      push_cast
      rw [← Hx]
      intro h
      have : y = (⌊y⌋ : ℝ) := by linarith
      exact h_y_int this
    rw [if_neg h_sum_not_int, if_neg h_y_int]
    by_cases h_even_y : Even ⌊y⌋
    · have h_even_xy : Even ⌊x + y⌋ := h_even_sum.mpr h_even_y
      rw [if_pos h_even_xy, if_pos h_even_y]
      -- ⌈x + y⌉ = x + ⌈y⌉, since x integer.
      have h_ceil_sum : ⌈x + y⌉ = ⌊x⌋ + ⌈y⌉ := by
        nth_rewrite 1 [Hx]; exact Zceil_plus _ y
      rw [h_ceil_sum]
      push_cast; rw [← Hx]
    · have h_not_even_xy : ¬ Even ⌊x + y⌋ := fun h => h_even_y (h_even_sum.mp h)
      rw [if_neg h_not_even_xy, if_neg h_even_y, h_floor_sum]
      push_cast; rw [← Hx]

/-! ### Round_odd produces a round-to-odd point -/

/-- The core theorem: rounding `x` with `Zrnd_odd` produces a round-to-odd point.

For `x` not in the format, either round-down or round-up is selected so that
the canonical mantissa is odd. This is the parity-engineering invariant. -/
theorem round_odd_pt (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) [Exists_NE beta fexp] (x : ℝ) :
    Rnd_odd_pt beta fexp x (round beta fexp Zrnd_odd x) := by
  suffices h_pos : ∀ y : ℝ, 0 < y →
      Rnd_odd_pt beta fexp y (round beta fexp Zrnd_odd y) by
    rcases lt_trichotomy x 0 with hx | hx | hx
    · -- x < 0: reduce via opp_inv.
      apply Rnd_odd_pt_opp_inv beta fexp
      rw [← round_odd_opp]
      have h : 0 < -x := by linarith
      have := h_pos (-x) h
      simpa using this
    · -- x = 0.
      rw [hx, round_0]
      exact ⟨generic_format_0 _ _, Or.inl rfl⟩
    · exact h_pos x hx
  -- Positive case.
  intro x Hxp
  set o := round beta fexp Zrnd_odd x with ho_def
  have Ho : generic_format beta fexp o :=
    generic_format_round beta fexp hValid Zrnd_odd x
  refine ⟨Ho, ?_⟩
  by_cases Hx_F : o = x
  · left; exact Hx_F
  right
  set sm := scaled_mantissa beta fexp x with hsm_def
  have h_sm_pos : 0 < sm := mul_pos Hxp (bpow_gt_0 _ _)
  have h_sm_nn : 0 ≤ sm := le_of_lt h_sm_pos
  have h_x_not_F : ¬ generic_format beta fexp x := by
    intro h_x_F; apply Hx_F
    rw [ho_def, round_generic beta fexp Zrnd_odd h_x_F]
  have h_sm_not_int : sm ≠ (⌊sm⌋ : ℝ) := by
    intro h_sm_eq
    apply h_x_not_F
    show x = F2R (beta := beta) ⟨Ztrunc sm, cexp beta fexp x⟩
    rw [Ztrunc_floor h_sm_nn]
    show x = ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x)
    rw [← h_sm_eq]
    exact (scaled_mantissa_mult_bpow beta fexp x).symm
  set rd := round beta fexp (fun y : ℝ => ⌊y⌋) x with hrd_def
  set ru := round beta fexp (fun y : ℝ => ⌈y⌉) x with hru_def
  -- 0 ≤ rd from x > 0 and monotonicity of round.
  have h_rd_nn : 0 ≤ rd := by
    rw [hrd_def, show (0 : ℝ) = round beta fexp (fun y : ℝ => ⌊y⌋) 0 from
          (round_0 _ _ _).symm]
    exact round_le beta fexp hValid _ (le_of_lt Hxp)
  -- Round_DN explicit: rd = ⌊sm⌋ · bpow(cexp x).
  have h_rd_explicit : rd = ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x) := by
    rw [hrd_def]; rfl
  have h_bpow_ne : bpow beta (cexp beta fexp x) ≠ 0 := ne_of_gt (bpow_gt_0 _ _)
  by_cases h_even_floor : Even ⌊sm⌋
  · -- Even ⌊sm⌋: Zrnd_odd sm = ⌈sm⌉, so o = ru.
    have h_o_eq_ru : o = ru := by
      rw [ho_def, hru_def]
      unfold round
      congr 2
      show Zrnd_odd sm = ⌈sm⌉
      show (if sm = (⌊sm⌋ : ℝ) then ⌊sm⌋
            else if Even ⌊sm⌋ then ⌈sm⌉ else ⌊sm⌋) = ⌈sm⌉
      rw [if_neg h_sm_not_int, if_pos h_even_floor]
    refine ⟨Or.inr (h_o_eq_ru ▸ round_UP_pt beta fexp hValid x), ?_⟩
    -- Canonical witness for ru.
    set gu_mant := Ztrunc (scaled_mantissa beta fexp ru) with hgu_mant_def
    set gu_exp := cexp beta fexp ru with hgu_exp_def
    set gd_mant := Ztrunc (scaled_mantissa beta fexp rd) with hgd_mant_def
    set gd_exp := cexp beta fexp rd with hgd_exp_def
    have h_ru_F2R : ru = F2R (beta := beta) ⟨gu_mant, gu_exp⟩ :=
      generic_format_round beta fexp hValid _ x
    have h_rd_F2R : rd = F2R (beta := beta) ⟨gd_mant, gd_exp⟩ :=
      generic_format_round beta fexp hValid _ x
    have h_gd_can : canonical beta fexp ⟨gd_mant, gd_exp⟩ := by
      show gd_exp = cexp beta fexp (F2R (beta := beta) ⟨gd_mant, gd_exp⟩)
      rw [← h_rd_F2R]
    have h_gu_can : canonical beta fexp ⟨gu_mant, gu_exp⟩ := by
      show gu_exp = cexp beta fexp (F2R (beta := beta) ⟨gu_mant, gu_exp⟩)
      rw [← h_ru_F2R]
    have h_parity : Even gu_mant ↔ ¬ Even gd_mant :=
      DN_UP_parity_generic beta fexp hValid x ⟨gd_mant, gd_exp⟩ ⟨gu_mant, gu_exp⟩
        h_x_not_F h_gd_can h_gu_can h_rd_F2R.symm h_ru_F2R.symm
    -- gd_mant is Even (= ⌊sm⌋ if rd > 0, = 0 if rd = 0).
    have h_gd_even : Even gd_mant := by
      rcases eq_or_lt_of_le h_rd_nn with h_rd_zero | h_rd_pos
      · -- rd = 0: gd_mant = 0.
        have h_gd_mant_zero : gd_mant = 0 := by
          rw [hgd_mant_def, ← h_rd_zero]
          unfold scaled_mantissa
          rw [zero_mul, Ztrunc_floor (le_refl 0), Int.floor_zero]
        rw [h_gd_mant_zero]; exact ⟨0, by ring⟩
      · -- rd > 0: gd_exp = cexp x, so gd_mant = ⌊sm⌋.
        have h_cexp_rd : gd_exp = cexp beta fexp x := by
          rw [hgd_exp_def, hrd_def]
          exact cexp_DN beta fexp hValid h_rd_pos
        have h_F2R_eq : ((gd_mant : ℤ) : ℝ) * bpow beta gd_exp
                      = ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x) := by
          show F2R (beta := beta) ⟨gd_mant, gd_exp⟩ = _
          rw [← h_rd_F2R, h_rd_explicit]
        rw [h_cexp_rd] at h_F2R_eq
        have h_mant_cast : (gd_mant : ℝ) = (⌊sm⌋ : ℝ) :=
          mul_right_cancel₀ h_bpow_ne h_F2R_eq
        have : gd_mant = ⌊sm⌋ := by exact_mod_cast h_mant_cast
        rw [this]; exact h_even_floor
    exact ⟨⟨gu_mant, gu_exp⟩, h_o_eq_ru.trans h_ru_F2R, h_gu_can,
           fun h => (h_parity.mp h) h_gd_even⟩
  · -- ¬ Even ⌊sm⌋: Zrnd_odd sm = ⌊sm⌋, so o = rd.
    have h_o_eq_rd : o = rd := by
      rw [ho_def, hrd_def]
      unfold round
      congr 2
      show Zrnd_odd sm = ⌊sm⌋
      show (if sm = (⌊sm⌋ : ℝ) then ⌊sm⌋
            else if Even ⌊sm⌋ then ⌈sm⌉ else ⌊sm⌋) = ⌊sm⌋
      rw [if_neg h_sm_not_int, if_neg h_even_floor]
    refine ⟨Or.inl (h_o_eq_rd ▸ round_DN_pt beta fexp hValid x), ?_⟩
    -- rd > 0 (else ⌊sm⌋ = 0 which is even, contradicting hypothesis).
    have h_rd_pos : 0 < rd := by
      rcases eq_or_lt_of_le h_rd_nn with h_rd_zero | h_rd_pos
      · exfalso
        have h_zero_eq : ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x) = 0 := by
          rw [← h_rd_explicit, ← h_rd_zero]
        have h_floor_zero : ⌊sm⌋ = 0 := by
          have := (mul_eq_zero.mp h_zero_eq).resolve_right h_bpow_ne
          exact_mod_cast this
        apply h_even_floor; rw [h_floor_zero]; exact ⟨0, by ring⟩
      · exact h_rd_pos
    refine ⟨⟨⌊sm⌋, cexp beta fexp x⟩, ?_, ?_, h_even_floor⟩
    · -- o = F2R⟨⌊sm⌋, cexp x⟩.
      rw [h_o_eq_rd, h_rd_explicit]; rfl
    · -- canonical: cexp x = cexp(F2R⟨⌊sm⌋, cexp x⟩) = cexp rd.
      show cexp beta fexp x
         = cexp beta fexp (F2R (beta := beta) ⟨⌊sm⌋, cexp beta fexp x⟩)
      have h_F2R_eq_rd : F2R (beta := beta) ⟨⌊sm⌋, cexp beta fexp x⟩ = rd := by
        show ((⌊sm⌋ : ℤ) : ℝ) * bpow beta (cexp beta fexp x) = rd
        rw [← h_rd_explicit]
      rw [h_F2R_eq_rd]
      exact (cexp_DN beta fexp hValid h_rd_pos).symm

/-! ### Uniqueness and monotonicity of round-to-odd -/

/-- The round-to-odd point of `x` is unique. -/
theorem Rnd_odd_pt_unique (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) [Exists_NE beta fexp]
    {x f1 f2 : ℝ} (H1 : Rnd_odd_pt beta fexp x f1)
    (H2 : Rnd_odd_pt beta fexp x f2) :
    f1 = f2 := by
  obtain ⟨Ff1, H1'⟩ := H1
  obtain ⟨Ff2, H2'⟩ := H2
  -- Case 1: x is in the format. Then both f1 and f2 must equal x.
  rcases generic_format_EM beta fexp hValid x with L | L
  · have h_f1_eq_x : f1 = x := by
      rcases H1' with h | ⟨h_du, _⟩
      · exact h
      · rcases h_du with h_dn | h_up
        · exact Rnd_DN_pt_idempotent _ h_dn L
        · exact Rnd_UP_pt_idempotent _ h_up L
    have h_f2_eq_x : f2 = x := by
      rcases H2' with h | ⟨h_du, _⟩
      · exact h
      · rcases h_du with h_dn | h_up
        · exact Rnd_DN_pt_idempotent _ h_dn L
        · exact Rnd_UP_pt_idempotent _ h_up L
    rw [h_f1_eq_x, h_f2_eq_x]
  -- Case 2: x ∉ format. Both f1 and f2 are in the DN/UP case.
  rcases H1' with h | ⟨h1_du, g1, hg1_f, hg1_can, hg1_odd⟩
  · exfalso; apply L; rw [← h]; exact Ff1
  rcases H2' with h | ⟨h2_du, g2, hg2_f, hg2_can, hg2_odd⟩
  · exfalso; apply L; rw [← h]; exact Ff2
  -- Both DN, both UP, or mixed.
  rcases h1_du with h1_dn | h1_up <;> rcases h2_du with h2_dn | h2_up
  · -- Both DN: unique.
    exact Rnd_DN_pt_unique _ h1_dn h2_dn
  · -- f1 DN, f2 UP: contradicts parity.
    exfalso
    set gd_mant := Ztrunc (scaled_mantissa beta fexp
                    (round beta fexp (fun y : ℝ => ⌊y⌋) x)) with hgd_def
    set gd_exp := cexp beta fexp (round beta fexp (fun y : ℝ => ⌊y⌋) x) with hgde_def
    set gu_mant := Ztrunc (scaled_mantissa beta fexp
                    (round beta fexp (fun y : ℝ => ⌈y⌉) x)) with hgu_def
    set gu_exp := cexp beta fexp (round beta fexp (fun y : ℝ => ⌈y⌉) x) with hgue_def
    have h_rd_F2R : round beta fexp (fun y : ℝ => ⌊y⌋) x
                  = F2R (beta := beta) ⟨gd_mant, gd_exp⟩ :=
      generic_format_round beta fexp hValid _ x
    have h_ru_F2R : round beta fexp (fun y : ℝ => ⌈y⌉) x
                  = F2R (beta := beta) ⟨gu_mant, gu_exp⟩ :=
      generic_format_round beta fexp hValid _ x
    have h_gd_can : canonical beta fexp ⟨gd_mant, gd_exp⟩ := by
      show gd_exp = cexp beta fexp (F2R (beta := beta) ⟨gd_mant, gd_exp⟩)
      rw [← h_rd_F2R]
    have h_gu_can : canonical beta fexp ⟨gu_mant, gu_exp⟩ := by
      show gu_exp = cexp beta fexp (F2R (beta := beta) ⟨gu_mant, gu_exp⟩)
      rw [← h_ru_F2R]
    have h_parity : Even gu_mant ↔ ¬ Even gd_mant :=
      DN_UP_parity_generic beta fexp hValid x ⟨gd_mant, gd_exp⟩ ⟨gu_mant, gu_exp⟩
        L h_gd_can h_gu_can h_rd_F2R.symm h_ru_F2R.symm
    -- f1 = F2R g1 (DN) so g1 ≡ ⟨gd_mant, gd_exp⟩ as canonical reps.
    have h_f1_eq_rd : f1 = round beta fexp (fun y : ℝ => ⌊y⌋) x :=
      Rnd_DN_pt_unique _ h1_dn (round_DN_pt beta fexp hValid x)
    have h_f2_eq_ru : f2 = round beta fexp (fun y : ℝ => ⌈y⌉) x :=
      Rnd_UP_pt_unique _ h2_up (round_UP_pt beta fexp hValid x)
    -- From g1 canonical = canonical of round_DN: their Fnums match.
    have h_g1_eq_gd : g1.Fnum = gd_mant := by
      have h1 : F2R g1 = F2R (beta := beta) ⟨gd_mant, gd_exp⟩ := by
        rw [← hg1_f, h_f1_eq_rd, h_rd_F2R]
      have h_exp_eq : g1.Fexp = gd_exp := by
        have h_can : g1.Fexp = cexp beta fexp (F2R g1) := hg1_can
        rw [h_can, ← hg1_f, h_f1_eq_rd]
      have h_bpow_ne : bpow beta g1.Fexp ≠ 0 := ne_of_gt (bpow_gt_0 _ _)
      have h_eq : (g1.Fnum : ℝ) * bpow beta g1.Fexp
                = (gd_mant : ℝ) * bpow beta gd_exp := h1
      rw [h_exp_eq] at h_eq
      have h_mant_real : (g1.Fnum : ℝ) = (gd_mant : ℝ) :=
        mul_right_cancel₀ (h_exp_eq ▸ h_bpow_ne) h_eq
      exact_mod_cast h_mant_real
    have h_g2_eq_gu : g2.Fnum = gu_mant := by
      have h1 : F2R g2 = F2R (beta := beta) ⟨gu_mant, gu_exp⟩ := by
        rw [← hg2_f, h_f2_eq_ru, h_ru_F2R]
      have h_exp_eq : g2.Fexp = gu_exp := by
        have h_can : g2.Fexp = cexp beta fexp (F2R g2) := hg2_can
        rw [h_can, ← hg2_f, h_f2_eq_ru]
      have h_bpow_ne : bpow beta g2.Fexp ≠ 0 := ne_of_gt (bpow_gt_0 _ _)
      have h_eq : (g2.Fnum : ℝ) * bpow beta g2.Fexp
                = (gu_mant : ℝ) * bpow beta gu_exp := h1
      rw [h_exp_eq] at h_eq
      have h_mant_real : (g2.Fnum : ℝ) = (gu_mant : ℝ) :=
        mul_right_cancel₀ (h_exp_eq ▸ h_bpow_ne) h_eq
      exact_mod_cast h_mant_real
    rw [h_g1_eq_gd] at hg1_odd
    rw [h_g2_eq_gu] at hg2_odd
    -- gd_mant odd ∧ gu_mant odd, but parity says gu even ↔ gd not even, contradiction.
    have h_gu_even : Even gu_mant := h_parity.mpr hg1_odd
    exact hg2_odd h_gu_even
  · -- f1 UP, f2 DN: symmetric. By Rnd_UP_pt_unique/Rnd_DN_pt_unique, just swap.
    exfalso
    set gd_mant := Ztrunc (scaled_mantissa beta fexp
                    (round beta fexp (fun y : ℝ => ⌊y⌋) x)) with hgd_def
    set gd_exp := cexp beta fexp (round beta fexp (fun y : ℝ => ⌊y⌋) x) with hgde_def
    set gu_mant := Ztrunc (scaled_mantissa beta fexp
                    (round beta fexp (fun y : ℝ => ⌈y⌉) x)) with hgu_def
    set gu_exp := cexp beta fexp (round beta fexp (fun y : ℝ => ⌈y⌉) x) with hgue_def
    have h_rd_F2R : round beta fexp (fun y : ℝ => ⌊y⌋) x
                  = F2R (beta := beta) ⟨gd_mant, gd_exp⟩ :=
      generic_format_round beta fexp hValid _ x
    have h_ru_F2R : round beta fexp (fun y : ℝ => ⌈y⌉) x
                  = F2R (beta := beta) ⟨gu_mant, gu_exp⟩ :=
      generic_format_round beta fexp hValid _ x
    have h_gd_can : canonical beta fexp ⟨gd_mant, gd_exp⟩ := by
      show gd_exp = cexp beta fexp (F2R (beta := beta) ⟨gd_mant, gd_exp⟩)
      rw [← h_rd_F2R]
    have h_gu_can : canonical beta fexp ⟨gu_mant, gu_exp⟩ := by
      show gu_exp = cexp beta fexp (F2R (beta := beta) ⟨gu_mant, gu_exp⟩)
      rw [← h_ru_F2R]
    have h_parity : Even gu_mant ↔ ¬ Even gd_mant :=
      DN_UP_parity_generic beta fexp hValid x ⟨gd_mant, gd_exp⟩ ⟨gu_mant, gu_exp⟩
        L h_gd_can h_gu_can h_rd_F2R.symm h_ru_F2R.symm
    have h_f1_eq_ru : f1 = round beta fexp (fun y : ℝ => ⌈y⌉) x :=
      Rnd_UP_pt_unique _ h1_up (round_UP_pt beta fexp hValid x)
    have h_f2_eq_rd : f2 = round beta fexp (fun y : ℝ => ⌊y⌋) x :=
      Rnd_DN_pt_unique _ h2_dn (round_DN_pt beta fexp hValid x)
    have h_g1_eq_gu : g1.Fnum = gu_mant := by
      have h1 : F2R g1 = F2R (beta := beta) ⟨gu_mant, gu_exp⟩ := by
        rw [← hg1_f, h_f1_eq_ru, h_ru_F2R]
      have h_exp_eq : g1.Fexp = gu_exp := by
        have h_can : g1.Fexp = cexp beta fexp (F2R g1) := hg1_can
        rw [h_can, ← hg1_f, h_f1_eq_ru]
      have h_bpow_ne : bpow beta g1.Fexp ≠ 0 := ne_of_gt (bpow_gt_0 _ _)
      have h_eq : (g1.Fnum : ℝ) * bpow beta g1.Fexp
                = (gu_mant : ℝ) * bpow beta gu_exp := h1
      rw [h_exp_eq] at h_eq
      have h_mant_real : (g1.Fnum : ℝ) = (gu_mant : ℝ) :=
        mul_right_cancel₀ (h_exp_eq ▸ h_bpow_ne) h_eq
      exact_mod_cast h_mant_real
    have h_g2_eq_gd : g2.Fnum = gd_mant := by
      have h1 : F2R g2 = F2R (beta := beta) ⟨gd_mant, gd_exp⟩ := by
        rw [← hg2_f, h_f2_eq_rd, h_rd_F2R]
      have h_exp_eq : g2.Fexp = gd_exp := by
        have h_can : g2.Fexp = cexp beta fexp (F2R g2) := hg2_can
        rw [h_can, ← hg2_f, h_f2_eq_rd]
      have h_bpow_ne : bpow beta g2.Fexp ≠ 0 := ne_of_gt (bpow_gt_0 _ _)
      have h_eq : (g2.Fnum : ℝ) * bpow beta g2.Fexp
                = (gd_mant : ℝ) * bpow beta gd_exp := h1
      rw [h_exp_eq] at h_eq
      have h_mant_real : (g2.Fnum : ℝ) = (gd_mant : ℝ) :=
        mul_right_cancel₀ (h_exp_eq ▸ h_bpow_ne) h_eq
      exact_mod_cast h_mant_real
    rw [h_g1_eq_gu] at hg1_odd
    rw [h_g2_eq_gd] at hg2_odd
    have h_gu_even : Even gu_mant := h_parity.mpr hg2_odd
    exact hg1_odd h_gu_even
  · -- Both UP: unique.
    exact Rnd_UP_pt_unique _ h1_up h2_up

/-- Round-to-odd is monotone. -/
theorem Rnd_odd_pt_monotone (beta : radix) (fexp : ℤ → ℤ)
    (hValid : Valid_exp fexp) [Exists_NE beta fexp] :
    round_pred_monotone (Rnd_odd_pt beta fexp) := by
  intro x y f g H1 H2 Hxy
  have h_f_eq : f = round beta fexp Zrnd_odd x :=
    Rnd_odd_pt_unique beta fexp hValid H1 (round_odd_pt beta fexp hValid x)
  have h_g_eq : g = round beta fexp Zrnd_odd y :=
    Rnd_odd_pt_unique beta fexp hValid H2 (round_odd_pt beta fexp hValid y)
  rw [h_f_eq, h_g_eq]
  exact round_le beta fexp hValid Zrnd_odd Hxy

end LeanFlocq
