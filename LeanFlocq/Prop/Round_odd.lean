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

/-! ### Stage 5: Odd_prop_aux — geometry around the DN/UP midpoint

The lemmas below build up to `round_N_odd_pos` (and `round_N_odd`), the
no-double-rounding theorem: rounding to nearest at a target precision of
(rounding to odd at a finer precision) of `x` equals rounding to nearest
directly, provided the precision gap is at least 2.

The setup is shared across many lemmas:
- `beta` has even radix
- `fexp` (target) and `fexpe` (finer) are valid with `Exists_NE`
- `fexpe e ≤ fexp e - 2`
- `d, u` are the canonical DN/UP witnesses for `x > 0` in `fexp`
- `m = (F2R d + F2R u) / 2` is the midpoint

Rather than a Lean `section`, we pass these hypotheses explicitly to match
the file's style. -/

/-- A finer-precision format includes the coarser one (precision gap ≥ 2). -/
theorem generic_format_fexpe_fexp (beta : radix) (fexp fexpe : ℤ → ℤ)
    (fexpe_fexp : ∀ e, fexpe e ≤ fexp e - 2)
    {x : ℝ} (Hx : generic_format beta fexp x) :
    generic_format beta fexpe x := by
  apply generic_inclusion_mag beta fexp fexpe ?_ Hx
  intro _
  linarith [fexpe_fexp (mag beta x)]

/-- Given a float `g` with `F2R g = x` and `Fexp g > c (mag x)`, there's an
equivalent representation at exponent exactly `c (mag x)` whose mantissa is
even. Uses `Even beta` to deliver the parity. -/
theorem exists_even_fexp_lt (beta : radix) (Even_beta : Even beta.val)
    (c : ℤ → ℤ) {x : ℝ}
    (h : ∃ f : float beta, F2R f = x ∧ c (mag beta x) < f.Fexp) :
    ∃ f : float beta, F2R f = x ∧ canonical beta c f ∧ Even f.Fnum := by
  obtain ⟨g, hg1, hg2⟩ := h
  set k : ℕ := (g.Fexp - c (mag beta x)).toNat with hk_def
  have hk_eq : (k : ℤ) = g.Fexp - c (mag beta x) := Int.toNat_of_nonneg (by linarith)
  have hk_pos : 0 < k := by
    have : 0 < (k : ℤ) := by rw [hk_eq]; linarith
    exact_mod_cast this
  have h_F2R : (((g.Fnum * (beta.val : ℤ)^k : ℤ)) : ℝ) * bpow beta (c (mag beta x))
      = F2R g := by
    show (((g.Fnum * (beta.val : ℤ)^k : ℤ)) : ℝ) * bpow beta (c (mag beta x))
      = (g.Fnum : ℝ) * bpow beta g.Fexp
    push_cast
    rw [mul_assoc]
    have h_pow : ((beta.val : ℤ)^k : ℝ) = bpow beta (k : ℤ) := by
      rw [bpow]; push_cast; rfl
    rw [h_pow, ← bpow_plus]
    congr 2
    linarith [hk_eq]
  have h_eq_x : (((g.Fnum * (beta.val : ℤ)^k : ℤ)) : ℝ) * bpow beta (c (mag beta x)) = x :=
    h_F2R.trans hg1
  refine ⟨⟨g.Fnum * (beta.val : ℤ)^k, c (mag beta x)⟩, h_eq_x, ?_, ?_⟩
  · -- canonical
    show c (mag beta x) = cexp beta c
      ((((g.Fnum * (beta.val : ℤ)^k : ℤ)) : ℝ) * bpow beta (c (mag beta x)))
    rw [h_eq_x]; rfl
  · -- Even Fnum
    show Even (g.Fnum * (beta.val : ℤ)^k)
    apply Even.mul_left
    rw [Int.even_pow]
    exact ⟨Even_beta, Nat.pos_iff_ne_zero.mp hk_pos⟩

/-- `F2R d = round_DN(x)`. -/
theorem d_eq_round_DN (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {d : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d)) :
    F2R d = round beta fexp (fun y : ℝ => ⌊y⌋) x :=
  Rnd_DN_pt_unique _ Hd (round_DN_pt beta fexp hValid x)

/-- `F2R u = round_UP(x)`. -/
theorem u_eq_round_UP (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {u : float beta}
    (Hu : Rnd_UP_pt (generic_format beta fexp) x (F2R u)) :
    F2R u = round beta fexp (fun y : ℝ => ⌈y⌉) x :=
  Rnd_UP_pt_unique _ Hu (round_UP_pt beta fexp hValid x)

/-- `0 ≤ F2R d` when `x > 0`. -/
theorem d_ge_0 (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {d : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (xPos : 0 < x) :
    0 ≤ F2R d := by
  rw [d_eq_round_DN beta fexp hValid Hd]
  exact round_ge_generic beta fexp hValid _ (generic_format_0 _ _) (le_of_lt xPos)

/-- `mag(F2R d) = mag x` when `0 < F2R d`. -/
theorem mag_d (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {d : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Y : 0 < F2R d) :
    mag beta (F2R d) = mag beta x := by
  rw [d_eq_round_DN beta fexp hValid Hd]
  apply mag_DN beta fexp hValid
  rw [← d_eq_round_DN beta fexp hValid Hd]
  exact Y

/-- `Fexp d = fexp(mag x)` when `0 < F2R d` and `d` is canonical. -/
theorem Fexp_d (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {d : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : canonical beta fexp d) (Y : 0 < F2R d) :
    d.Fexp = fexp (mag beta x) := by
  have h_can : d.Fexp = cexp beta fexp (F2R d) := Cd
  rw [h_can]
  show fexp (mag beta (F2R d)) = fexp (mag beta x)
  rw [mag_d beta fexp hValid Hd Y]

/-- `bpow(mag x) ∈ F` when `0 < F2R d` and `d` is canonical. -/
theorem format_bpow_x (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {x : ℝ} {d : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Cd : canonical beta fexp d) (Y : 0 < F2R d) :
    generic_format beta fexp (bpow beta (mag beta x)) := by
  apply generic_format_bpow' beta fexp hValid
  have h_F2Rd_ne : F2R d ≠ 0 := ne_of_gt Y
  have h_F2Rd_F : generic_format beta fexp (F2R d) := Hd.1
  have h_lt : cexp beta fexp (F2R d) < mag beta (F2R d) :=
    mag_generic_gt beta fexp hValid h_F2Rd_ne h_F2Rd_F
  have h_x_pos : 0 < x := lt_of_lt_of_le Y Hd.2.1
  have h_le : mag beta (F2R d) ≤ mag beta x := by
    apply mag_le_abs beta h_F2Rd_ne
    rw [abs_of_pos Y, abs_of_pos h_x_pos]
    exact Hd.2.1
  have h_Fexp : d.Fexp = cexp beta fexp (F2R d) := Cd
  have h_Fexp_eq : d.Fexp = fexp (mag beta x) := Fexp_d beta fexp hValid Hd Cd Y
  -- Goal: fexp (mag beta x) ≤ mag beta x
  -- We have: fexp(mag x) = Fexp d = cexp(F2R d) = fexp(mag(F2R d)) < mag(F2R d) ≤ mag x
  rw [← h_Fexp_eq, h_Fexp]
  show fexp (mag beta (F2R d)) ≤ mag beta x
  -- cexp(F2R d) = fexp(mag(F2R d)) by definition
  exact le_trans (le_of_lt h_lt) h_le

/-- `bpow(mag(F2R d)) ∈ F` when `0 < F2R d`. -/
theorem format_bpow_d (beta : radix) (fexp : ℤ → ℤ) (hValid : Valid_exp fexp)
    {d : float beta} (Hd_F : generic_format beta fexp (F2R d)) (Y : 0 < F2R d) :
    generic_format beta fexp (bpow beta (mag beta (F2R d))) := by
  apply generic_format_bpow' beta fexp hValid
  have h_ne : F2R d ≠ 0 := ne_of_gt Y
  have hlt : cexp beta fexp (F2R d) < mag beta (F2R d) :=
    mag_generic_gt beta fexp hValid h_ne Hd_F
  show fexp (mag beta (F2R d)) ≤ mag beta (F2R d)
  exact le_of_lt hlt

/-- `F2R d ≤ m = (F2R d + F2R u) / 2`. -/
theorem d_le_m (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {d u : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Hu : Rnd_UP_pt (generic_format beta fexp) x (F2R u)) :
    F2R d ≤ (F2R d + F2R u) / 2 := by
  have h_du : F2R d ≤ F2R u := le_trans Hd.2.1 Hu.2.1
  linarith

/-- `m ≤ F2R u`. -/
theorem m_le_u (beta : radix) (fexp : ℤ → ℤ) {x : ℝ} {d u : float beta}
    (Hd : Rnd_DN_pt (generic_format beta fexp) x (F2R d))
    (Hu : Rnd_UP_pt (generic_format beta fexp) x (F2R u)) :
    (F2R d + F2R u) / 2 ≤ F2R u := by
  have h_du : F2R d ≤ F2R u := le_trans Hd.2.1 Hu.2.1
  linarith

/-! ### Magnitude and canonical exponent preservation under round-to-odd -/

/-- Under FLT with even radix and `prec > 1`, round-to-odd preserves the
magnitude (when not in the subnormal regime). -/
theorem mag_round_odd (beta : radix) (Even_beta : Even beta.val)
    (emin prec : ℤ) (Hp1 : 1 < prec)
    {x : ℝ} (Hx : emin < mag beta x) :
    mag beta (round beta (FLT_exp emin prec) Zrnd_odd x) = mag beta x := by
  have Hp : 0 < prec := by linarith
  have hValid : Valid_exp (FLT_exp emin prec) := FLT_exp_valid emin prec Hp
  haveI : Exists_NE beta (FLT_exp emin prec) :=
    exists_NE_FLT beta emin prec Hp (Or.inr Hp1)
  by_cases Zx : x = 0
  · rw [Zx, round_0]
  set e := mag beta x with he_def
  -- bpow(e-1) ≤ |x| and |x| < bpow(e).
  have h_lo : bpow beta (e - 1) ≤ |x| := bpow_mag_le beta Zx
  have h_hi : |x| < bpow beta e := bpow_mag_gt beta x
  refine mag_unique beta ?_ ?_
  · -- Show: bpow(e-1) ≤ |round x|.
    apply abs_round_ge_generic beta (FLT_exp emin prec) hValid Zrnd_odd
    · exact FLT_format_bpow beta emin prec Hp (e - 1) (by linarith)
    · exact h_lo
  · -- Show: |round x| < bpow e.
    have h_le : |round beta (FLT_exp emin prec) Zrnd_odd x| ≤ bpow beta e := by
      apply abs_round_le_generic beta (FLT_exp emin prec) hValid Zrnd_odd
      · exact FLT_format_bpow beta emin prec Hp e (by linarith)
      · linarith
    rcases lt_or_eq_of_le h_le with h_lt | h_eq
    · exact h_lt
    -- Contradiction: |round x| = bpow e is incompatible with odd witness.
    exfalso
    have h_odd_pt := round_odd_pt beta (FLT_exp emin prec) hValid x
    obtain ⟨_, h_cases⟩ := h_odd_pt
    rcases h_cases with h_eq_x | ⟨_, g, hg_F2R, hg_can, hg_odd⟩
    · -- round x = x: but then |x| = bpow e, contradicting |x| < bpow e.
      rw [← h_eq_x] at h_lo h_hi
      linarith
    · -- round x has canonical odd-numerator g. But |round x| = bpow e
      -- means |g| equals the canonical of bpow e, whose numerator is β^k
      -- (k > 0), hence even. Contradiction with g odd.
      -- Set up: canonical for bpow e is at exponent FLT_exp(e+1).
      set ee := FLT_exp emin prec (e + 1) with hee_def
      have h_ee_le_e : ee ≤ e := by
        show FLT_exp emin prec (e + 1) ≤ e
        unfold FLT_exp
        exact max_le (by linarith) (by linarith)
      have h_ee_lt_e : ee < e := by
        show FLT_exp emin prec (e + 1) < e
        unfold FLT_exp
        apply max_lt
        · linarith
        · exact Hx
      set k : ℕ := (e - ee).toNat with hk_def
      have hk_eq : (k : ℤ) = e - ee := Int.toNat_of_nonneg (by linarith)
      have hk_pos : 0 < k := by
        have : 0 < (k : ℤ) := by rw [hk_eq]; linarith
        exact_mod_cast this
      -- gg : ⟨β^k, ee⟩. F2R gg = bpow e.
      set gg : float beta := ⟨(beta.val : ℤ)^k, ee⟩ with hgg_def
      have hgg_F2R : F2R gg = bpow beta e := by
        have h_F2R : F2R gg = (((beta.val : ℤ)^k : ℤ) : ℝ) * bpow beta ee := rfl
        rw [h_F2R]
        have h_pow_cast : (((beta.val : ℤ)^k : ℤ) : ℝ) = bpow beta (k : ℤ) := by
          rw [bpow]; push_cast; rfl
        rw [h_pow_cast, ← bpow_plus]
        congr 1; omega
      have hgg_can : canonical beta (FLT_exp emin prec) gg := by
        show ee = cexp beta (FLT_exp emin prec) (F2R gg)
        rw [hgg_F2R]
        unfold cexp
        rw [mag_bpow]
      -- Fabs g has same canonical structure, equal F2R = |F2R g| = bpow e.
      have h_F2R_g_abs : |F2R g| = bpow beta e := by
        rw [← hg_F2R, h_eq]
      have hFabs_g_F2R : F2R (Fabs g) = bpow beta e := by
        rw [F2R_abs, h_F2R_g_abs]
      have hFabs_g_can : canonical beta (FLT_exp emin prec) (Fabs g) :=
        canonical_abs beta (FLT_exp emin prec) g.Fnum g.Fexp hg_can
      -- canonical_unique: Fabs g = gg.
      have h_Fabs_eq_gg : Fabs g = gg :=
        canonical_unique beta (FLT_exp emin prec) (Fabs g) gg
          hFabs_g_can hgg_can (hFabs_g_F2R.trans hgg_F2R.symm)
      -- So |g.Fnum| = β^k.
      have h_Fabs_g_Fnum : (Fabs g).Fnum = g.Fnum.natAbs := by
        show |g.Fnum| = g.Fnum.natAbs
        exact Int.abs_eq_natAbs g.Fnum
      have h_natAbs_eq : (g.Fnum.natAbs : ℤ) = (beta.val : ℤ)^k := by
        have h_Fnum_eq : (Fabs g).Fnum = gg.Fnum := by rw [h_Fabs_eq_gg]
        rw [h_Fabs_g_Fnum] at h_Fnum_eq
        exact h_Fnum_eq
      -- β^k is even (β even, k > 0).
      have h_pow_even : Even ((beta.val : ℤ)^k) := by
        rw [Int.even_pow]
        exact ⟨Even_beta, Nat.pos_iff_ne_zero.mp hk_pos⟩
      -- So g.Fnum.natAbs is even, so g.Fnum is even, contradicting hg_odd.
      apply hg_odd
      have h_natAbs_even : Even g.Fnum.natAbs := by
        have h_cast : Even (g.Fnum.natAbs : ℤ) := h_natAbs_eq ▸ h_pow_even
        exact_mod_cast h_cast
      exact (Int.natAbs_even).mp h_natAbs_even

/-- Under FLT with even radix and `prec > 1`, round-to-odd preserves the
canonical exponent of any real `x`.

In the normal regime (`emin < mag x`) this follows from `mag_round_odd`.
In the subnormal regime (`mag x ≤ emin`, `x ≠ 0`), we use the round-to-odd
characterization: round x is nonzero (either it equals x, or it has an
odd-mantissa canonical witness), so by `succ_le_lt` and `ulp_FLT_small`,
`|round x| ≥ bpow emin`; combined with `|round x| ≤ bpow emin` (from
`abs_round_le_generic` on the in-format `bpow emin`), this forces
`|round x| = bpow emin` exactly, hence `mag (round x) = emin + 1` and both
canonical exponents collapse to `emin`. -/
theorem fexp_round_odd (beta : radix) (Even_beta : Even beta.val)
    (emin prec : ℤ) (Hp1 : 1 < prec) (x : ℝ) :
    cexp beta (FLT_exp emin prec)
        (round beta (FLT_exp emin prec) Zrnd_odd x)
      = cexp beta (FLT_exp emin prec) x := by
  have Hp : 0 < prec := by linarith
  have hValid : Valid_exp (FLT_exp emin prec) := FLT_exp_valid emin prec Hp
  haveI : Exists_NE beta (FLT_exp emin prec) :=
    exists_NE_FLT beta emin prec Hp (Or.inr Hp1)
  by_cases Zx : x = 0
  · rw [Zx, round_0]
  rcases lt_or_ge emin (mag beta x) with H | H
  · -- Normal regime: `emin < mag x`. Magnitude is preserved.
    have h_mag := mag_round_odd beta Even_beta emin prec Hp1 H
    unfold cexp
    rw [h_mag]
  · -- Subnormal regime: `mag x ≤ emin`. Both `cexp` values collapse to `emin`.
    have h_cexp_x : cexp beta (FLT_exp emin prec) x = emin := by
      show FLT_exp emin prec (mag beta x) = emin
      unfold FLT_exp
      exact max_eq_right (by linarith)
    -- `round x` and its absolute value are in F.
    have hr_F : generic_format beta (FLT_exp emin prec)
        (round beta (FLT_exp emin prec) Zrnd_odd x) :=
      generic_format_round beta (FLT_exp emin prec) hValid Zrnd_odd x
    have h_abs_r_F : generic_format beta (FLT_exp emin prec)
        |round beta (FLT_exp emin prec) Zrnd_odd x| :=
      generic_format_abs beta (FLT_exp emin prec) hr_F
    -- `bpow emin` is in F.
    have h_bpow_in_F : generic_format beta (FLT_exp emin prec) (bpow beta emin) :=
      FLT_format_bpow beta emin prec Hp emin (le_refl _)
    -- `|x| < bpow emin` from `|x| < bpow (mag x) ≤ bpow emin`.
    have h_x_lt : |x| < bpow beta emin := by
      have h1 : |x| < bpow beta (mag beta x) := bpow_mag_gt beta x
      have h2 : bpow beta (mag beta x) ≤ bpow beta emin := bpow_le beta H
      linarith
    -- Upper bound: `|round x| ≤ bpow emin`.
    have h_round_le : |round beta (FLT_exp emin prec) Zrnd_odd x| ≤ bpow beta emin :=
      abs_round_le_generic beta (FLT_exp emin prec) hValid Zrnd_odd
        h_bpow_in_F (le_of_lt h_x_lt)
    -- `round x ≠ 0` from the round-to-odd characterization.
    have h_round_pt := round_odd_pt beta (FLT_exp emin prec) hValid x
    have h_round_ne_0 : round beta (FLT_exp emin prec) Zrnd_odd x ≠ 0 := by
      obtain ⟨_, h_cases⟩ := h_round_pt
      rcases h_cases with h_eq | ⟨_, g, hg_F2R, _, hg_odd⟩
      · -- `round x = x` and `x ≠ 0`.
        rw [h_eq]; exact Zx
      · -- `round x = F2R g` with odd `Fnum g`, so `Fnum g ≠ 0`, so `F2R g ≠ 0`.
        rw [hg_F2R]
        apply F2R_neq_0
        intro h_zero
        apply hg_odd
        rw [h_zero]
        exact ⟨0, by ring⟩
    have h_abs_r_pos : 0 < |round beta (FLT_exp emin prec) Zrnd_odd x| :=
      abs_pos.mpr h_round_ne_0
    -- Lower bound via `succ_le_lt`: `succ 0 ≤ |round x|`, and `succ 0 = bpow emin`
    -- in the FLT subnormal regime.
    have h_zero_F : generic_format beta (FLT_exp emin prec) 0 :=
      generic_format_0 beta (FLT_exp emin prec)
    have h_succ_le : succ beta (FLT_exp emin prec) 0
        ≤ |round beta (FLT_exp emin prec) Zrnd_odd x| :=
      succ_le_lt beta (FLT_exp emin prec) hValid h_zero_F h_abs_r_F h_abs_r_pos
    have h_succ_0_eq : succ beta (FLT_exp emin prec) 0 = bpow beta emin := by
      rw [succ_0]
      apply ulp_FLT_small beta emin prec Hp
      rw [abs_zero]
      exact bpow_gt_0 beta _
    rw [h_succ_0_eq] at h_succ_le
    -- Sandwich: `|round x| = bpow emin`.
    have h_abs_r_eq : |round beta (FLT_exp emin prec) Zrnd_odd x| = bpow beta emin :=
      le_antisymm h_round_le h_succ_le
    -- Hence `mag (round x) = emin + 1`.
    have h_mag_r : mag beta (round beta (FLT_exp emin prec) Zrnd_odd x) = emin + 1 := by
      rw [← mag_abs, h_abs_r_eq, mag_bpow]
    -- And `cexp (round x) = max(emin + 1 - prec, emin) = emin` since `prec ≥ 1`.
    have h_cexp_r : cexp beta (FLT_exp emin prec)
        (round beta (FLT_exp emin prec) Zrnd_odd x) = emin := by
      show FLT_exp emin prec
          (mag beta (round beta (FLT_exp emin prec) Zrnd_odd x)) = emin
      rw [h_mag_r]
      unfold FLT_exp
      exact max_eq_right (by linarith)
    rw [h_cexp_r, h_cexp_x]

end LeanFlocq
