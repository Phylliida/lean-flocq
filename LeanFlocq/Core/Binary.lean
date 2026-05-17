/-
Port of `flocq/src/IEEE754/Binary.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

IEEE 754 binary floating-point: the `binary_float` datatype, validity
predicates, and conversions. Parameterized over precision `prec` and
maximum exponent `emax`.

This file ports the structural part of Binary.v: the inductive types,
sign/finiteness predicates, and basic operations (negation, absolute value,
comparison). Arithmetic operations (`Bplus`, `Bmult`, etc.) live in
follow-on files since they rely on `Calc/`.

Differences from Coq:
- Coq's `positive` mantissa becomes an `ℤ` with `1 ≤ m` baked into `bounded`
  / `nan_pl`. The Lean predicates therefore include the positivity clause
  that Coq gets for free from the `positive` type.
- `Zpos (digits2_pos m)` becomes `Zdigits radix2 m`, made definitional
  by `Zdigits := mag β (n : ℝ)`.
- Validity is a `Prop`, and proof irrelevance lets us discharge
  `eqbool_irrelevance`-style obligations via `rfl`.
-/

import LeanFlocq.Core.FLT
import LeanFlocq.Core.Digits
import LeanFlocq.Core.Round_NE
import LeanFlocq.Calc.Bracket
import LeanFlocq.Calc.Round
import LeanFlocq.Calc.Operations
import LeanFlocq.Calc.Div
import LeanFlocq.Calc.Sqrt

namespace LeanFlocq

open radix (radix2)

/-! ## Section AnyRadix: full_float and FF2R -/

/-- A floating-point datum without a chosen radix: zero, infinity, NaN,
or a finite signed-mantissa-exponent pair. Mantissas (`m`, `pl`) are
intended to be strictly positive — the `valid_binary` predicate enforces
this. -/
inductive full_float where
  | F754_zero (s : Bool)
  | F754_infinity (s : Bool)
  | F754_nan (s : Bool) (pl : ℤ)
  | F754_finite (s : Bool) (m : ℤ) (e : ℤ)
  deriving DecidableEq

/-- Real value of a `full_float`. NaN/zero/infinity all map to `0`. -/
noncomputable def FF2R (beta : radix) : full_float → ℝ
  | full_float.F754_finite s m e => F2R (beta := beta) ⟨cond_Zopp s m, e⟩
  | _ => 0

/-! ## Section Binary: the IEEE-754 family -/

/-- `canonical_mantissa prec emax m e`: `e` is the canonical exponent for a
mantissa of `Zdigits` digits (in radix 2), under the FLT format with
`emin = 3 - emax - prec`. -/
def canonical_mantissa (prec emax : ℤ) (m e : ℤ) : Prop :=
  FLT_exp (3 - emax - prec) prec (Zdigits radix2 m + e) = e

/-- `bounded prec emax m e`: a finite IEEE float `(s, m, e)` is well-formed.
We bake `1 ≤ m` into the predicate (Coq gets it for free from `m : positive`). -/
def bounded (prec emax m e : ℤ) : Prop :=
  1 ≤ m ∧ canonical_mantissa prec emax m e ∧ e ≤ emax - prec

/-- `nan_pl prec pl`: a NaN payload `pl` is well-formed. We bake `1 ≤ pl`
in (Coq gets it for free from `pl : positive`). -/
def nan_pl (prec pl : ℤ) : Prop :=
  1 ≤ pl ∧ Zdigits radix2 pl < prec

/-- A `full_float` is valid for the given `(prec, emax)` parameters. -/
def valid_binary (prec emax : ℤ) : full_float → Prop
  | full_float.F754_finite _ m e => bounded prec emax m e
  | full_float.F754_nan _ pl => nan_pl prec pl
  | _ => True

/-- The IEEE-754 binary float type, parameterized by precision `prec` and
maximum exponent `emax`. -/
inductive binary_float (prec emax : ℤ) where
  | B754_zero (s : Bool) : binary_float prec emax
  | B754_infinity (s : Bool) : binary_float prec emax
  | B754_nan (s : Bool) (pl : ℤ) (h : nan_pl prec pl) : binary_float prec emax
  | B754_finite (s : Bool) (m e : ℤ) (h : bounded prec emax m e) : binary_float prec emax

namespace binary_float

variable {prec emax : ℤ}

/-- Cast `full_float → binary_float`, given a validity proof. -/
def FF2B (x : full_float) (h : valid_binary prec emax x) : binary_float prec emax :=
  match x, h with
  | full_float.F754_zero s, _ => B754_zero s
  | full_float.F754_infinity s, _ => B754_infinity s
  | full_float.F754_nan s pl, h => B754_nan s pl h
  | full_float.F754_finite s m e, h => B754_finite s m e h

/-- Cast `binary_float → full_float`. -/
def B2FF : binary_float prec emax → full_float
  | B754_zero s => full_float.F754_zero s
  | B754_infinity s => full_float.F754_infinity s
  | B754_nan s pl _ => full_float.F754_nan s pl
  | B754_finite s m e _ => full_float.F754_finite s m e

/-- Real value of a binary float. NaN/zero/infinity → `0`. Finite floats
have value `(±m) · 2^e`. -/
noncomputable def B2R : binary_float prec emax → ℝ
  | B754_finite s m e _ => F2R (beta := radix2) ⟨cond_Zopp s m, e⟩
  | _ => 0

/-! ### Conversions and round-trips -/

theorem FF2R_B2FF (x : binary_float prec emax) :
    FF2R radix2 (B2FF x) = B2R x := by
  cases x <;> rfl

theorem B2FF_FF2B (x : full_float) (h : valid_binary prec emax x) :
    B2FF (FF2B (prec := prec) (emax := emax) x h) = x := by
  cases x <;> rfl

theorem valid_binary_B2FF (x : binary_float prec emax) :
    valid_binary prec emax (B2FF x) := by
  cases x with
  | B754_zero _ => trivial
  | B754_infinity _ => trivial
  | B754_nan _ _ h => exact h
  | B754_finite _ _ _ h => exact h

theorem FF2B_B2FF (x : binary_float prec emax) (h : valid_binary prec emax (B2FF x)) :
    FF2B (B2FF x) h = x := by
  cases x <;> rfl

theorem FF2B_B2FF_valid (x : binary_float prec emax) :
    FF2B (B2FF x) (valid_binary_B2FF x) = x :=
  FF2B_B2FF x _

theorem B2R_FF2B (x : full_float) (h : valid_binary prec emax x) :
    B2R (FF2B (prec := prec) (emax := emax) x h) = FF2R radix2 x := by
  cases x <;> rfl

/-! ### Format inhabitation -/

/-- A canonical mantissa proof translates to a canonical float in the
`FLT_exp emin prec` format. -/
theorem canonical_canonical_mantissa
    (sx : Bool) (mx ex : ℤ) (h : canonical_mantissa prec emax mx ex)
    (hpos : 1 ≤ mx) :
    canonical radix2 (FLT_exp (3 - emax - prec) prec)
      (⟨cond_Zopp sx mx, ex⟩ : float radix2) := by
  unfold canonical cexp
  show ex = FLT_exp (3 - emax - prec) prec
      (mag radix2 (F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩))
  -- mx ≠ 0
  have hmx_ne : mx ≠ 0 := by linarith
  have hsigned_ne : cond_Zopp sx mx ≠ 0 := by
    cases sx <;> simp [cond_Zopp, hmx_ne]
  -- mag (F2R ⟨cond_Zopp sx mx, ex⟩) = Zdigits (cond_Zopp sx mx) + ex
  rw [mag_F2R_Zdigits (cond_Zopp sx mx) ex hsigned_ne]
  -- Zdigits (cond_Zopp sx mx) = Zdigits mx
  have h_abs : Zdigits radix2 (cond_Zopp sx mx) = Zdigits radix2 mx := by
    cases sx
    · rfl
    · show Zdigits radix2 (-mx) = Zdigits radix2 mx
      exact Zdigits_neg radix2 mx
  rw [h_abs]
  exact h.symm

/-- The real value of a binary float is in the FLT generic format. -/
theorem generic_format_B2R (x : binary_float prec emax) :
    generic_format radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) := by
  cases x with
  | B754_zero _ => exact generic_format_0 radix2 _
  | B754_infinity _ => exact generic_format_0 radix2 _
  | B754_nan _ _ _ => exact generic_format_0 radix2 _
  | B754_finite sx mx ex hb =>
    show generic_format radix2 (FLT_exp (3 - emax - prec) prec)
        (F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩)
    apply generic_format_canonical
    exact canonical_canonical_mantissa (prec := prec) (emax := emax)
      sx mx ex hb.2.1 hb.1

/-- The real value of a binary float is in the FLT format (the existential
form). Requires `0 < prec`. -/
theorem FLT_format_B2R (hp : 0 < prec) (x : binary_float prec emax) :
    FLT_format radix2 (3 - emax - prec) prec (B2R x) :=
  FLT_format_generic radix2 _ _ hp (generic_format_B2R x)

/-- `B2FF` is injective. -/
theorem B2FF_inj (x y : binary_float prec emax) (h : B2FF x = B2FF y) : x = y := by
  cases x <;> cases y <;> simp [B2FF] at h <;>
    first
    | rfl
    | (obtain ⟨_, _⟩ := h; subst_vars; rfl)
    | (obtain ⟨_, _, _⟩ := h; subst_vars; rfl)

/-! ### Strictly finite floats -/

/-- `is_finite_strict x = true` iff `x` is `B754_finite _ _ _ _` (excludes
zero, infinity, and NaN). -/
def is_finite_strict : binary_float prec emax → Bool
  | B754_finite _ _ _ _ => true
  | _ => false

/-- `B2R` is injective on strictly-finite floats. -/
theorem B2R_inj (x y : binary_float prec emax)
    (hx : is_finite_strict x = true) (hy : is_finite_strict y = true)
    (h : B2R x = B2R y) : x = y := by
  cases x with
  | B754_zero _ => simp [is_finite_strict] at hx
  | B754_infinity _ => simp [is_finite_strict] at hx
  | B754_nan _ _ _ => simp [is_finite_strict] at hx
  | B754_finite sx mx ex hbx =>
    cases y with
    | B754_zero _ => simp [is_finite_strict] at hy
    | B754_infinity _ => simp [is_finite_strict] at hy
    | B754_nan _ _ _ => simp [is_finite_strict] at hy
    | B754_finite sy my ey hby =>
      -- Both are finite. h : F2R ⟨cond_Zopp sx mx, ex⟩ = F2R ⟨cond_Zopp sy my, ey⟩.
      -- Use canonical_unique to deduce equality of (mantissa, exponent), then signs.
      have hmx_pos : 0 < mx := by linarith [hbx.1]
      have hmy_pos : 0 < my := by linarith [hby.1]
      have hcanx : canonical radix2 (FLT_exp (3 - emax - prec) prec)
          (⟨cond_Zopp sx mx, ex⟩ : float radix2) :=
        canonical_canonical_mantissa sx mx ex hbx.2.1 hbx.1
      have hcany : canonical radix2 (FLT_exp (3 - emax - prec) prec)
          (⟨cond_Zopp sy my, ey⟩ : float radix2) :=
        canonical_canonical_mantissa sy my ey hby.2.1 hby.1
      have h_eq : (⟨cond_Zopp sx mx, ex⟩ : float radix2)
          = ⟨cond_Zopp sy my, ey⟩ :=
        canonical_unique radix2 _ _ _ hcanx hcany h
      have h_mx : cond_Zopp sx mx = cond_Zopp sy my := by
        injection h_eq
      have h_ex : ex = ey := by injection h_eq
      -- Now derive sx = sy and mx = my from h_mx using positivity.
      have h_sign : sx = sy ∧ mx = my := by
        cases sx <;> cases sy <;> simp [cond_Zopp] at h_mx
        · exact ⟨rfl, h_mx⟩
        · exfalso; linarith
        · exfalso; linarith
        · exact ⟨rfl, by linarith⟩
      obtain ⟨h_sx, h_mxmy⟩ := h_sign
      subst h_sx
      subst h_mxmy
      subst h_ex
      rfl

/-! ### Sign and finiteness predicates -/

/-- Sign of a binary float. -/
def Bsign : binary_float prec emax → Bool
  | B754_zero s => s
  | B754_infinity s => s
  | B754_nan s _ _ => s
  | B754_finite s _ _ _ => s

/-- Sign of a `full_float`. -/
def sign_FF : full_float → Bool
  | full_float.F754_zero s => s
  | full_float.F754_infinity s => s
  | full_float.F754_nan s _ => s
  | full_float.F754_finite s _ _ => s

theorem Bsign_FF2B (x : full_float) (h : valid_binary prec emax x) :
    Bsign (FF2B (prec := prec) (emax := emax) x h) = sign_FF x := by
  cases x <;> rfl

/-- A binary float is finite (zero or finite). -/
def is_finite : binary_float prec emax → Bool
  | B754_zero _ => true
  | B754_finite _ _ _ _ => true
  | _ => false

/-- A `full_float` is finite (zero or finite). -/
def is_finite_FF : full_float → Bool
  | full_float.F754_zero _ => true
  | full_float.F754_finite _ _ _ => true
  | _ => false

theorem is_finite_FF2B (x : full_float) (h : valid_binary prec emax x) :
    is_finite (FF2B (prec := prec) (emax := emax) x h) = is_finite_FF x := by
  cases x <;> rfl

theorem is_finite_FF_B2FF (x : binary_float prec emax) :
    is_finite_FF (B2FF x) = is_finite x := by
  cases x <;> rfl

/-- A binary float is a NaN. -/
def is_nan : binary_float prec emax → Bool
  | B754_nan _ _ _ => true
  | _ => false

/-- A `full_float` is a NaN. -/
def is_nan_FF : full_float → Bool
  | full_float.F754_nan _ _ => true
  | _ => false

theorem is_nan_FF2B (x : full_float) (h : valid_binary prec emax x) :
    is_nan (FF2B (prec := prec) (emax := emax) x h) = is_nan_FF x := by
  cases x <;> rfl

theorem is_nan_FF_B2FF (x : binary_float prec emax) :
    is_nan_FF (B2FF x) = is_nan x := by
  cases x <;> rfl

/-- Two finite floats with the same `B2R` and the same sign are equal. The
sign condition handles the `+0` vs `-0` edge case. -/
theorem B2R_Bsign_inj (x y : binary_float prec emax)
    (hx : is_finite x = true) (hy : is_finite y = true)
    (hr : B2R x = B2R y) (hs : Bsign x = Bsign y) : x = y := by
  cases x with
  | B754_zero sx =>
    cases y with
    | B754_zero sy =>
      have : sx = sy := hs
      subst this; rfl
    | B754_infinity _ => simp [is_finite] at hy
    | B754_nan _ _ _ => simp [is_finite] at hy
    | B754_finite sy my ey hby =>
      -- B2R = 0, so F2R ⟨cond_Zopp sy my, ey⟩ = 0, hence cond_Zopp sy my = 0,
      -- hence my = 0 — contradicting bounded (1 ≤ my).
      exfalso
      have h_F2R : F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩ = 0 := hr.symm
      have h_my : cond_Zopp sy my = 0 := eq_0_F2R (beta := radix2) (e := ey) h_F2R
      have hmy : my = 0 := by
        cases sy <;> simp [cond_Zopp] at h_my
        · exact h_my
        · linarith
      have := hby.1
      omega
  | B754_infinity _ => simp [is_finite] at hx
  | B754_nan _ _ _ => simp [is_finite] at hx
  | B754_finite sx mx ex hbx =>
    cases y with
    | B754_zero sy =>
      exfalso
      have h_F2R : F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ = 0 := hr
      have h_mx : cond_Zopp sx mx = 0 := eq_0_F2R (beta := radix2) (e := ex) h_F2R
      have hmx : mx = 0 := by
        cases sx <;> simp [cond_Zopp] at h_mx
        · exact h_mx
        · linarith
      have := hbx.1
      omega
    | B754_infinity _ => simp [is_finite] at hy
    | B754_nan _ _ _ => simp [is_finite] at hy
    | B754_finite sy my ey hby =>
      exact B2R_inj _ _ rfl rfl hr

/-! ### NaN payload extraction and rebuild -/

/-- Extract the payload of a NaN, defaulting to `1` for non-NaN. -/
def get_nan_pl : binary_float prec emax → ℤ
  | B754_nan _ pl _ => pl
  | _ => 1

/-- Rebuild a NaN: given a NaN-tagged binary float, return a binary float
with the same sign and payload. (Trivial in Lean — proof irrelevance does
the work Coq's `eqbool_irrelevance` does.) -/
def build_nan : {x : binary_float prec emax // is_nan x = true} → binary_float prec emax
  | ⟨B754_nan s pl h, _⟩ => B754_nan s pl h
  | ⟨B754_zero _, hbad⟩ => absurd hbad (by simp [is_nan])
  | ⟨B754_infinity _, hbad⟩ => absurd hbad (by simp [is_nan])
  | ⟨B754_finite _ _ _ _, hbad⟩ => absurd hbad (by simp [is_nan])

theorem build_nan_correct (x : {x : binary_float prec emax // is_nan x = true}) :
    build_nan x = x.val := by
  obtain ⟨v, hv⟩ := x
  cases v with
  | B754_zero _ => simp [is_nan] at hv
  | B754_infinity _ => simp [is_nan] at hv
  | B754_finite _ _ _ _ => simp [is_nan] at hv
  | B754_nan _ _ _ => rfl

theorem B2R_build_nan (x : {x : binary_float prec emax // is_nan x = true}) :
    B2R (build_nan x) = 0 := by
  rw [build_nan_correct]
  obtain ⟨v, hv⟩ := x
  cases v with
  | B754_zero _ => rfl
  | B754_infinity _ => rfl
  | B754_finite _ _ _ _ => simp [is_nan] at hv
  | B754_nan _ _ _ => rfl

theorem is_finite_build_nan (x : {x : binary_float prec emax // is_nan x = true}) :
    is_finite (build_nan x) = false := by
  rw [build_nan_correct]
  obtain ⟨v, hv⟩ := x
  cases v with
  | B754_zero _ => simp [is_nan] at hv
  | B754_infinity _ => rfl
  | B754_finite _ _ _ _ => simp [is_nan] at hv
  | B754_nan _ _ _ => rfl

theorem is_nan_build_nan (x : {x : binary_float prec emax // is_nan x = true}) :
    is_nan (build_nan x) = true := by
  rw [build_nan_correct]
  exact x.property

/-- Erase the proof inside a binary float. Trivial in Lean: returns the
input unchanged (proof irrelevance). -/
def erase (x : binary_float prec emax) : binary_float prec emax := x

theorem erase_correct (x : binary_float prec emax) : erase x = x := rfl

/-! ### Negation -/

/-- IEEE 754 negation. The `opp_nan` argument is the NaN-propagation
policy applied to NaN inputs. -/
def Bopp (opp_nan : binary_float prec emax →
            {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | B754_zero s => B754_zero (!s)
  | B754_infinity s => B754_infinity (!s)
  | B754_finite s m e h => B754_finite (!s) m e h
  | B754_nan _ _ _ => build_nan (opp_nan x)

theorem Bopp_involutive (opp_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) (hx : is_nan x = false) :
    Bopp opp_nan (Bopp opp_nan x) = x := by
  cases x <;> simp [Bopp, Bool.not_not] <;> simp [is_nan] at hx

theorem B2R_Bopp (opp_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) :
    B2R (Bopp opp_nan x) = -(B2R x) := by
  cases x with
  | B754_zero _ => simp [Bopp, B2R]
  | B754_infinity _ => simp [Bopp, B2R]
  | B754_nan _ _ _ =>
    show B2R (build_nan (opp_nan _)) = -(B2R _)
    rw [B2R_build_nan]
    show (0 : ℝ) = -0
    ring
  | B754_finite s m e h =>
    show F2R (beta := radix2) ⟨cond_Zopp (!s) m, e⟩
        = -(F2R (beta := radix2) ⟨cond_Zopp s m, e⟩)
    cases s <;> simp [cond_Zopp]
    · show F2R (beta := radix2) ⟨-m, e⟩ = -F2R (beta := radix2) ⟨m, e⟩
      exact F2R_Zopp m e
    · show F2R (beta := radix2) ⟨m, e⟩ = -F2R (beta := radix2) ⟨-m, e⟩
      rw [F2R_Zopp]; ring

theorem is_finite_Bopp (opp_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) :
    is_finite (Bopp opp_nan x) = is_finite x := by
  cases x with
  | B754_zero _ => rfl
  | B754_infinity _ => rfl
  | B754_finite _ _ _ _ => rfl
  | B754_nan _ _ _ =>
    show is_finite (build_nan _) = _
    rw [is_finite_build_nan]
    rfl

theorem Bsign_Bopp (opp_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) (hx : is_nan x = false) :
    Bsign (Bopp opp_nan x) = !(Bsign x) := by
  cases x <;> simp [Bopp, Bsign] <;> simp [is_nan] at hx

/-! ### Absolute value -/

/-- IEEE 754 absolute value. -/
def Babs (abs_nan : binary_float prec emax →
            {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | B754_zero _ => B754_zero false
  | B754_infinity _ => B754_infinity false
  | B754_finite _ m e h => B754_finite false m e h
  | B754_nan _ _ _ => build_nan (abs_nan x)

theorem B2R_Babs (abs_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) :
    B2R (Babs abs_nan x) = |B2R x| := by
  cases x with
  | B754_zero _ => simp [Babs, B2R]
  | B754_infinity _ => simp [Babs, B2R]
  | B754_nan _ _ _ =>
    show B2R (build_nan _) = |B2R _|
    rw [B2R_build_nan]
    show (0 : ℝ) = |0|
    rw [abs_zero]
  | B754_finite s m e h =>
    show F2R (beta := radix2) ⟨cond_Zopp false m, e⟩ = |F2R (beta := radix2) ⟨cond_Zopp s m, e⟩|
    rw [show (cond_Zopp false m : ℤ) = m from rfl]
    cases s
    · show F2R (beta := radix2) ⟨m, e⟩ = |F2R (beta := radix2) ⟨m, e⟩|
      rw [abs_of_nonneg]
      exact le_of_lt (F2R_gt_0 ⟨m, e⟩ (by linarith [h.1]))
    · show F2R (beta := radix2) ⟨m, e⟩ = |F2R (beta := radix2) ⟨-m, e⟩|
      rw [F2R_Zopp, abs_neg]
      rw [abs_of_nonneg]
      exact le_of_lt (F2R_gt_0 ⟨m, e⟩ (by linarith [h.1]))

theorem is_finite_Babs (abs_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) :
    is_finite (Babs abs_nan x) = is_finite x := by
  cases x with
  | B754_zero _ => rfl
  | B754_infinity _ => rfl
  | B754_finite _ _ _ _ => rfl
  | B754_nan _ _ _ =>
    show is_finite (build_nan _) = _
    rw [is_finite_build_nan]
    rfl

theorem Bsign_Babs (abs_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) (hx : is_nan x = false) :
    Bsign (Babs abs_nan x) = false := by
  cases x <;> simp [Babs, Bsign] <;> simp [is_nan] at hx

theorem Babs_idempotent (abs_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) (hx : is_nan x = false) :
    Babs abs_nan (Babs abs_nan x) = Babs abs_nan x := by
  cases x <;> simp [Babs] <;> simp [is_nan] at hx

theorem Babs_Bopp (abs_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (opp_nan : binary_float prec emax →
        {x : binary_float prec emax // is_nan x = true})
    (x : binary_float prec emax) (hx : is_nan x = false) :
    Babs abs_nan (Bopp opp_nan x) = Babs abs_nan x := by
  cases x <;> simp [Babs, Bopp] <;> simp [is_nan] at hx

/-! ### Comparison

`Bcompare` returns `none` if either input is NaN. For `±∞` we use IEEE
ordering (`+∞ > everything finite, -∞ < everything finite`). For finite/
zero pairs we delegate to `compare` on the real values, which makes
`Bcompare_correct` essentially trivial. -/

noncomputable def Bcompare : binary_float prec emax → binary_float prec emax → Option Ordering
  | B754_nan _ _ _, _ => none
  | _, B754_nan _ _ _ => none
  | B754_infinity true, B754_infinity true => some .eq
  | B754_infinity false, B754_infinity false => some .eq
  | B754_infinity true, B754_infinity false => some .lt
  | B754_infinity false, B754_infinity true => some .gt
  | B754_infinity true, _ => some .lt
  | B754_infinity false, _ => some .gt
  | _, B754_infinity true => some .gt
  | _, B754_infinity false => some .lt
  | f1, f2 => some (compare (B2R f1) (B2R f2))

/-- Helper: real-valued `compare` is antisymmetric in this concrete sense. -/
private theorem compare_swap_real (a b : ℝ) : (compare a b).swap = compare b a := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr h]; rfl
  · subst h
    rw [compare_eq_iff_eq.mpr (rfl : a = a)]; rfl
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr h]; rfl

/-- For finite arguments, `Bcompare` agrees with `compare` on real values. -/
theorem Bcompare_correct (f1 f2 : binary_float prec emax)
    (h1 : is_finite f1 = true) (h2 : is_finite f2 = true) :
    Bcompare f1 f2 = some (compare (B2R f1) (B2R f2)) := by
  cases f1 with
  | B754_zero _ =>
    cases f2 with
    | B754_zero _ => rfl
    | B754_infinity _ => simp [is_finite] at h2
    | B754_nan _ _ _ => simp [is_finite] at h2
    | B754_finite _ _ _ _ => rfl
  | B754_infinity _ => simp [is_finite] at h1
  | B754_nan _ _ _ => simp [is_finite] at h1
  | B754_finite _ _ _ _ =>
    cases f2 with
    | B754_zero _ => rfl
    | B754_infinity _ => simp [is_finite] at h2
    | B754_nan _ _ _ => simp [is_finite] at h2
    | B754_finite _ _ _ _ => rfl

/-- Swapping arguments swaps the resulting `Ordering`. -/
theorem Bcompare_swap (x y : binary_float prec emax) :
    Bcompare y x = (Bcompare x y).map Ordering.swap := by
  cases x with
  | B754_zero _ =>
    cases y with
    | B754_zero _ =>
      show some (compare _ _) = (some (compare _ _)).map Ordering.swap
      simp [compare_swap_real]
    | B754_infinity s => cases s <;> rfl
    | B754_nan _ _ _ => rfl
    | B754_finite _ _ _ _ =>
      show some (compare _ _) = (some (compare _ _)).map Ordering.swap
      simp [compare_swap_real]
  | B754_infinity sx =>
    cases y with
    | B754_zero _ => cases sx <;> rfl
    | B754_infinity sy => cases sx <;> cases sy <;> rfl
    | B754_nan _ _ _ => cases sx <;> rfl
    | B754_finite _ _ _ _ => cases sx <;> rfl
  | B754_nan _ _ _ =>
    cases y with
    | B754_zero _ => rfl
    | B754_infinity s => cases s <;> rfl
    | B754_nan _ _ _ => rfl
    | B754_finite _ _ _ _ => rfl
  | B754_finite _ _ _ _ =>
    cases y with
    | B754_zero _ =>
      show some (compare _ _) = (some (compare _ _)).map Ordering.swap
      simp [compare_swap_real]
    | B754_infinity s => cases s <;> rfl
    | B754_nan _ _ _ => rfl
    | B754_finite _ _ _ _ =>
      show some (compare _ _) = (some (compare _ _)).map Ordering.swap
      simp [compare_swap_real]

/-! ### Boundedness theorems -/

/-- A bounded float satisfies `F2R ⟨m, e⟩ < β^emax`. -/
theorem bounded_lt_emax (hp : 0 < prec) (hmax : prec < emax)
    (mx ex : ℤ) (hb : bounded prec emax mx ex) :
    F2R (beta := radix2) ⟨mx, ex⟩ < bpow radix2 emax := by
  -- mx ≥ 1, so F2R is positive
  have hmx_pos : 0 < mx := by linarith [hb.1]
  have hmx_ne : mx ≠ 0 := by linarith
  have h_F2R_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ hmx_pos
  -- |F2R| < bpow (mag F2R)
  have h_lt_mag : |F2R (beta := radix2) ⟨mx, ex⟩| < bpow radix2 (mag radix2 _) :=
    bpow_mag_gt radix2 _
  rw [abs_of_pos h_F2R_pos] at h_lt_mag
  -- mag F2R = Zdigits mx + ex
  rw [mag_F2R_Zdigits mx ex hmx_ne] at h_lt_mag
  -- Need: bpow (Zdigits mx + ex) ≤ bpow emax, then linarith.
  -- From canonical_mantissa: fexp(Zdigits mx + ex) = ex
  --   → max(Zdigits mx + ex - prec, emin) = ex
  -- From bounded: ex ≤ emax - prec
  -- Case split on which max wins.
  have hcm : FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex) = ex := hb.2.1
  have hex_le : ex ≤ emax - prec := hb.2.2
  have h_zd_pos : 0 < Zdigits radix2 mx := Zdigits_gt_0 radix2 hmx_ne
  unfold FLT_exp at hcm
  -- max(k - prec, emin) = ex, where k = Zdigits mx + ex
  set k := Zdigits radix2 mx + ex with hk_def
  have h_zde : Zdigits radix2 mx + ex ≤ emax := by
    -- max (k - prec) emin = ex
    rcases max_cases (k - prec) (3 - emax - prec) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- k - prec is the max, equal to ex
      rw [h1] at hcm
      -- k - prec = ex, so k = ex + prec. With ex ≤ emax - prec: k ≤ emax.
      omega
    · -- emin is the max, equal to ex
      rw [h1] at hcm
      -- ex = emin = 3 - emax - prec; and k - prec ≤ emin (from h2 reversed).
      -- So k ≤ emin + prec = 3 - emax. Hence k < emax.
      -- Actually h2 is `k - prec ≤ 3 - emax - prec` (max_cases gives ≤ for non-winner).
      omega
  exact lt_of_lt_of_le h_lt_mag (bpow_le radix2 h_zde)

/-- A bounded float satisfies `β^emin ≤ F2R ⟨m, e⟩` (where `emin = 3 - emax - prec`). -/
theorem bounded_ge_emin (hp : 0 < prec)
    (mx ex : ℤ) (hb : bounded prec emax mx ex) :
    bpow radix2 (3 - emax - prec) ≤ F2R (beta := radix2) ⟨mx, ex⟩ := by
  have hmx_pos : 0 < mx := by linarith [hb.1]
  have hmx_ne : mx ≠ 0 := by linarith
  have h_F2R_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ hmx_pos
  have h_F2R_ne : F2R (beta := radix2) ⟨mx, ex⟩ ≠ 0 := ne_of_gt h_F2R_pos
  -- bpow (mag F2R - 1) ≤ |F2R|
  have h_low : bpow radix2 (mag radix2 _ - 1) ≤ |F2R (beta := radix2) ⟨mx, ex⟩| :=
    bpow_mag_le radix2 h_F2R_ne
  rw [abs_of_pos h_F2R_pos] at h_low
  rw [mag_F2R_Zdigits mx ex hmx_ne] at h_low
  -- Need: emin ≤ Zdigits mx + ex - 1
  have hcm : FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex) = ex := hb.2.1
  have h_zd_pos : 0 < Zdigits radix2 mx := Zdigits_gt_0 radix2 hmx_ne
  unfold FLT_exp at hcm
  set k := Zdigits radix2 mx + ex with hk_def
  have h_emin_le : 3 - emax - prec ≤ k - 1 := by
    rcases max_cases (k - prec) (3 - emax - prec) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- k - prec wins, = ex. So ex ≥ emin (from h2: emin ≤ k - prec = ex).
      -- k - 1 = ex + prec - 1 ≥ emin + prec - 1 ≥ emin.
      omega
    · -- emin wins, = ex. Zdigits mx ≥ 1 → k = Zd + emin ≥ 1 + emin > emin → k - 1 ≥ emin.
      omega
  exact le_trans (bpow_le radix2 h_emin_le) h_low

/-- The absolute value of a binary float is bounded by `β^emax`. -/
theorem abs_B2R_lt_emax (hp : 0 < prec) (hmax : prec < emax)
    (x : binary_float prec emax) :
    |B2R x| < bpow radix2 emax := by
  cases x with
  | B754_zero _ => simp [B2R, abs_zero]; exact bpow_gt_0 radix2 _
  | B754_infinity _ => simp [B2R, abs_zero]; exact bpow_gt_0 radix2 _
  | B754_nan _ _ _ => simp [B2R, abs_zero]; exact bpow_gt_0 radix2 _
  | B754_finite sx mx ex hb =>
    show |F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩| < bpow radix2 emax
    have h_abs : |F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩|
        = F2R (beta := radix2) ⟨mx, ex⟩ := by
      cases sx
      · show |F2R (beta := radix2) ⟨mx, ex⟩| = F2R (beta := radix2) ⟨mx, ex⟩
        rw [abs_of_nonneg]
        exact le_of_lt (F2R_gt_0 ⟨mx, ex⟩ (by linarith [hb.1]))
      · show |F2R (beta := radix2) ⟨-mx, ex⟩| = F2R (beta := radix2) ⟨mx, ex⟩
        rw [F2R_Zopp, abs_neg, abs_of_nonneg]
        exact le_of_lt (F2R_gt_0 ⟨mx, ex⟩ (by linarith [hb.1]))
    rw [h_abs]
    exact bounded_lt_emax hp hmax mx ex hb

/-- For a strictly-finite float, `|B2R x| ≥ β^emin`. -/
theorem abs_B2R_ge_emin (hp : 0 < prec) (x : binary_float prec emax)
    (h_finite : is_finite_strict x = true) :
    bpow radix2 (3 - emax - prec) ≤ |B2R x| := by
  cases x with
  | B754_zero _ => simp [is_finite_strict] at h_finite
  | B754_infinity _ => simp [is_finite_strict] at h_finite
  | B754_nan _ _ _ => simp [is_finite_strict] at h_finite
  | B754_finite sx mx ex hb =>
    show bpow radix2 (3 - emax - prec) ≤ |F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩|
    have h_abs : |F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩|
        = F2R (beta := radix2) ⟨mx, ex⟩ := by
      cases sx
      · show |F2R (beta := radix2) ⟨mx, ex⟩| = F2R (beta := radix2) ⟨mx, ex⟩
        rw [abs_of_nonneg]
        exact le_of_lt (F2R_gt_0 ⟨mx, ex⟩ (by linarith [hb.1]))
      · show |F2R (beta := radix2) ⟨-mx, ex⟩| = F2R (beta := radix2) ⟨mx, ex⟩
        rw [F2R_Zopp, abs_neg, abs_of_nonneg]
        exact le_of_lt (F2R_gt_0 ⟨mx, ex⟩ (by linarith [hb.1]))
    rw [h_abs]
    exact bounded_ge_emin hp mx ex hb

/-- A canonical float with absolute value below `β^emax` is bounded. -/
theorem bounded_canonical_lt_emax (hp : 0 < prec) (hmax : prec < emax)
    (mx ex : ℤ) (hpos : 1 ≤ mx)
    (hcan : canonical radix2 (FLT_exp (3 - emax - prec) prec)
              (⟨mx, ex⟩ : float radix2))
    (hlt : F2R (beta := radix2) ⟨mx, ex⟩ < bpow radix2 emax) :
    bounded prec emax mx ex := by
  refine ⟨hpos, ?_, ?_⟩
  · -- canonical_mantissa: fexp(Zdigits mx + ex) = ex
    unfold canonical_mantissa
    unfold canonical at hcan
    simp only at hcan
    -- hcan : ex = cexp radix2 (FLT_exp ...) (F2R ⟨mx, ex⟩)
    -- = FLT_exp ... (mag (F2R ⟨mx, ex⟩))
    -- = FLT_exp ... (Zdigits mx + ex)
    have hmx_ne : mx ≠ 0 := by linarith
    rw [show cexp radix2 (FLT_exp (3 - emax - prec) prec)
            (F2R (beta := radix2) ⟨mx, ex⟩)
        = FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex) from by
      unfold cexp
      rw [mag_F2R_Zdigits mx ex hmx_ne]] at hcan
    exact hcan.symm
  · -- ex ≤ emax - prec
    unfold canonical at hcan
    simp only at hcan
    -- ex = FLT_exp(mag F2R) = max(mag F2R - prec, emin)
    unfold cexp FLT_exp at hcan
    have hmx_ne : mx ≠ 0 := by linarith
    have hmx_pos : 0 < mx := by linarith
    have h_F2R_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ hmx_pos
    have h_F2R_ne : F2R (beta := radix2) ⟨mx, ex⟩ ≠ 0 := ne_of_gt h_F2R_pos
    -- |F2R| < bpow emax → mag F2R ≤ emax
    have hmag_le : mag radix2 (F2R (beta := radix2) ⟨mx, ex⟩) ≤ emax := by
      apply mag_le_bpow radix2 h_F2R_ne
      rwa [abs_of_pos h_F2R_pos]
    -- ex = max(mag - prec, emin) ≤ max(emax - prec, 3 - emax - prec)
    -- = emax - prec (since emax - prec > 0 > 3 - emax - prec when prec < emax and emax ≥ 1)
    rw [hcan]
    apply max_le
    · linarith
    · linarith

/-! ### Rounding modes

The five IEEE 754 rounding modes. `choice_mode` and `binary_round_aux` —
which require the `loc_of_shr_record` / `Bracket` infrastructure — are
deferred until after `Calc/` is ported. -/

inductive mode where
  | mode_NE  -- round to nearest, ties to even
  | mode_ZR  -- round toward zero (truncation)
  | mode_DN  -- round toward −∞ (floor)
  | mode_UP  -- round toward +∞ (ceil)
  | mode_NA  -- round to nearest, ties away from zero
  deriving DecidableEq

/-- The integer-valued rounding function for each mode. -/
noncomputable def round_mode (m : mode) : ℝ → ℤ :=
  match m with
  | .mode_NE => ZnearestE
  | .mode_ZR => Ztrunc
  | .mode_DN => fun x => ⌊x⌋
  | .mode_UP => fun x => ⌈x⌉
  | .mode_NA => ZnearestA

/-- Every IEEE rounding mode gives a `Valid_rnd`. -/
instance valid_rnd_round_mode (m : mode) : Valid_rnd (round_mode m) := by
  cases m <;> unfold round_mode <;> infer_instance

/-- `choice_mode m sx mx lx`: given a rounding mode `m`, a sign bit `sx`,
a mantissa `mx`, and the location `lx` of the true value within `[mx, mx+1)`,
return the rounded mantissa. -/
def choice_mode (m : mode) (sx : Bool) (mx : ℤ) (lx : location) : ℤ :=
  match m with
  | .mode_NE => cond_incr (round_N (decide (¬ Even mx)) lx) mx
  | .mode_ZR => mx
  | .mode_DN => cond_incr (round_sign_DN sx lx) mx
  | .mode_UP => cond_incr (round_sign_UP sx lx) mx
  | .mode_NA => cond_incr (round_N true lx) mx

/-- `overflow_to_inf m s`: under mode `m` and sign `s`, does an overflow round
to `±∞` (`true`) or saturate to the maximum finite (`false`)? -/
def overflow_to_inf (m : mode) (s : Bool) : Bool :=
  match m with
  | .mode_NE => true
  | .mode_NA => true
  | .mode_ZR => false
  | .mode_UP => !s
  | .mode_DN => s

/-- `binary_overflow prec emax m s`: the `full_float` produced by an overflow
under mode `m` with sign `s`. Either `±∞` or `±max_float = ±(2^prec−1)·2^(emax−prec)`. -/
def binary_overflow (prec emax : ℤ) (m : mode) (s : Bool) : full_float :=
  if overflow_to_inf m s then full_float.F754_infinity s
  else full_float.F754_finite s (2 ^ prec.toNat - 1) (emax - prec)

/-- For each rounding mode, `round_mode m` paired with `choice_mode m`
satisfies the `inbetween_int_valid` shape required by
`round_trunc_sign_any_correct'`: given a bracketing of `|x|` between integers
`mx` and `mx+1` with location `l`, the integer-rounded value is the
sign-flipped `choice_mode` result. -/
theorem inbetween_int_valid_round_mode (m : mode) (x : ℝ) (mx : ℤ)
    (l : location) (hin : inbetween_int mx |x| l) :
    round_mode m x =
      cond_Zopp (decide (x < 0))
        (choice_mode m (decide (x < 0)) mx l) := by
  cases m with
  | mode_NE => exact inbetween_int_NE_sign hin
  | mode_ZR => exact inbetween_int_ZR_sign hin
  | mode_DN => exact inbetween_int_DN_sign hin
  | mode_UP => exact inbetween_int_UP_sign hin
  | mode_NA => exact inbetween_int_NA_sign hin

end binary_float

/-! ### Truncation: shr_record

A "round-and-sticky" record carrying a mantissa `m`, a round bit `r`, and a
sticky bit `s`. The pair `(r, s)` encodes a 4-way location classification:
`(false, false) = Exact`, `(false, true) = Inexact Lt`,
`(true, false) = Inexact Eq` (i.e., exactly halfway), and
`(true, true) = Inexact Gt`. `shr_1` halves `m` (toward zero), shifts the
old `r` into the new `s`, and writes the dropped bit into the new `r`. -/

structure shr_record where
  m : ℤ
  r : Bool
  s : Bool
  deriving DecidableEq

namespace shr_record

/-- Shift right by 1: halve `m` toward zero, write the dropped bit into the
new round bit, and shift the old round bit into the sticky bit. -/
def shr_1 (mrs : shr_record) : shr_record :=
  let s' := mrs.r || mrs.s
  if mrs.m = 0 then ⟨0, false, s'⟩
  else
    let r' := decide (mrs.m % 2 ≠ 0)
    ⟨mrs.m / 2, r', s'⟩

/-- Decode a `shr_record` into the corresponding `location`. -/
def loc_of_shr_record (mrs : shr_record) : location :=
  match mrs with
  | ⟨_, false, false⟩ => location.Exact
  | ⟨_, false, true⟩ => location.Inexact .lt
  | ⟨_, true, false⟩ => location.Inexact .eq
  | ⟨_, true, true⟩ => location.Inexact .gt

/-- Build a `shr_record` from a mantissa and location. -/
def shr_record_of_loc (m : ℤ) (l : location) : shr_record :=
  match l with
  | location.Exact => ⟨m, false, false⟩
  | location.Inexact .lt => ⟨m, false, true⟩
  | location.Inexact .eq => ⟨m, true, false⟩
  | location.Inexact .gt => ⟨m, true, true⟩

theorem m_shr_record_of_loc (m : ℤ) (l : location) :
    (shr_record_of_loc m l).m = m := by
  cases l with
  | Exact => rfl
  | Inexact c => cases c <;> rfl

/-- Alias matching Coq's `shr_m_shr_record_of_loc`. -/
theorem shr_m_shr_record_of_loc (m : ℤ) (l : location) :
    (shr_record_of_loc m l).m = m :=
  m_shr_record_of_loc m l

theorem loc_of_shr_record_of_loc (m : ℤ) (l : location) :
    loc_of_shr_record (shr_record_of_loc m l) = l := by
  cases l with
  | Exact => rfl
  | Inexact c => cases c <;> rfl

/-- Iterate `shr_1` `n` times (treating non-positive `n` as no-op), adjusting
the exponent accordingly. Returns the new `shr_record` and new exponent. -/
def shr (mrs : shr_record) (e n : ℤ) : shr_record × ℤ :=
  if 0 < n then (shr_1^[n.toNat] mrs, e + n) else (mrs, e)

/-- `shr_1` preserves the `inbetween_float` invariant: if `x` lies between
floats with mantissa `m = mrs.m` and `m + 1` at exponent `e` with location
`loc_of_shr_record mrs`, then it also lies between floats with mantissa
`(shr_1 mrs).m` and `(shr_1 mrs).m + 1` at exponent `e + 1` with location
`loc_of_shr_record (shr_1 mrs)`. Requires `mrs.m ≥ 0`. -/
theorem inbetween_shr_1 (mrs : shr_record) (e : ℤ) (x : ℝ)
    (Hm : 0 ≤ mrs.m)
    (Hl : inbetween_float radix2 mrs.m e x (loc_of_shr_record mrs)) :
    inbetween_float radix2 (shr_1 mrs).m (e + 1) x (loc_of_shr_record (shr_1 mrs)) := by
  -- Notation
  set m := mrs.m with hm_def
  set m' := (shr_1 mrs).m with hm'_def
  -- Key arithmetic: m' = m / 2, with parity tracked in r
  have h_radix2 : (radix2 : radix).val = 2 := rfl
  have h_step_pos : (0 : ℝ) < bpow radix2 e := bpow_gt_0 _ _
  have h_2_pos : (0 : ℝ) < 2 := by norm_num
  -- bpow (e+1) = 2 * bpow e
  have h_bpow_e1 : bpow radix2 (e + 1) = 2 * bpow radix2 e := by
    rw [bpow_plus]
    have h1 : bpow radix2 (1 : ℤ) = 2 := by
      show ((radix2 : radix).val : ℝ) ^ (1 : ℤ) = 2
      rw [zpow_one, h_radix2]; norm_num
    rw [h1]; ring
  -- Define the "start" of the new interval
  -- F2R ⟨m', e+1⟩ = m' * 2 * bpow e
  have h_F2R_start : F2R (beta := radix2) ⟨m', e + 1⟩ = (m' : ℝ) * 2 * bpow radix2 e := by
    show (m' : ℝ) * bpow radix2 (e + 1) = (m' : ℝ) * 2 * bpow radix2 e
    rw [h_bpow_e1]; ring
  -- F2R ⟨m'+1, e+1⟩ = (m'+1) * 2 * bpow e = m'*2*bpow e + 2 * bpow e
  have h_F2R_end : F2R (beta := radix2) ⟨m' + 1, e + 1⟩
      = (m' : ℝ) * 2 * bpow radix2 e + 2 * bpow radix2 e := by
    show ((m' + 1 : ℤ) : ℝ) * bpow radix2 (e + 1)
      = (m' : ℝ) * 2 * bpow radix2 e + 2 * bpow radix2 e
    rw [h_bpow_e1]
    push_cast; ring
  -- F2R ⟨m, e⟩ = m * bpow e
  have h_F2R_m : F2R (beta := radix2) ⟨m, e⟩ = (m : ℝ) * bpow radix2 e := rfl
  have h_F2R_m1 : F2R (beta := radix2) ⟨m + 1, e⟩ = ((m + 1 : ℤ) : ℝ) * bpow radix2 e := rfl
  -- Key relation: m = 2 * m' + (if r_new then 1 else 0)
  -- And (shr_1 mrs).r tracks the parity of mrs.m (when mrs.m ≠ 0)
  -- Case split on m = 0 vs m > 0
  rcases eq_or_lt_of_le Hm with Hm_eq | Hm_pos
  · -- m = 0 case
    have hm0 : m = 0 := Hm_eq.symm
    -- shr_1 mrs = ⟨0, false, mrs.r || mrs.s⟩
    have h_shr1 : shr_1 mrs = ⟨0, false, mrs.r || mrs.s⟩ := by
      show shr_1 mrs = _
      unfold shr_1
      rw [if_pos hm0]
    have hm'0 : m' = 0 := by rw [hm'_def, h_shr1]
    -- Subcase: original location
    unfold inbetween_float at Hl ⊢
    rw [hm0] at Hl
    rw [hm'0]
    -- Goal: inbetween (F2R ⟨0, e+1⟩) (F2R ⟨0+1, e+1⟩) x (loc_of_shr_record (shr_1 mrs))
    -- Have Hl : inbetween (F2R ⟨0, e⟩) (F2R ⟨0+1, e⟩) x (loc_of_shr_record mrs)
    -- F2R ⟨0, e⟩ = 0 = F2R ⟨0, e+1⟩
    -- F2R ⟨1, e⟩ = bpow e, F2R ⟨1, e+1⟩ = 2 * bpow e
    have h_F2R_0e : F2R (beta := radix2) ⟨(0 : ℤ), e⟩ = 0 := by
      show ((0 : ℤ) : ℝ) * bpow radix2 e = 0; simp
    have h_F2R_0e1 : F2R (beta := radix2) ⟨(0 : ℤ), e + 1⟩ = 0 := by
      show ((0 : ℤ) : ℝ) * bpow radix2 (e + 1) = 0; simp
    have h_F2R_1e : F2R (beta := radix2) ⟨(0 + 1 : ℤ), e⟩ = bpow radix2 e := by
      show ((0 + 1 : ℤ) : ℝ) * bpow radix2 e = bpow radix2 e
      push_cast; ring
    have h_F2R_1e1 : F2R (beta := radix2) ⟨(0 + 1 : ℤ), e + 1⟩ = 2 * bpow radix2 e := by
      show ((0 + 1 : ℤ) : ℝ) * bpow radix2 (e + 1) = 2 * bpow radix2 e
      rw [h_bpow_e1]; push_cast; ring
    rw [h_F2R_0e] at Hl
    rw [h_F2R_1e] at Hl
    rw [h_F2R_0e1, h_F2R_1e1]
    -- Apply new_location_even_correct with start = 0, step = bpow e, nb_steps = 2, k = 0
    have h_new := new_location_even_correct (start := 0) (step := bpow radix2 e) h_step_pos
      (nb_steps := 2) (by norm_num) (by norm_num : (2 : ℤ) % 2 = 0)
      x 0 (loc_of_shr_record mrs) ⟨le_refl _, by norm_num⟩
      (by
        have h1 : (0 : ℝ) + ((0 : ℤ) : ℝ) * bpow radix2 e = 0 := by push_cast; ring
        have h2 : (0 : ℝ) + (((0 + 1) : ℤ) : ℝ) * bpow radix2 e = bpow radix2 e := by
          push_cast; ring
        rw [h1, h2]; exact Hl)
    have h_target : (0 : ℝ) + ((2 : ℤ) : ℝ) * bpow radix2 e = 2 * bpow radix2 e := by
      push_cast; ring
    rw [h_target] at h_new
    -- new_location_even 2 0 l simplifies; show equals loc_of_shr_record (shr_1 mrs)
    -- shr_1 mrs has r = false, s = mrs.r || mrs.s
    -- loc_of_shr_record (shr_1 mrs):
    --   if mrs.r || mrs.s = false → Exact
    --   if mrs.r || mrs.s = true → Inexact .lt
    -- new_location_even 2 0 l:
    --   k = 0 branch: if l = Exact then Exact else Inexact .lt
    -- These match iff: loc_of_shr_record mrs = Exact iff mrs.r || mrs.s = false
    have h_match : new_location_even 2 0 (loc_of_shr_record mrs)
        = loc_of_shr_record (shr_1 mrs) := by
      rw [h_shr1]
      unfold new_location_even loc_of_shr_record
      simp only [if_pos rfl]
      obtain ⟨_, r, s⟩ := mrs
      cases r <;> cases s <;> rfl
    rw [h_match] at h_new
    exact h_new
  · -- m > 0 case
    have hm_ne : m ≠ 0 := ne_of_gt Hm_pos
    -- shr_1 mrs = ⟨m / 2, m % 2 ≠ 0, mrs.r || mrs.s⟩
    have h_shr1 : shr_1 mrs = ⟨m / 2, decide (m % 2 ≠ 0), mrs.r || mrs.s⟩ := by
      show shr_1 mrs = _
      unfold shr_1
      rw [if_neg hm_ne]
    have hm'_eq : m' = m / 2 := by rw [hm'_def, h_shr1]
    -- Parity split
    by_cases h_par : m % 2 = 0
    · -- m even: m = 2 * (m/2), shr_1.r = false
      have h_m_eq : m = 2 * m' := by
        rw [hm'_eq]
        omega
      have h_shr1' : shr_1 mrs = ⟨m', false, mrs.r || mrs.s⟩ := by
        rw [h_shr1, hm'_eq]
        congr 1
        simp [h_par]
      unfold inbetween_float at Hl ⊢
      rw [h_F2R_start, h_F2R_end]
      -- F2R ⟨m, e⟩ = (2 m') * bpow e = start + 0 * step
      -- F2R ⟨m+1, e⟩ = (2m'+1) * bpow e = start + 1 * step
      have h_Hl1 : F2R (beta := radix2) ⟨m, e⟩
          = (m' : ℝ) * 2 * bpow radix2 e + ((0 : ℤ) : ℝ) * bpow radix2 e := by
        show (m : ℝ) * bpow radix2 e
          = (m' : ℝ) * 2 * bpow radix2 e + ((0 : ℤ) : ℝ) * bpow radix2 e
        rw [show (m : ℝ) = 2 * m' from by exact_mod_cast h_m_eq]
        push_cast; ring
      have h_Hl2 : F2R (beta := radix2) ⟨m + 1, e⟩
          = (m' : ℝ) * 2 * bpow radix2 e + ((0 + 1 : ℤ) : ℝ) * bpow radix2 e := by
        show ((m + 1 : ℤ) : ℝ) * bpow radix2 e
          = (m' : ℝ) * 2 * bpow radix2 e + ((0 + 1 : ℤ) : ℝ) * bpow radix2 e
        rw [show ((m + 1 : ℤ) : ℝ) = 2 * m' + 1 from by exact_mod_cast (by omega : m + 1 = 2 * m' + 1)]
        push_cast; ring
      rw [h_Hl1, h_Hl2] at Hl
      have h_new := new_location_even_correct
        (start := (m' : ℝ) * 2 * bpow radix2 e) (step := bpow radix2 e) h_step_pos
        (nb_steps := 2) (by norm_num) (by norm_num : (2 : ℤ) % 2 = 0)
        x 0 (loc_of_shr_record mrs) ⟨le_refl _, by norm_num⟩ Hl
      have h_target : (m' : ℝ) * 2 * bpow radix2 e + ((2 : ℤ) : ℝ) * bpow radix2 e
          = (m' : ℝ) * 2 * bpow radix2 e + 2 * bpow radix2 e := by push_cast; ring
      rw [h_target] at h_new
      have h_match : new_location_even 2 0 (loc_of_shr_record mrs)
          = loc_of_shr_record (shr_1 mrs) := by
        rw [h_shr1']
        unfold new_location_even loc_of_shr_record
        simp only [if_pos rfl]
        obtain ⟨_, r, s⟩ := mrs
        cases r <;> cases s <;> rfl
      rw [h_match] at h_new
      exact h_new
    · -- m odd: m = 2 * (m/2) + 1, shr_1.r = true
      have h_par' : m % 2 = 1 := by omega
      have h_m_eq : m = 2 * m' + 1 := by
        rw [hm'_eq]
        omega
      have h_shr1' : shr_1 mrs = ⟨m', true, mrs.r || mrs.s⟩ := by
        rw [h_shr1, hm'_eq]
        congr 1
        simp [h_par']
      unfold inbetween_float at Hl ⊢
      rw [h_F2R_start, h_F2R_end]
      have h_Hl1 : F2R (beta := radix2) ⟨m, e⟩
          = (m' : ℝ) * 2 * bpow radix2 e + ((1 : ℤ) : ℝ) * bpow radix2 e := by
        show (m : ℝ) * bpow radix2 e
          = (m' : ℝ) * 2 * bpow radix2 e + ((1 : ℤ) : ℝ) * bpow radix2 e
        rw [show (m : ℝ) = 2 * m' + 1 from by exact_mod_cast h_m_eq]
        push_cast; ring
      have h_Hl2 : F2R (beta := radix2) ⟨m + 1, e⟩
          = (m' : ℝ) * 2 * bpow radix2 e + ((1 + 1 : ℤ) : ℝ) * bpow radix2 e := by
        show ((m + 1 : ℤ) : ℝ) * bpow radix2 e
          = (m' : ℝ) * 2 * bpow radix2 e + ((1 + 1 : ℤ) : ℝ) * bpow radix2 e
        rw [show ((m + 1 : ℤ) : ℝ) = 2 * m' + 2 from by exact_mod_cast (by omega : m + 1 = 2 * m' + 2)]
        push_cast; ring
      rw [h_Hl1, h_Hl2] at Hl
      have h_new := new_location_even_correct
        (start := (m' : ℝ) * 2 * bpow radix2 e) (step := bpow radix2 e) h_step_pos
        (nb_steps := 2) (by norm_num) (by norm_num : (2 : ℤ) % 2 = 0)
        x 1 (loc_of_shr_record mrs) ⟨by norm_num, by norm_num⟩ Hl
      have h_target : (m' : ℝ) * 2 * bpow radix2 e + ((2 : ℤ) : ℝ) * bpow radix2 e
          = (m' : ℝ) * 2 * bpow radix2 e + 2 * bpow radix2 e := by push_cast; ring
      rw [h_target] at h_new
      have h_match : new_location_even 2 1 (loc_of_shr_record mrs)
          = loc_of_shr_record (shr_1 mrs) := by
        rw [h_shr1']
        unfold new_location_even loc_of_shr_record
        simp only [if_neg (by norm_num : (1 : ℤ) ≠ 0)]
        have h_cmp : compare (2 * (1 : ℤ)) 2 = .eq := by decide
        rw [h_cmp]
        obtain ⟨_, r, s⟩ := mrs
        cases r <;> cases s <;> rfl
      rw [h_match] at h_new
      exact h_new

/-- `shr_1` preserves `0 ≤ m`. -/
theorem shr_1_nonneg (mrs : shr_record) (Hm : 0 ≤ mrs.m) :
    0 ≤ (shr_1 mrs).m := by
  unfold shr_1
  split_ifs with h
  · exact le_refl _
  · show 0 ≤ mrs.m / 2
    exact Int.ediv_nonneg Hm (by norm_num)

/-- Iterating `shr_1` preserves `0 ≤ m`. -/
theorem shr_1_iter_nonneg (mrs : shr_record) (n : ℕ) (Hm : 0 ≤ mrs.m) :
    0 ≤ (shr_1^[n] mrs).m := by
  induction n with
  | zero => exact Hm
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact shr_1_nonneg _ ih

/-- Iterating `shr_1` preserves the `inbetween_float` invariant. -/
theorem inbetween_shr_iter (mrs : shr_record) (e : ℤ) (x : ℝ) (n : ℕ)
    (Hm : 0 ≤ mrs.m)
    (Hl : inbetween_float radix2 mrs.m e x (loc_of_shr_record mrs)) :
    inbetween_float radix2 (shr_1^[n] mrs).m (e + n) x
      (loc_of_shr_record (shr_1^[n] mrs)) := by
  induction n with
  | zero =>
    show inbetween_float radix2 mrs.m (e + (0 : ℕ)) x (loc_of_shr_record mrs)
    have h_eq : (e + (0 : ℕ) : ℤ) = e := by push_cast; ring
    rw [h_eq]; exact Hl
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    have h_nonneg : 0 ≤ (shr_1^[k] mrs).m := shr_1_iter_nonneg mrs k Hm
    have h_step := inbetween_shr_1 (shr_1^[k] mrs) (e + k) x h_nonneg ih
    have h_eq : e + k + 1 = e + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [← h_eq]; exact h_step

/-- `inbetween_shr`: the `shr` iteration preserves the `inbetween_float`
invariant when starting from `shr_record_of_loc m l`. -/
theorem inbetween_shr (x : ℝ) (m e : ℤ) (l : location) (n : ℤ)
    (Hm : 0 ≤ m)
    (Hl : inbetween_float radix2 m e x l) :
    let (mrs, e') := shr (shr_record_of_loc m l) e n
    inbetween_float radix2 mrs.m e' x (loc_of_shr_record mrs) := by
  unfold shr
  by_cases hn : 0 < n
  · rw [if_pos hn]
    show inbetween_float radix2 (shr_1^[n.toNat] (shr_record_of_loc m l)).m (e + n) x
      (loc_of_shr_record (shr_1^[n.toNat] (shr_record_of_loc m l)))
    have h_Hm' : 0 ≤ (shr_record_of_loc m l).m := by
      rw [m_shr_record_of_loc]; exact Hm
    have h_Hl' : inbetween_float radix2 (shr_record_of_loc m l).m e x
        (loc_of_shr_record (shr_record_of_loc m l)) := by
      rw [m_shr_record_of_loc, loc_of_shr_record_of_loc]
      exact Hl
    have h_iter := inbetween_shr_iter (shr_record_of_loc m l) e x n.toNat h_Hm' h_Hl'
    have h_eq : (e + (n.toNat : ℤ) : ℤ) = e + n := by
      have : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (le_of_lt hn)
      rw [this]
    rw [h_eq] at h_iter
    exact h_iter
  · rw [if_neg hn]
    show inbetween_float radix2 (shr_record_of_loc m l).m e x
      (loc_of_shr_record (shr_record_of_loc m l))
    rw [m_shr_record_of_loc, loc_of_shr_record_of_loc]
    exact Hl

/-- Round-trip: rebuilding a `shr_record` from its `m` and its decoded
location gives back the original. -/
theorem shr_record_of_loc_m_l (mrs : shr_record) :
    shr_record_of_loc mrs.m (loc_of_shr_record mrs) = mrs := by
  obtain ⟨_, r, s⟩ := mrs
  cases r <;> cases s <;> rfl

/-- `shr_fexp fexp m e l`: build a `shr_record` from `(m, l)` and shift it
to the canonical exponent `fexp(Zdigits₂ m + e)`. This is the bridge between
the location-bracketed form `(m, e, l)` and the IEEE-style round-and-sticky
form used by `binary_round_aux`. -/
noncomputable def shr_fexp (fexp : ℤ → ℤ) (m e : ℤ) (l : location) :
    shr_record × ℤ :=
  shr (shr_record_of_loc m l) e (fexp (Zdigits radix2 m + e) - e)

/-- **`shr_truncate`**: the round-and-sticky form `shr_fexp` agrees with
the `(m, e, l) → (m', e', l')` truncation from `Calc/Round.lean`, up to the
location-encoding round trip. -/
theorem shr_truncate (fexp : ℤ → ℤ) (hValid : Valid_exp fexp) (m e : ℤ)
    (l : location) (Hm : 0 ≤ m) :
    shr_fexp fexp m e l =
      (shr_record_of_loc (truncate radix2 fexp (m, e, l)).1
         (truncate radix2 fexp (m, e, l)).2.2,
       (truncate radix2 fexp (m, e, l)).2.1) := by
  -- The key quantity: how much we shift by.
  set k : ℤ := fexp (Zdigits radix2 m + e) - e with hk_def
  -- Unfold shr_fexp
  show shr (shr_record_of_loc m l) e k =
      (shr_record_of_loc (truncate radix2 fexp (m, e, l)).1
         (truncate radix2 fexp (m, e, l)).2.2,
       (truncate radix2 fexp (m, e, l)).2.1)
  rcases lt_or_ge 0 k with hk_pos | hk_nonpos
  · -- k > 0: both sides shift
    -- LHS: shr (shr_record_of_loc m l) e k = (shr_1^[k.toNat] _, e + k)
    have h_lhs : shr (shr_record_of_loc m l) e k
        = (shr_1^[k.toNat] (shr_record_of_loc m l), e + k) := by
      unfold shr; rw [if_pos hk_pos]
    -- RHS: truncate goes through the if_pos branch
    have h_rhs : truncate radix2 fexp (m, e, l) = truncate_aux radix2 k (m, e, l) := by
      unfold truncate
      show (if 0 < fexp (Zdigits radix2 (m, e, l).1 + (m, e, l).2.1) - (m, e, l).2.1
            then truncate_aux radix2 _ (m, e, l) else (m, e, l))
            = truncate_aux radix2 k (m, e, l)
      rw [show ((m, e, l).1 : ℤ) = m from rfl, show ((m, e, l).2.1 : ℤ) = e from rfl,
          show fexp (Zdigits radix2 m + e) - e = k from hk_def.symm]
      rw [if_pos hk_pos]
    -- Use inbetween_float_ex to obtain a witness x
    obtain ⟨x, Hx⟩ := inbetween_float_ex (beta := radix2) m e l
    -- 0 ≤ x: from inbetween_float_bounds and 0 ≤ m
    have h_x_nonneg : 0 ≤ x := by
      have ⟨h_lo, _⟩ := inbetween_float_bounds (beta := radix2) m e x l Hx
      have h_F2R_nonneg : 0 ≤ F2R (beta := radix2) ⟨m, e⟩ := F2R_ge_0 ⟨m, e⟩ Hm
      linarith
    -- He: e ≤ fexp(Zdigits + e) (since k > 0)
    have hHe : e ≤ fexp (Zdigits radix2 m + e) := by omega
    -- Apply inbetween_shr on the LHS side
    have h_inb_shr : let p := shr (shr_record_of_loc m l) e k
                     inbetween_float radix2 p.1.m p.2 x (loc_of_shr_record p.1) :=
      inbetween_shr x m e l k Hm Hx
    rw [h_lhs] at h_inb_shr
    -- Apply truncate_correct on the RHS side
    have h_tc := truncate_correct radix2 fexp hValid h_x_nonneg Hx (Or.inl hHe)
    -- h_tc.1 : inbetween_float radix2 t.1 t.2.1 x t.2.2  where t = truncate ...
    have h_inb_tr : inbetween_float radix2
        (truncate radix2 fexp (m, e, l)).1
        (truncate radix2 fexp (m, e, l)).2.1
        x
        (truncate radix2 fexp (m, e, l)).2.2 := h_tc.1
    -- The exponents match: e + k = (truncate ...).2.1
    have h_exp_eq : (truncate radix2 fexp (m, e, l)).2.1 = e + k := by
      rw [h_rhs]; show e + k = e + k; rfl
    -- Combine: both inbetween_float at same exponent e + k
    rw [h_exp_eq] at h_inb_tr
    -- Uniqueness: m and l components match
    obtain ⟨h_m_eq, h_l_eq⟩ := inbetween_float_unique (beta := radix2)
      (e + k) _ _ _ _ x h_inb_shr h_inb_tr
    -- Conclude
    rw [h_lhs]
    ext
    · -- The shr_record component
      show shr_1^[k.toNat] (shr_record_of_loc m l)
        = shr_record_of_loc (truncate radix2 fexp (m, e, l)).1
            (truncate radix2 fexp (m, e, l)).2.2
      rw [← h_m_eq, ← h_l_eq]
      exact (shr_record_of_loc_m_l _).symm
    · -- The exponent component
      show e + k = (truncate radix2 fexp (m, e, l)).2.1
      exact h_exp_eq.symm
  · -- k ≤ 0: neither side shifts
    have h_not_pos : ¬ 0 < k := not_lt.mpr hk_nonpos
    -- LHS: shr (shr_record_of_loc m l) e k = (shr_record_of_loc m l, e)
    have h_lhs : shr (shr_record_of_loc m l) e k = (shr_record_of_loc m l, e) := by
      unfold shr; rw [if_neg h_not_pos]
    -- RHS: truncate = (m, e, l)
    have h_rhs : truncate radix2 fexp (m, e, l) = (m, e, l) := by
      unfold truncate
      show (if 0 < fexp (Zdigits radix2 (m, e, l).1 + (m, e, l).2.1) - (m, e, l).2.1
            then truncate_aux radix2 _ (m, e, l) else (m, e, l))
            = (m, e, l)
      rw [show ((m, e, l).1 : ℤ) = m from rfl, show ((m, e, l).2.1 : ℤ) = e from rfl,
          show fexp (Zdigits radix2 m + e) - e = k from hk_def.symm]
      rw [if_neg h_not_pos]
    rw [h_lhs, h_rhs]

end shr_record

namespace binary_float

/-- **`binary_round_aux`**: the IEEE-754 rounding kernel. Given a rounding
mode, a sign bit, a mantissa `mx`, an exponent `ex`, and the location `lx`
of the true value within `[mx·β^ex, (mx+1)·β^ex)`, produce the IEEE-754
`full_float` representing the rounded result.

The kernel works in three steps:
1. `shr_fexp` shifts `(mx, ex, lx)` down to the canonical exponent under
   `FLT_exp (3 - emax - prec) prec`, accumulating the round-and-sticky
   bits into the resulting `shr_record`.
2. `choice_mode` consumes the round/sticky encoding (via
   `loc_of_shr_record`) and rounds the mantissa per the mode.
3. A second `shr_fexp` re-normalizes after the round (which may have
   carried into a higher exponent).

The result is then classified: zero, finite (if the exponent fits in
`[emin, emax - prec]`), or overflow (handled by `binary_overflow`). The
negative-mantissa branch is unreachable post-truncation; we emit a dummy
NaN there. -/
noncomputable def binary_round_aux (prec emax : ℤ) (m : mode)
    (sx : Bool) (mx ex : ℤ) (lx : location) : full_float :=
  let fexp := FLT_exp (3 - emax - prec) prec
  let mrs_e := shr_record.shr_fexp fexp mx ex lx
  let mrs' := mrs_e.1
  let e' := mrs_e.2
  let mx2 := choice_mode m sx mrs'.m (shr_record.loc_of_shr_record mrs')
  let mrs_e2 := shr_record.shr_fexp fexp mx2 e' location.Exact
  let mrs'' := mrs_e2.1
  let e'' := mrs_e2.2
  match mrs''.m with
  | Int.ofNat 0 => full_float.F754_zero sx
  | Int.ofNat (n + 1) =>
      if e'' ≤ emax - prec
      then full_float.F754_finite sx (Int.ofNat (n + 1)) e''
      else binary_overflow prec emax m sx
  | Int.negSucc _ => full_float.F754_nan false 1

/-- **`binary_round_aux_correct'`** (Coq lines 974–1154): the IEEE-754
rounding-kernel correctness theorem.

Given a nonzero real `x` bracketed by `[mx·2^ex, (mx+1)·2^ex)` with location
`lx`, and with `ex` no larger than the canonical exponent of `x` under
`FLT_exp (3 - emax - prec) prec`, the result of `binary_round_aux`:

* is always a valid `binary_float`;
* if `|round x|` fits in the `[0, β^emax)` range, equals the rounded value
  (as `FF2R`), is finite, and has sign `decide (x < 0)`;
* otherwise equals the canonical `binary_overflow` (which is either `±∞`
  or the maximum finite float, per `overflow_to_inf`).

The conditional structure is delicate: the post-rounding mantissa may carry
into a higher exponent and push the result over `bpow emax`. -/
theorem binary_round_aux_correct' (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (x : ℝ) (mx ex : ℤ) (lx : location)
    (Px : x ≠ 0)
    (Bx : inbetween_float radix2 mx ex |x| lx)
    (Ex : ex ≤ cexp radix2 (FLT_exp (3 - emax - prec) prec) x) :
    let z := binary_round_aux prec emax m (decide (x < 0)) mx ex lx
    valid_binary prec emax z ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax then
      FF2R radix2 z = round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ∧
      is_finite_FF z = true ∧
      sign_FF z = decide (x < 0)
    else
      z = binary_overflow prec emax m (decide (x < 0))) := by
  intro z
  -- Abbreviate `fexp` as a Lean `let` (not `set`, since the unfolding of
  -- `binary_round_aux` introduces its own internal `have fexp := ...` that
  -- a `set` reverse-rewrite would conflict with).
  let fexp : ℤ → ℤ := FLT_exp (3 - emax - prec) prec
  have hValid : Valid_exp fexp := FLT_exp_valid (3 - emax - prec) prec hp
  -- Expand `z` everywhere in the goal so subsequent rewrites propagate to
  -- all occurrences (FF2R z, is_finite_FF z, sign_FF z, etc.).
  show valid_binary prec emax
      (binary_round_aux prec emax m (decide (x < 0)) mx ex lx) ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax then
      FF2R radix2 (binary_round_aux prec emax m (decide (x < 0)) mx ex lx) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ∧
      is_finite_FF (binary_round_aux prec emax m (decide (x < 0)) mx ex lx) = true ∧
      sign_FF (binary_round_aux prec emax m (decide (x < 0)) mx ex lx) = decide (x < 0)
    else
      binary_round_aux prec emax m (decide (x < 0)) mx ex lx =
        binary_overflow prec emax m (decide (x < 0)))
  -- `0 ≤ mx` follows from the bracket: |x| < F2R⟨mx+1, ex⟩ and |x| ≥ 0.
  have Hmx : 0 ≤ mx := by
    have hbounds := inbetween_float_bounds (beta := radix2) mx ex |x| lx Bx
    have hpos : 0 < F2R (beta := radix2) ⟨mx + 1, ex⟩ :=
      lt_of_le_of_lt (abs_nonneg x) hbounds.2
    have hmx_succ_pos : 0 < mx + 1 := gt_0_F2R (beta := radix2) (m := mx + 1) (e := ex) hpos
    omega
  -- The truncate result and its three components.
  set T := truncate radix2 fexp (mx, ex, lx) with hT_def
  set m1 := T.1 with hm1_def
  set e1 := T.2.1 with he1_def
  set l1 := T.2.2 with hl1_def
  -- The post-rounding mantissa.
  set m1' := choice_mode m (decide (x < 0)) m1 l1 with hm1'_def
  -- The abstract correctness equation: round x = F2R⟨sign-flipped m1', e1⟩.
  have Hround : round radix2 fexp (round_mode m) x =
      F2R (beta := radix2) ⟨cond_Zopp (decide (x < 0)) m1', e1⟩ := by
    have := round_trunc_sign_any_correct' (beta := radix2) (fexp := fexp)
      (round_mode m) (choice_mode m)
      (fun y mxy lxy hin => inbetween_int_valid_round_mode m y mxy lxy hin)
      hValid Bx (Or.inl Ex)
    exact this
  -- The truncate-after-bracket fact: m1, e1, l1 bracket |x| at the canonical
  -- exponent for |x|.
  have Hpartial : inbetween_float radix2 m1 e1 |x| l1 ∧ e1 = cexp radix2 fexp |x| := by
    have h := truncate_correct_partial' (beta := radix2) (fexp := fexp) hValid
      (abs_pos.mpr Px) Bx (by rw [cexp_abs]; exact Ex)
    exact h
  obtain ⟨H1a, H1b⟩ := Hpartial
  -- m1 ≤ m1': every mode's choice_mode either preserves m1 or adds 1.
  have Hm_le : m1 ≤ m1' := by
    show m1 ≤ choice_mode m (decide (x < 0)) m1 l1
    cases m <;> simp only [choice_mode, cond_incr] <;>
      first | (split_ifs <;> omega) | omega
  -- 0 ≤ m1 (truncate preserves nonneg, via inbetween_float_bounds on |x|).
  have Hm1_nonneg : 0 ≤ m1 := by
    have hb := inbetween_float_bounds (beta := radix2) m1 e1 |x| l1 H1a
    have hpos : 0 < F2R (beta := radix2) ⟨m1 + 1, e1⟩ :=
      lt_of_le_of_lt (abs_nonneg x) hb.2
    have hm1_succ_pos : 0 < m1 + 1 :=
      gt_0_F2R (beta := radix2) (m := m1 + 1) (e := e1) hpos
    omega
  -- Hence 0 ≤ m1'.
  have Hm1'_nonneg : 0 ≤ m1' := le_trans Hm1_nonneg Hm_le
  -- Drive the goal: unfold binary_round_aux via simp (which also β/ζ-reduces
  -- the internal lets, exposing the actual shr_fexp calls).
  simp only [binary_round_aux]
  -- Rewrite the first shr_fexp using shr_truncate.
  rw [shr_record.shr_truncate (FLT_exp (3 - emax - prec) prec) hValid mx ex lx Hmx,
      shr_record.m_shr_record_of_loc,
      shr_record.loc_of_shr_record_of_loc]
  -- Apply shr_truncate to the second shr_fexp.
  rw [shr_record.shr_truncate (FLT_exp (3 - emax - prec) prec) hValid m1' e1
        location.Exact Hm1'_nonneg,
      shr_record.m_shr_record_of_loc]
  -- Case split on m1' = 0 vs m1' > 0 (the negSucc branch is unreachable since
  -- m1' ≥ 0, and likewise post-truncate the mantissa stays ≥ 0).
  rcases eq_or_lt_of_le Hm1'_nonneg with h_zero | h_pos
  · -- ===== Case m1' = 0 =====
    -- truncate (0, e1, Exact).1 = 0, so the match hits F754_zero.
    have h_trunc_zero :
        (truncate radix2 (FLT_exp (3 - emax - prec) prec)
           (m1', e1, location.Exact)).1 = 0 := by
      rw [← h_zero]; exact truncate_0 radix2 (FLT_exp (3 - emax - prec) prec)
        e1 location.Exact
    rw [h_trunc_zero]
    -- round x = F2R⟨cond_Zopp sx 0, e1⟩ = 0
    have h_round_zero :
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x = 0 := by
      rw [Hround, ← h_zero]
      show F2R (beta := radix2) ⟨cond_Zopp (decide (x < 0)) 0, e1⟩ = 0
      cases decide (x < 0) <;> simp [cond_Zopp, F2R_0]
    -- |round x| < bpow emax (since |round x| = 0)
    have h_abs_lt : |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax := by
      rw [h_round_zero, abs_zero]; exact bpow_gt_0 radix2 _
    -- Conclude: valid F754_zero, and the if-true branch gives the three facts.
    refine ⟨trivial, ?_⟩
    rw [if_pos h_abs_lt]
    refine ⟨?_, rfl, rfl⟩
    -- FF2R F754_zero = 0 = round x
    show FF2R radix2 (full_float.F754_zero (decide (x < 0))) =
      round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x
    rw [h_round_zero]; rfl
  · -- ===== Case m1' > 0 =====
    -- |round x| = F2R⟨m1', e1⟩ (from Hround + sign-absorbing |cond_Zopp _ m1'| = m1').
    have h_abs_round : |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        = F2R (beta := radix2) ⟨m1', e1⟩ := by
      have h_abs_cond : |cond_Zopp (decide (x < 0)) m1'| = m1' := by
        cases hd : decide (x < 0)
        · show |m1'| = m1'; exact abs_of_nonneg Hm1'_nonneg
        · show |(-m1')| = m1'; rw [abs_neg]; exact abs_of_nonneg Hm1'_nonneg
      rw [Hround, ← F2R_Zabs]
      show F2R (beta := radix2) ⟨|cond_Zopp (decide (x < 0)) m1'|, e1⟩
        = F2R (beta := radix2) ⟨m1', e1⟩
      rw [h_abs_cond]
    -- 0 < F2R⟨m1', e1⟩, hence round x ≠ 0.
    have h_F2R_pos : 0 < F2R (beta := radix2) ⟨m1', e1⟩ :=
      F2R_gt_0 ⟨m1', e1⟩ h_pos
    have h_round_ne :
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ≠ 0 := by
      intro hr0
      have : |(0 : ℝ)| = F2R (beta := radix2) ⟨m1', e1⟩ := by
        rw [← hr0]; exact h_abs_round
      rw [abs_zero] at this
      exact ne_of_gt h_F2R_pos this.symm
    -- F2R⟨m1', e1⟩ ∈ generic_format.
    have h_F2R_fmt :
        generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (F2R (beta := radix2) ⟨m1', e1⟩) := by
      rw [← h_abs_round]
      exact generic_format_abs radix2 (FLT_exp (3 - emax - prec) prec)
        (generic_format_round radix2 (FLT_exp (3 - emax - prec) prec) hValid
          (round_mode m) x)
    -- e1 ≤ fexp(Zdigits m1' + e1) — via cexp_round_ge + H1b + mag rewrite.
    have h_mag_F2R : mag radix2 (F2R (beta := radix2) ⟨m1', e1⟩)
                   = Zdigits radix2 m1' + e1 :=
      mag_F2R_Zdigits m1' e1 (ne_of_gt h_pos)
    have h_e1_le_fexp :
        e1 ≤ FLT_exp (3 - emax - prec) prec (Zdigits radix2 m1' + e1) := by
      have h_cexp_round :
          cexp radix2 (FLT_exp (3 - emax - prec) prec) x ≤
          cexp radix2 (FLT_exp (3 - emax - prec) prec)
            (round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x) :=
        cexp_round_ge radix2 (FLT_exp (3 - emax - prec) prec) hValid
          (FLT_exp_monotone (3 - emax - prec) prec) (round_mode m) h_round_ne
      calc e1
          = cexp radix2 (FLT_exp (3 - emax - prec) prec) x := by
              rw [H1b, cexp_abs]
        _ ≤ cexp radix2 (FLT_exp (3 - emax - prec) prec)
              (round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x) :=
              h_cexp_round
        _ = cexp radix2 (FLT_exp (3 - emax - prec) prec)
              |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x| :=
              (cexp_abs radix2 _ _).symm
        _ = FLT_exp (3 - emax - prec) prec
              (mag radix2 |round radix2 (FLT_exp (3 - emax - prec) prec)
                (round_mode m) x|) := rfl
        _ = FLT_exp (3 - emax - prec) prec
              (mag radix2 (F2R (beta := radix2) ⟨m1', e1⟩)) := by rw [h_abs_round]
        _ = FLT_exp (3 - emax - prec) prec (Zdigits radix2 m1' + e1) := by
              rw [h_mag_F2R]
    -- Apply truncate_correct_format: get F2R-eq + cexp-eq for the truncate result.
    have h_tcf := truncate_correct_format
      (beta := radix2) (fexp := FLT_exp (3 - emax - prec) prec)
      (m := m1') (e := e1) (ne_of_gt h_pos) h_F2R_fmt h_e1_le_fexp
    obtain ⟨H3, H4⟩ := h_tcf
    -- Name the truncate result components.
    set m2 := (truncate radix2 (FLT_exp (3 - emax - prec) prec)
                (m1', e1, location.Exact)).1 with hm2_def
    set e2 := (truncate radix2 (FLT_exp (3 - emax - prec) prec)
                (m1', e1, location.Exact)).2.1 with he2_def
    -- 0 < m2 (since F2R⟨m2, e2⟩ = F2R⟨m1', e1⟩ > 0).
    have h_m2_pos : 0 < m2 := by
      apply gt_0_F2R (beta := radix2) (m := m2) (e := e2)
      rw [← H3]; exact h_F2R_pos
    -- Express m2 = Int.ofNat (k + 1).
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m2 = Int.ofNat (k + 1) := by
      refine ⟨(m2 - 1).toNat, ?_⟩
      have hpos1 : 0 ≤ m2 - 1 := by linarith
      have hcast : ((m2 - 1).toNat : ℤ) = m2 - 1 := Int.toNat_of_nonneg hpos1
      show m2 = ((m2 - 1).toNat + 1 : ℤ)
      push_cast [hcast]; ring
    -- Canonical mantissa fact: FLT_exp(Zdigits m2 + e2) = e2.
    -- Derived from H4 (e2 = cexp F2R⟨m1', e1⟩) and mag(F2R⟨m2,e2⟩) = Zdigits m2 + e2
    -- bridged via H3 (F2R⟨m1', e1⟩ = F2R⟨m2, e2⟩).
    have hm2_ne : m2 ≠ 0 := ne_of_gt h_m2_pos
    have h_mag2 : mag radix2 (F2R (beta := radix2) ⟨m2, e2⟩)
                = Zdigits radix2 m2 + e2 :=
      mag_F2R_Zdigits m2 e2 hm2_ne
    have h_canonical_eq :
        FLT_exp (3 - emax - prec) prec (Zdigits radix2 m2 + e2) = e2 := by
      have h_cexp_F2R :
          cexp radix2 (FLT_exp (3 - emax - prec) prec)
              (F2R (beta := radix2) ⟨m1', e1⟩)
          = FLT_exp (3 - emax - prec) prec (Zdigits radix2 m2 + e2) := by
        show FLT_exp (3 - emax - prec) prec
              (mag radix2 (F2R (beta := radix2) ⟨m1', e1⟩))
            = FLT_exp (3 - emax - prec) prec (Zdigits radix2 m2 + e2)
        rw [H3, h_mag2]
      rw [← h_cexp_F2R, ← H4]
    -- Fire the right match branch, and reduce the pair projection.
    rw [hk]
    simp only []
    -- Case split on e2 ≤ emax - prec.
    by_cases h_e2_le : e2 ≤ emax - prec
    · -- ===== Bounded sub-case (|round x| < bpow emax) =====
      rw [if_pos h_e2_le]
      -- The result is F754_finite (decide (x<0)) (Int.ofNat (k+1)) e2.
      -- Build bounded, then conclude all three facts of the Rlt_bool true branch.
      have h_bnd : bounded prec emax (Int.ofNat (k + 1)) e2 := by
        refine ⟨?_, ?_, h_e2_le⟩
        · -- 1 ≤ Int.ofNat (k+1) — trivial.
          show (1 : ℤ) ≤ Int.ofNat (k + 1); omega
        · -- canonical_mantissa: FLT_exp(Zdigits (Int.ofNat (k+1)) + e2) = e2.
          show FLT_exp (3 - emax - prec) prec
              (Zdigits radix2 (Int.ofNat (k + 1)) + e2) = e2
          rw [← hk]; exact h_canonical_eq
      refine ⟨h_bnd, ?_⟩
      -- |round x| < bpow emax via bounded_lt_emax.
      have h_abs_lt :
          |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
          < bpow radix2 emax := by
        rw [h_abs_round, H3]
        exact bounded_lt_emax (prec := prec) (emax := emax) hp hmax m2 e2
          (by rw [hk]; exact h_bnd)
      rw [if_pos h_abs_lt]
      refine ⟨?_, rfl, rfl⟩
      -- FF2R (F754_finite sx (k+1) e2) = round x.
      show F2R (beta := radix2) ⟨cond_Zopp (decide (x < 0)) (Int.ofNat (k + 1)), e2⟩
        = round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x
      rw [Hround, ← hk, F2R_cond_Zopp, F2R_cond_Zopp, H3]
    · -- ===== Overflow sub-case (|round x| ≥ bpow emax) =====
      rw [if_neg h_e2_le]
      -- The match arm becomes `binary_overflow prec emax m sx`.
      -- The outer `if |round x| < bpow emax` lands on the FALSE branch,
      -- because if it were true, `bounded_canonical_lt_emax` would give
      -- us `bounded m2 e2`, whose third conjunct is `e2 ≤ emax - prec` —
      -- contradicting our case.
      have h_abs_ge :
          ¬ |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
              < bpow radix2 emax := by
        intro h_lt
        have h_F2R_lt : F2R (beta := radix2) ⟨m2, e2⟩ < bpow radix2 emax := by
          rw [← H3, ← h_abs_round]; exact h_lt
        have h_canon : canonical radix2 (FLT_exp (3 - emax - prec) prec)
            (⟨m2, e2⟩ : float radix2) := by
          show e2 = cexp radix2 (FLT_exp (3 - emax - prec) prec)
              (F2R (beta := radix2) ⟨m2, e2⟩)
          show e2 = FLT_exp (3 - emax - prec) prec
              (mag radix2 (F2R (beta := radix2) ⟨m2, e2⟩))
          rw [h_mag2]; exact h_canonical_eq.symm
        have h_bnd_m2 : bounded prec emax m2 e2 :=
          bounded_canonical_lt_emax hp hmax m2 e2 h_m2_pos h_canon h_F2R_lt
        exact h_e2_le h_bnd_m2.2.2
      rw [if_neg h_abs_ge]
      refine ⟨?_, rfl⟩
      -- valid_binary (binary_overflow) — case on overflow_to_inf.
      unfold binary_overflow
      by_cases h_oti : overflow_to_inf m (decide (x < 0)) = true
      · -- True: F754_infinity, valid_binary = True.
        rw [if_pos h_oti]; trivial
      · -- False: F754_finite sx (2^prec - 1) (emax - prec) — need bounded.
        rw [if_neg h_oti]
        show bounded prec emax (2 ^ prec.toNat - 1) (emax - prec)
        -- Useful fact: prec.toNat ≥ 1 (since 0 < prec).
        have h_prec_toNat : 1 ≤ prec.toNat := by omega
        -- (2 : ℤ) ^ prec.toNat ≥ 2
        have h_pow_ge_2 : (2 : ℤ) ≤ 2 ^ prec.toNat := by
          calc (2 : ℤ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ prec.toNat :=
              pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_prec_toNat
        -- (2 : ℤ) ^ prec.toNat - 1 ≥ 1
        have h_mant_ge_1 : 1 ≤ (2 : ℤ) ^ prec.toNat - 1 := by linarith
        -- Zdigits radix2 (2^prec - 1) = prec, via Zdigits_unique.
        have h_zd : Zdigits radix2 (2 ^ prec.toNat - 1) = prec := by
          apply Zdigits_unique radix2
          · -- bpow (prec - 1) ≤ |((2 ^ prec.toNat - 1 : ℤ) : ℝ)|
            -- |x| = x since x ≥ 1 > 0
            have h_abs : |((2 ^ prec.toNat - 1 : ℤ) : ℝ)|
                      = ((2 ^ prec.toNat - 1 : ℤ) : ℝ) := by
              apply abs_of_pos
              exact_mod_cast (by linarith : (0 : ℤ) < 2 ^ prec.toNat - 1)
            rw [h_abs]
            -- bpow radix2 (prec - 1) = ((2 ^ (prec - 1).toNat : ℤ) : ℝ)
            have h_prec_sub_nn : 0 ≤ prec - 1 := by
              have : 1 ≤ prec := hp
              linarith
            rw [show bpow radix2 (prec - 1)
                = ((2 ^ (prec - 1).toNat : ℤ) : ℝ) from
                  (IZR_Zpower radix2 h_prec_sub_nn).symm]
            -- (prec - 1).toNat = prec.toNat - 1 (since prec ≥ 1)
            have h_tn_sub : (prec - 1).toNat = prec.toNat - 1 := by
              omega
            rw [h_tn_sub]
            -- Show: 2 ^ (prec.toNat - 1) ≤ 2 ^ prec.toNat - 1 (as reals).
            have h_nat : ((2 : ℤ) ^ (prec.toNat - 1) : ℤ) ≤ 2 ^ prec.toNat - 1 := by
              set n := prec.toNat - 1 with hn_def
              have hN : prec.toNat = n + 1 := by omega
              rw [hN, pow_succ]
              -- Goal: 2 ^ n ≤ 2 ^ n * 2 - 1
              have h_pos : (1 : ℤ) ≤ 2 ^ n :=
                calc (1 : ℤ) = 2 ^ 0 := by norm_num
                  _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
              linarith
            exact_mod_cast h_nat
          · -- |((2 ^ prec.toNat - 1 : ℤ) : ℝ)| < bpow radix2 prec
            have h_abs : |((2 ^ prec.toNat - 1 : ℤ) : ℝ)|
                      = ((2 ^ prec.toNat - 1 : ℤ) : ℝ) := by
              apply abs_of_pos
              exact_mod_cast (by linarith : (0 : ℤ) < 2 ^ prec.toNat - 1)
            rw [h_abs]
            have h_prec_nn : 0 ≤ prec := le_of_lt hp
            rw [show bpow radix2 prec = ((2 ^ prec.toNat : ℤ) : ℝ) from
                  (IZR_Zpower radix2 h_prec_nn).symm]
            exact_mod_cast (by linarith : (2 ^ prec.toNat - 1 : ℤ) < 2 ^ prec.toNat)
        refine ⟨h_mant_ge_1, ?_, le_refl _⟩
        show FLT_exp (3 - emax - prec) prec
            (Zdigits radix2 (2 ^ prec.toNat - 1) + (emax - prec)) = emax - prec
        rw [h_zd]
        -- FLT_exp (emin) prec (prec + (emax - prec)) = FLT_exp emin prec emax
        --   = max (emax - prec) (3 - emax - prec)
        --   = emax - prec (since emax ≥ 2)
        show FLT_exp (3 - emax - prec) prec (prec + (emax - prec)) = emax - prec
        have h_simp : prec + (emax - prec) = emax := by ring
        rw [h_simp]
        unfold FLT_exp
        -- max (emax - prec) (3 - emax - prec) = emax - prec.
        -- Need: 3 - emax - prec ≤ emax - prec, i.e., 2*emax ≥ 3, i.e., emax ≥ 2.
        have h_emax_ge_2 : 2 ≤ emax := by linarith
        exact max_eq_left (by linarith)

/-- **`binary_round_aux_correct`** (Coq lines 1156–1329): the positive-mantissa
specialization of `binary_round_aux_correct'`.

When `mx > 0` and `|x|` is bracketed by `[mx·2^ex, (mx+1)·2^ex)`, the result of
`binary_round_aux` has the same correctness behavior as the generic primed
version. The Zdigits-form precondition `ex ≤ FLT_exp(Zdigits mx + ex)` is
equivalent to `ex ≤ cexp x` here (via `cexp_inbetween_float`), and `x ≠ 0` is
derivable from the positive lower bound `F2R⟨mx, ex⟩ ≤ |x|`. -/
theorem binary_round_aux_correct (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (x : ℝ) (mx ex : ℤ) (lx : location)
    (hmx : 0 < mx)
    (Bx : inbetween_float radix2 mx ex |x| lx)
    (Ex : ex ≤ FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex)) :
    let z := binary_round_aux prec emax m (decide (x < 0)) mx ex lx
    valid_binary prec emax z ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax then
      FF2R radix2 z = round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ∧
      is_finite_FF z = true ∧
      sign_FF z = decide (x < 0)
    else
      z = binary_overflow prec emax m (decide (x < 0))) := by
  intro z
  let fexp : ℤ → ℤ := FLT_exp (3 - emax - prec) prec
  have hValid : Valid_exp fexp := FLT_exp_valid (3 - emax - prec) prec hp
  -- 0 < |x|: from F2R⟨mx, ex⟩ ≤ |x| and F2R⟨mx, ex⟩ > 0 (since mx > 0).
  have h_abs_pos : 0 < |x| := by
    have hbounds := inbetween_float_bounds (beta := radix2) mx ex |x| lx Bx
    have h_F2R_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ :=
      F2R_gt_0 (⟨mx, ex⟩ : float radix2) hmx
    linarith
  -- Hence x ≠ 0.
  have Px : x ≠ 0 := by
    intro hx
    rw [hx, abs_zero] at h_abs_pos
    exact lt_irrefl _ h_abs_pos
  -- Convert the Zdigits-form precondition to `ex ≤ cexp x` via
  -- `cexp_inbetween_float` applied to `|x|`, then `cexp_abs`.
  have h_cexp_abs : cexp radix2 fexp |x| = fexp (Zdigits radix2 mx + ex) :=
    cexp_inbetween_float radix2 fexp hValid h_abs_pos Bx (Or.inr Ex)
  have h_cexp_eq : cexp radix2 fexp x = fexp (Zdigits radix2 mx + ex) := by
    rw [← cexp_abs radix2 fexp x]; exact h_cexp_abs
  have Ex' : ex ≤ cexp radix2 fexp x := by rw [h_cexp_eq]; exact Ex
  -- Apply the primed version.
  exact binary_round_aux_correct' hp hmax m x mx ex lx Px Bx Ex'

/-! ## Multiplication -/

/-- The technical exponent bound used by `Bmult_correct_aux`: if both `(mx, ex)`
and `(my, ey)` are `bounded`, then the product exponent `ex + ey` is no larger
than `FLT_exp(Zdigits(mx * my) + ex + ey)`. Coq inlines this with a single
`omega` once `FLT_exp` is unfolded. -/
theorem bounded_mult_exp_le (hp : 0 < prec) (hmax : prec < emax)
    (mx ex my ey : ℤ) (Hx : bounded prec emax mx ex) (Hy : bounded prec emax my ey) :
    ex + ey ≤ FLT_exp (3 - emax - prec) prec
      (Zdigits radix2 (mx * my) + (ex + ey)) := by
  obtain ⟨h_mx_pos, h_mx_canon, _⟩ := Hx
  obtain ⟨h_my_pos, h_my_canon, _⟩ := Hy
  have h_mx_ne : mx ≠ 0 := by linarith
  have h_my_ne : my ≠ 0 := by linarith
  have h_zd_mx_pos : 0 < Zdigits radix2 mx := Zdigits_gt_0 radix2 h_mx_ne
  have h_zd_my_pos : 0 < Zdigits radix2 my := Zdigits_gt_0 radix2 h_my_ne
  have h_zd_mult : Zdigits radix2 mx + Zdigits radix2 my - 1
                  ≤ Zdigits radix2 (mx * my) := Zdigits_mult_ge radix2 h_mx_ne h_my_ne
  -- Unfold canonical_mantissa and FLT_exp; then omega handles the max arithmetic.
  unfold canonical_mantissa FLT_exp at h_mx_canon h_my_canon
  unfold FLT_exp
  simp only [max_def] at h_mx_canon h_my_canon ⊢
  split_ifs at h_mx_canon h_my_canon ⊢ <;> omega

/-- **`Bmult_correct_aux`** (Coq lines 1333–1384): the rounding-kernel
correctness statement for the product of two finite bounded floats. Reduces to
`binary_round_aux_correct` applied to the product mantissa `mx * my` with
exponent `ex + ey` and exact location. -/
theorem Bmult_correct_aux (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (sx : Bool) (mx ex : ℤ) (Hx : bounded prec emax mx ex)
    (sy : Bool) (my ey : ℤ) (Hy : bounded prec emax my ey) :
    let x := F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
    let y := F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩
    let z := binary_round_aux prec emax m (xor sx sy) (mx * my) (ex + ey)
              location.Exact
    valid_binary prec emax z ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (x * y)|
        < bpow radix2 emax then
      FF2R radix2 z =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (x * y) ∧
      is_finite_FF z = true ∧
      sign_FF z = xor sx sy
    else
      z = binary_overflow prec emax m (xor sx sy)) := by
  intro x y z
  have h_mx_pos : 0 < mx := Hx.1
  have h_my_pos : 0 < my := Hy.1
  have h_mxmy_pos : 0 < mx * my := mul_pos h_mx_pos h_my_pos
  have h_F2R_pos_mx : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ h_mx_pos
  have h_F2R_pos_my : 0 < F2R (beta := radix2) ⟨my, ey⟩ := F2R_gt_0 ⟨my, ey⟩ h_my_pos
  -- F2R⟨cond_Zopp sx mx, ex⟩ * F2R⟨cond_Zopp sy my, ey⟩
  --   = F2R⟨cond_Zopp sx mx * cond_Zopp sy my, ex + ey⟩
  -- via F2R_mult applied to the Fmult of the two floats.
  have h_F2R_mult : x * y =
      F2R (beta := radix2)
        ⟨cond_Zopp sx mx * cond_Zopp sy my, ex + ey⟩ := by
    show F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
       * F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩ = _
    rw [← F2R_mult]
    rfl
  -- |x * y| = F2R⟨mx * my, ex + ey⟩
  have h_abs_xy : |x * y| = F2R (beta := radix2) ⟨mx * my, ex + ey⟩ := by
    rw [h_F2R_mult]
    rw [show |F2R (beta := radix2) ⟨cond_Zopp sx mx * cond_Zopp sy my, ex + ey⟩|
            = F2R (beta := radix2) ⟨|cond_Zopp sx mx * cond_Zopp sy my|, ex + ey⟩
          from by rw [← F2R_Zabs]]
    have h_eq : |cond_Zopp sx mx * cond_Zopp sy my| = mx * my := by
      rw [abs_mul]
      have h1 : |cond_Zopp sx mx| = mx := by
        cases sx <;> simp [cond_Zopp, abs_of_pos h_mx_pos]
      have h2 : |cond_Zopp sy my| = my := by
        cases sy <;> simp [cond_Zopp, abs_of_pos h_my_pos]
      rw [h1, h2]
    rw [h_eq]
  have Bxy : inbetween_float radix2 (mx * my) (ex + ey) |x * y|
              location.Exact :=
    inbetween.Exact h_abs_xy
  have Exy : ex + ey ≤ FLT_exp (3 - emax - prec) prec
                  (Zdigits radix2 (mx * my) + (ex + ey)) :=
    bounded_mult_exp_le hp hmax mx ex my ey Hx Hy
  -- Sign: xor sx sy = decide (x*y < 0).
  have hx_eq : x = cond_Ropp sx (F2R (beta := radix2) ⟨mx, ex⟩) := by
    show F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ = _
    exact F2R_cond_Zopp sx mx ex
  have hy_eq : y = cond_Ropp sy (F2R (beta := radix2) ⟨my, ey⟩) := by
    show F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩ = _
    exact F2R_cond_Zopp sy my ey
  have h_sign : xor sx sy = decide (x * y < 0) := by
    rw [hx_eq, hy_eq]
    set X := F2R (beta := radix2) ⟨mx, ex⟩
    set Y := F2R (beta := radix2) ⟨my, ey⟩
    cases sx <;> cases sy <;>
      simp [cond_Ropp, decide_eq_false_iff_not, decide_eq_true_iff] <;>
      nlinarith [h_F2R_pos_mx, h_F2R_pos_my]
  -- Apply binary_round_aux_correct.
  have h_main := binary_round_aux_correct hp hmax m (x * y) (mx * my) (ex + ey)
                   location.Exact h_mxmy_pos Bxy Exy
  -- Convert the conclusion's `decide (x*y < 0)` back to `xor sx sy`.
  rw [← h_sign] at h_main
  exact h_main

/-- **`Bmult`** (Coq line 1386): IEEE-754 multiplication of two binary floats.
NaN inputs are propagated via the `mult_nan` policy. Zero × infinity is NaN.
Two finite floats are multiplied via `binary_round_aux` on the product mantissa
and summed exponents. -/
noncomputable def Bmult (hp : 0 < prec) (hmax : prec < emax)
    (mult_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | B754_nan _ _ _, _ => build_nan (mult_nan x y)
  | _, B754_nan _ _ _ => build_nan (mult_nan x y)
  | B754_infinity sx, B754_infinity sy => B754_infinity (xor sx sy)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xor sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_infinity (xor sx sy)
  | B754_infinity _, B754_zero _ => build_nan (mult_nan x y)
  | B754_zero _, B754_infinity _ => build_nan (mult_nan x y)
  | B754_finite sx _ _ _, B754_zero sy => B754_zero (xor sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xor sx sy)
  | B754_zero sx, B754_zero sy => B754_zero (xor sx sy)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    FF2B _ (Bmult_correct_aux hp hmax m sx mx ex Hx sy my ey Hy).1

/-- A unified statement of the "degenerate (non-finite-finite) cases" of
`Bmult_correct`: the if-true branch holds with `B2R(result) = 0`, the
finiteness as the and of inputs, and the conditional sign. -/
private theorem Bmult_correct_degenerate (hp : 0 < prec) (hmax : prec < emax)
    (mult_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax)
    (hxy_zero : B2R x * B2R y = 0)
    (h_B2R : B2R (Bmult hp hmax mult_nan m x y) = 0)
    (h_finite : is_finite (Bmult hp hmax mult_nan m x y) = (is_finite x && is_finite y))
    (h_sign : is_nan (Bmult hp hmax mult_nan m x y) = false →
        Bsign (Bmult hp hmax mult_nan m x y) = xor (Bsign x) (Bsign y)) :
    if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (B2R x * B2R y)| < bpow radix2 emax then
      B2R (Bmult hp hmax mult_nan m x y) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (B2R x * B2R y) ∧
      is_finite (Bmult hp hmax mult_nan m x y) = (is_finite x && is_finite y) ∧
      (is_nan (Bmult hp hmax mult_nan m x y) = false →
        Bsign (Bmult hp hmax mult_nan m x y) = xor (Bsign x) (Bsign y))
    else
      B2FF (Bmult hp hmax mult_nan m x y) =
        binary_overflow prec emax m (xor (Bsign x) (Bsign y)) := by
  rw [hxy_zero, round_0, abs_zero, if_pos (bpow_gt_0 radix2 emax)]
  exact ⟨h_B2R, h_finite, h_sign⟩

/-- **`Bmult_correct`** (Coq line 1401): IEEE-754 multiplication correctness.

When the rounded product fits, `B2R (Bmult x y) = round(B2R x * B2R y)`, the
result is finite iff both inputs are finite, and the sign (when not NaN) is the
xor of input signs. Otherwise, the result has `B2FF = binary_overflow`. -/
theorem Bmult_correct (hp : 0 < prec) (hmax : prec < emax)
    (mult_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax) :
    if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (B2R x * B2R y)| < bpow radix2 emax then
      B2R (Bmult hp hmax mult_nan m x y) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
          (B2R x * B2R y) ∧
      is_finite (Bmult hp hmax mult_nan m x y) = (is_finite x && is_finite y) ∧
      (is_nan (Bmult hp hmax mult_nan m x y) = false →
        Bsign (Bmult hp hmax mult_nan m x y) = xor (Bsign x) (Bsign y))
    else
      B2FF (Bmult hp hmax mult_nan m x y) =
        binary_overflow prec emax m (xor (Bsign x) (Bsign y)) := by
  -- Degenerate-case helper: given that the result is build_nan, the four
  -- obligations follow from B2R_build_nan, is_finite_build_nan, is_nan_build_nan.
  -- We'll instantiate `Bmult_correct_degenerate` per case.
  cases x with
  | B754_nan sx plx hx =>
    cases y with
    | B754_nan sy ply hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_zero sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_infinity sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_finite sy my ey hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
  | B754_infinity sx =>
    cases y with
    | B754_nan sy ply hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_zero sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_infinity sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · rfl
      · rfl
      · intro _; rfl
    | B754_finite sy my ey hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · rfl
      · rfl
      · intro _; rfl
  | B754_zero sx =>
    cases y with
    | B754_nan sy ply hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_zero sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · rfl
      · rfl
      · intro _; rfl
    | B754_infinity sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_finite sy my ey hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · rfl
      · rfl
      · intro _; rfl
  | B754_finite sx mx ex hx =>
    cases y with
    | B754_nan sy ply hy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · show B2R (build_nan _) = 0; rw [B2R_build_nan]
      · show is_finite (build_nan _) = _; rw [is_finite_build_nan]; rfl
      · intro h; exfalso; revert h
        show is_nan (build_nan _) = false → _
        rw [is_nan_build_nan]; intro hcon; exact Bool.noConfusion hcon
    | B754_zero sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · rfl
      · rfl
      · intro _; rfl
    | B754_infinity sy =>
      apply Bmult_correct_degenerate hp hmax mult_nan m _ _ (by simp [B2R])
      · rfl
      · rfl
      · intro _; rfl
    | B754_finite sy my ey hy =>
      -- The non-trivial case: apply Bmult_correct_aux.
      have h_aux := Bmult_correct_aux hp hmax m sx mx ex hx sy my ey hy
      -- Unwrap the `let`-bound `z` to its actual form.
      simp only [] at h_aux
      obtain ⟨h_valid, h_cond⟩ := h_aux
      have hBx : B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)
                = F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ := rfl
      have hBy : B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy)
                = F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩ := rfl
      rw [hBx, hBy]
      -- Bmult result for (finite, finite) unfolds to FF2B.
      have h_Bmult_eq : Bmult hp hmax mult_nan m
            (B754_finite sx mx ex hx) (B754_finite sy my ey hy)
          = FF2B _ (Bmult_correct_aux hp hmax m sx mx ex hx sy my ey hy).1 := rfl
      rw [h_Bmult_eq]
      split_ifs with h_lt
      · rw [if_pos h_lt] at h_cond
        obtain ⟨h_F2R, h_finite, h_sign⟩ := h_cond
        refine ⟨?_, ?_, ?_⟩
        · rw [B2R_FF2B]; exact h_F2R
        · rw [is_finite_FF2B, h_finite]; rfl
        · intro _; rw [Bsign_FF2B]; exact h_sign
      · rw [if_neg h_lt] at h_cond
        rw [B2FF_FF2B]; exact h_cond

/-! ## Normalization and rounding -/

/-- **`shl_align`** (Coq line 1429): left-align a mantissa `mx` from exponent
`ex` toward a smaller target exponent `ex'`. If `ex' < ex`, multiplies the
mantissa by `2^(ex - ex')` and shifts exponent down to `ex'`; otherwise leaves
`(mx, ex)` unchanged. -/
def shl_align (mx ex ex' : ℤ) : ℤ × ℤ :=
  if ex' < ex then
    (mx * 2 ^ (ex - ex').toNat, ex')
  else
    (mx, ex)

theorem shl_align_correct (mx ex ex' : ℤ) :
    let mxex'' := shl_align mx ex ex'
    F2R (beta := radix2) ⟨mx, ex⟩
      = F2R (beta := radix2) ⟨mxex''.1, mxex''.2⟩ ∧
    mxex''.2 ≤ ex' := by
  unfold shl_align
  by_cases h : ex' < ex
  · rw [if_pos h]
    refine ⟨?_, le_refl _⟩
    show F2R (beta := radix2) ⟨mx, ex⟩
        = F2R (beta := radix2) ⟨mx * 2 ^ (ex - ex').toNat, ex'⟩
    rw [show (2 : ℤ) ^ (ex - ex').toNat = (radix2.val : ℤ) ^ (ex - ex').toNat from rfl]
    exact F2R_change_exp (beta := radix2) ex' mx ex (le_of_lt h)
  · rw [if_neg h]
    exact ⟨rfl, le_of_not_lt h⟩

theorem snd_shl_align (mx ex ex' : ℤ) (He : ex' ≤ ex) :
    (shl_align mx ex ex').2 = ex' := by
  unfold shl_align
  rcases lt_or_eq_of_le He with h | h
  · rw [if_pos h]
  · rw [if_neg (by omega : ¬ ex' < ex)]
    exact h.symm

/-- **`shl_align_fexp`** (Coq line 1487): align a mantissa to the canonical
exponent for `FLT_exp`. -/
noncomputable def shl_align_fexp (prec emax : ℤ) (mx ex : ℤ) : ℤ × ℤ :=
  shl_align mx ex (FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex))

theorem shl_align_fexp_correct (prec emax : ℤ) (mx ex : ℤ) (hmx : mx ≠ 0) :
    let mxex' := shl_align_fexp prec emax mx ex
    F2R (beta := radix2) ⟨mx, ex⟩
      = F2R (beta := radix2) ⟨mxex'.1, mxex'.2⟩ ∧
    mxex'.2 ≤ FLT_exp (3 - emax - prec) prec
                (Zdigits radix2 mxex'.1 + mxex'.2) := by
  unfold shl_align_fexp
  set fxp := FLT_exp (3 - emax - prec) prec
  obtain ⟨h_eq, h_le⟩ := shl_align_correct mx ex (fxp (Zdigits radix2 mx + ex))
  refine ⟨h_eq, ?_⟩
  -- Show the exponent of the shifted mantissa matches the canonical exponent.
  -- The shifted F2R has the same value, so Zdigits + exp is preserved.
  set mxex'' := shl_align mx ex (fxp (Zdigits radix2 mx + ex))
  have h_zd : Zdigits radix2 mxex''.1 + mxex''.2 = Zdigits radix2 mx + ex := by
    by_cases hm' : mxex''.1 = 0
    · -- Then F2R⟨mx, ex⟩ = 0, so mx = 0 — contradiction.
      exfalso
      apply hmx
      have h_F2R_eq : F2R (beta := radix2) ⟨mx, ex⟩ = 0 := by
        rw [h_eq, hm']
        show F2R (beta := radix2) ⟨0, mxex''.2⟩ = 0
        exact F2R_0 mxex''.2
      exact eq_0_F2R (m := mx) (e := ex) h_F2R_eq
    · -- mxex''.1 ≠ 0: bridge Zdigits via mag.
      have h_F2R_ne : F2R (beta := radix2) ⟨mx, ex⟩ ≠ 0 := by
        intro hcon
        exact hmx (eq_0_F2R hcon)
      have h_F2R_ne' : F2R (beta := radix2) ⟨mxex''.1, mxex''.2⟩ ≠ 0 := by
        rw [← h_eq]; exact h_F2R_ne
      rw [show Zdigits radix2 mxex''.1 + mxex''.2
            = mag radix2 (F2R (beta := radix2) ⟨mxex''.1, mxex''.2⟩)
          from (mag_F2R_Zdigits mxex''.1 mxex''.2 hm').symm,
          show Zdigits radix2 mx + ex
            = mag radix2 (F2R (beta := radix2) ⟨mx, ex⟩)
          from (mag_F2R_Zdigits mx ex hmx).symm, h_eq]
  rw [h_zd]; exact h_le

/-- **`binary_round`** (Coq line 1509): the full IEEE rounding wrapper. Aligns
the mantissa to the canonical FLT exponent, then applies `binary_round_aux`
with exact location. -/
noncomputable def binary_round (prec emax : ℤ) (m : mode)
    (sx : Bool) (mx ex : ℤ) : full_float :=
  let mzez := shl_align_fexp prec emax mx ex
  binary_round_aux prec emax m sx mzez.1 mzez.2 location.Exact

theorem binary_round_correct (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (sx : Bool) (mx ex : ℤ) (hmx : 0 < mx) :
    let z := binary_round prec emax m sx mx ex
    let x := F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
    valid_binary prec emax z ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax then
      FF2R radix2 z = round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ∧
      is_finite_FF z = true ∧
      sign_FF z = sx
    else
      z = binary_overflow prec emax m sx) := by
  intro z x
  have hmx_ne : mx ≠ 0 := by linarith
  -- Use shl_align_fexp_correct.
  obtain ⟨h_F2R_eq, h_le⟩ := shl_align_fexp_correct prec emax mx ex hmx_ne
  set mzez := shl_align_fexp prec emax mx ex with hmzez_def
  -- The shifted mantissa is still positive (preserves F2R sign).
  have h_mz_pos : 0 < mzez.1 := by
    by_contra h
    push_neg at h
    -- If mz ≤ 0, then F2R ≤ 0; but F2R⟨mx, ex⟩ > 0 since mx > 0.
    have h_F2R_mx : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ hmx
    have h_F2R_eq' : F2R (beta := radix2) ⟨mzez.1, mzez.2⟩
        = F2R (beta := radix2) ⟨mx, ex⟩ := h_F2R_eq.symm
    rcases lt_or_eq_of_le h with hlt | heq
    · have h_F2R_neg : F2R (beta := radix2) ⟨mzez.1, mzez.2⟩ < 0 :=
        F2R_lt_0 (⟨mzez.1, mzez.2⟩ : float radix2) hlt
      linarith
    · -- mzez.1 = 0 → F2R⟨0, ez⟩ = 0; but F2R⟨mx, ex⟩ > 0. Contradiction.
      have hF_zero : F2R (beta := radix2) ⟨mzez.1, mzez.2⟩ = 0 := by
        rw [show mzez.1 = 0 from heq]; exact F2R_0 mzez.2
      linarith
  -- |x| = F2R⟨mzez.1, mzez.2⟩
  have h_abs_x : |x| = F2R (beta := radix2) ⟨mzez.1, mzez.2⟩ := by
    show |F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩|
        = F2R (beta := radix2) ⟨mzez.1, mzez.2⟩
    rw [← F2R_Zabs]
    rw [show |cond_Zopp sx mx| = mx by cases sx <;> simp [cond_Zopp, abs_of_pos hmx]]
    exact h_F2R_eq
  have Bx : inbetween_float radix2 mzez.1 mzez.2 |x| location.Exact :=
    inbetween.Exact h_abs_x
  -- Sign: sx = decide (x < 0).
  have h_sign : sx = decide (x < 0) := by
    show sx = decide (F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ < 0)
    rw [F2R_cond_Zopp]
    have h_F2R_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ hmx
    cases sx <;> simp [cond_Ropp, decide_eq_true_iff, decide_eq_false_iff_not] <;> linarith
  -- Apply binary_round_aux_correct.
  have h_main := binary_round_aux_correct hp hmax m x mzez.1 mzez.2 location.Exact
                   h_mz_pos Bx h_le
  simp only [] at h_main
  -- z unfolds to binary_round_aux ... mzez.1 mzez.2 location.Exact.
  show valid_binary prec emax (binary_round_aux prec emax m sx mzez.1 mzez.2 location.Exact) ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax then
      FF2R radix2 (binary_round_aux prec emax m sx mzez.1 mzez.2 location.Exact)
        = round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ∧
      is_finite_FF (binary_round_aux prec emax m sx mzez.1 mzez.2 location.Exact) = true ∧
      sign_FF (binary_round_aux prec emax m sx mzez.1 mzez.2 location.Exact) = sx
    else
      binary_round_aux prec emax m sx mzez.1 mzez.2 location.Exact
        = binary_overflow prec emax m sx)
  rw [h_sign]
  exact h_main

/-- **`binary_normalize`** (Coq line 1544): normalize a signed mantissa + exponent
into a `binary_float`. Dispatches on the sign of `mx`: zero → `B754_zero szero`,
positive → `binary_round` with `sx = false`, negative → `binary_round` with
`sx = true` and `-mx` (which is then positive). -/
noncomputable def binary_normalize (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (mx ex : ℤ) (szero : Bool) : binary_float prec emax :=
  if h_pos : 0 < mx then
    FF2B _ (binary_round_correct hp hmax m false mx ex h_pos).1
  else if h_neg : mx < 0 then
    FF2B _ (binary_round_correct hp hmax m true (-mx) ex (by omega)).1
  else
    B754_zero szero

theorem binary_normalize_correct (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (mx ex : ℤ) (szero : Bool) :
    let x := F2R (beta := radix2) ⟨mx, ex⟩
    let z := binary_normalize hp hmax m mx ex szero
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x|
        < bpow radix2 emax then
      B2R z = round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) x ∧
      is_finite z = true ∧
      Bsign z = (match compare x (0 : ℝ) with
                  | Ordering.eq => szero
                  | Ordering.lt => true
                  | Ordering.gt => false)
    else
      B2FF z = binary_overflow prec emax m (decide (x < 0))) := by
  intro x z
  rcases lt_trichotomy mx 0 with h_neg | h_zero | h_pos
  · -- mx < 0
    show (if _ < _ then _ else _)
    have h_neg_mx_pos : 0 < -mx := by omega
    have h_brc := binary_round_correct hp hmax m true (-mx) ex h_neg_mx_pos
    simp only [] at h_brc
    -- F2R⟨cond_Zopp true (-mx), ex⟩ = F2R⟨mx, ex⟩
    have h_F2R_eq : F2R (beta := radix2) ⟨cond_Zopp true (-mx), ex⟩ = x := by
      show F2R (beta := radix2) ⟨-(-mx), ex⟩ = F2R (beta := radix2) ⟨mx, ex⟩
      congr 1; show ⟨-(-mx), ex⟩ = (⟨mx, ex⟩ : float radix2); congr 1; omega
    rw [h_F2R_eq] at h_brc
    obtain ⟨h_valid, h_cond⟩ := h_brc
    -- z = FF2B _ h_valid (via binary_normalize's mx < 0 branch)
    have h_z_eq : z = FF2B _ h_valid := by
      show binary_normalize hp hmax m mx ex szero = _
      unfold binary_normalize
      rw [dif_neg (by omega : ¬ 0 < mx), dif_pos h_neg]
    rw [h_z_eq]
    have h_F2R_neg : x < 0 :=
      F2R_lt_0 (⟨mx, ex⟩ : float radix2) h_neg
    -- Both branches use binary_round_correct's result.
    split_ifs with h_lt
    · rw [if_pos h_lt] at h_cond
      obtain ⟨h_F2R_round, h_finite, h_sign⟩ := h_cond
      refine ⟨?_, ?_, ?_⟩
      · rw [show B2R (FF2B _ _) = FF2R radix2 _ from B2R_FF2B _ _]
        exact h_F2R_round
      · rw [is_finite_FF2B]; exact h_finite
      · rw [Bsign_FF2B, h_sign]
        rw [show compare x (0 : ℝ) = Ordering.lt from compare_lt_iff_lt.mpr h_F2R_neg]
    · rw [if_neg h_lt] at h_cond
      rw [B2FF_FF2B, h_cond]
      rw [show decide (x < 0) = true from decide_eq_true h_F2R_neg]
  · -- mx = 0
    subst h_zero
    have h_F2R_zero : x = 0 := by show F2R (beta := radix2) ⟨0, ex⟩ = 0; exact F2R_0 ex
    rw [h_F2R_zero, round_0, abs_zero, if_pos (bpow_gt_0 radix2 emax)]
    have h_z_eq : z = B754_zero szero := by
      show binary_normalize hp hmax m 0 ex szero = _
      unfold binary_normalize
      rw [dif_neg (by omega : ¬ 0 < (0 : ℤ)),
          dif_neg (by omega : ¬ (0 : ℤ) < 0)]
    refine ⟨?_, ?_, ?_⟩
    · rw [h_z_eq]; rfl
    · rw [h_z_eq]; rfl
    · rw [h_z_eq]
      show szero = _
      rw [show compare (0 : ℝ) (0 : ℝ) = Ordering.eq from compare_eq_iff_eq.mpr rfl]
  · -- 0 < mx
    show (if _ < _ then _ else _)
    have h_brc := binary_round_correct hp hmax m false mx ex h_pos
    simp only [] at h_brc
    have h_F2R_eq : F2R (beta := radix2) ⟨cond_Zopp false mx, ex⟩ = x := rfl
    rw [h_F2R_eq] at h_brc
    obtain ⟨h_valid, h_cond⟩ := h_brc
    have h_z_eq : z = FF2B _ h_valid := by
      show binary_normalize hp hmax m mx ex szero = _
      unfold binary_normalize
      rw [dif_pos h_pos]
    rw [h_z_eq]
    have h_F2R_pos : 0 < x := F2R_gt_0 (⟨mx, ex⟩ : float radix2) h_pos
    split_ifs with h_lt
    · rw [if_pos h_lt] at h_cond
      obtain ⟨h_F2R_round, h_finite, h_sign⟩ := h_cond
      refine ⟨?_, ?_, ?_⟩
      · rw [show B2R (FF2B _ _) = FF2R radix2 _ from B2R_FF2B _ _]
        exact h_F2R_round
      · rw [is_finite_FF2B]; exact h_finite
      · rw [Bsign_FF2B, h_sign]
        rw [show compare x (0 : ℝ) = Ordering.gt from compare_gt_iff_gt.mpr h_F2R_pos]
    · rw [if_neg h_lt] at h_cond
      rw [B2FF_FF2B, h_cond]
      rw [show decide (x < 0) = false from decide_eq_false (by linarith)]

/-! ## Addition -/

/-- **`Bplus`** (Coq line 1613): IEEE-754 binary addition.

NaN cases dispatch through `plus_nan`. Infinity+Infinity returns the input
when signs match, NaN otherwise. Infinity + (zero|finite) returns the
infinity. Zero+Zero returns the input when signs match; otherwise the
mode-dependent sign-zero. (Zero+finite returns the finite; finite+zero too.)
Finite+Finite aligns to the lower exponent and goes through
`binary_normalize` with the mode-dependent zero sign. -/
noncomputable def Bplus (hp : 0 < prec) (hmax : prec < emax)
    (plus_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | B754_nan _ _ _, _ => build_nan (plus_nan x y)
  | _, B754_nan _ _ _ => build_nan (plus_nan x y)
  | B754_infinity sx, B754_infinity sy =>
    if sx = sy then B754_infinity sx else build_nan (plus_nan x y)
  | B754_infinity sx, B754_zero _ => B754_infinity sx
  | B754_infinity sx, B754_finite _ _ _ _ => B754_infinity sx
  | B754_zero _, B754_infinity sy => B754_infinity sy
  | B754_finite _ _ _ _, B754_infinity sy => B754_infinity sy
  | B754_zero sx, B754_zero sy =>
    if sx = sy then B754_zero sx else
      match m with
      | .mode_DN => B754_zero true
      | _ => B754_zero false
  | B754_zero _, B754_finite sy my ey hy => B754_finite sy my ey hy
  | B754_finite sx mx ex hx, B754_zero _ => B754_finite sx mx ex hx
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
    let ez := min ex ey
    binary_normalize hp hmax m
      (cond_Zopp sx (shl_align mx ex ez).1 + cond_Zopp sy (shl_align my ey ez).1)
      ez
      (match m with | .mode_DN => true | _ => false)

/-- **`Bminus`** (Coq line 1795): IEEE-754 binary subtraction.

The same shape as `Bplus`, but with the second operand's sign flipped at every
position. NaN cases dispatch via `minus_nan`. Reduces to `Bplus _ x (Bopp _ y)`
when neither input is NaN. -/
noncomputable def Bminus (hp : 0 < prec) (hmax : prec < emax)
    (minus_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | B754_nan _ _ _, _ => build_nan (minus_nan x y)
  | _, B754_nan _ _ _ => build_nan (minus_nan x y)
  | B754_infinity sx, B754_infinity sy =>
    if sx = !sy then B754_infinity sx else build_nan (minus_nan x y)
  | B754_infinity sx, B754_zero _ => B754_infinity sx
  | B754_infinity sx, B754_finite _ _ _ _ => B754_infinity sx
  | B754_zero _, B754_infinity sy => B754_infinity (!sy)
  | B754_finite _ _ _ _, B754_infinity sy => B754_infinity (!sy)
  | B754_zero sx, B754_zero sy =>
    if sx = !sy then B754_zero sx else
      match m with
      | .mode_DN => B754_zero true
      | _ => B754_zero false
  | B754_zero _, B754_finite sy my ey hy => B754_finite (!sy) my ey hy
  | B754_finite sx mx ex hx, B754_zero _ => B754_finite sx mx ex hx
  | B754_finite sx mx ex _, B754_finite sy my ey _ =>
    let ez := min ex ey
    binary_normalize hp hmax m
      (cond_Zopp sx (shl_align mx ex ez).1 - cond_Zopp sy (shl_align my ey ez).1)
      ez
      (match m with | .mode_DN => true | _ => false)

/-- **`Bplus_correct`** (Coq line 1631): IEEE-754 addition correctness.

If both inputs are finite, then either the rounded sum fits — and `B2R` of the
result equals `round (B2R x + B2R y)`, the result is finite, and `Bsign` matches
the rounded sum's sign — or the sum overflows, in which case the result encodes
`binary_overflow` and `Bsign x = Bsign y` (overflow requires same-sign inputs). -/
theorem Bplus_correct (hp : 0 < prec) (hmax : prec < emax)
    (plus_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax)
    (Fx : is_finite x = true) (Fy : is_finite y = true) :
    if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (B2R x + B2R y)| < bpow radix2 emax then
      B2R (Bplus hp hmax plus_nan m x y) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
          (B2R x + B2R y) ∧
      is_finite (Bplus hp hmax plus_nan m x y) = true ∧
      Bsign (Bplus hp hmax plus_nan m x y) =
        (match compare (B2R x + B2R y) (0 : ℝ) with
         | Ordering.eq =>
            match m with
            | .mode_DN => Bsign x || Bsign y
            | _ => Bsign x && Bsign y
         | Ordering.lt => true
         | Ordering.gt => false)
    else
      B2FF (Bplus hp hmax plus_nan m x y) = binary_overflow prec emax m (Bsign x)
        ∧ Bsign x = Bsign y := by
  -- Eliminate impossible nan/inf cases via Fx, Fy.
  cases x with
  | B754_nan _ _ _ => simp [is_finite] at Fx
  | B754_infinity _ => simp [is_finite] at Fx
  | B754_zero sx =>
    cases y with
    | B754_nan _ _ _ => simp [is_finite] at Fy
    | B754_infinity _ => simp [is_finite] at Fy
    | B754_zero sy =>
      -- (zero, zero): sum is 0, round is 0, |0| < bpow emax.
      have h_sum : B2R (B754_zero (prec := prec) (emax := emax) sx)
                 + B2R (B754_zero (prec := prec) (emax := emax) sy) = 0 := by
        show (0 : ℝ) + 0 = 0; ring
      rw [h_sum, round_0, abs_zero, if_pos (bpow_gt_0 radix2 emax)]
      have h_Bplus_eq : Bplus hp hmax plus_nan m
            (B754_zero (prec := prec) (emax := emax) sx)
            (B754_zero (prec := prec) (emax := emax) sy)
          = (if sx = sy then B754_zero sx else
              match m with
              | .mode_DN => B754_zero true
              | _ => B754_zero false) := rfl
      rw [h_Bplus_eq]
      refine ⟨?_, ?_, ?_⟩
      · by_cases hs : sx = sy
        · rw [if_pos hs]; rfl
        · rw [if_neg hs]; cases m <;> rfl
      · by_cases hs : sx = sy
        · rw [if_pos hs]; rfl
        · rw [if_neg hs]; cases m <;> rfl
      · -- Bsign of result vs match-on-compare-of-0.
        rw [show compare (0 : ℝ) (0 : ℝ) = Ordering.eq from compare_eq_iff_eq.mpr rfl]
        by_cases hs : sx = sy
        · subst hs
          rw [if_pos rfl]
          cases m <;> simp [Bsign]
        · rw [if_neg hs]
          have hne : sx ≠ sy := hs
          cases m <;> cases sx <;> cases sy <;> simp_all [Bsign]
    | B754_finite sy my ey hy =>
      -- (zero, finite): Bplus returns y; sum = B2R y; round generic.
      have h_x_zero : B2R (B754_zero (prec := prec) (emax := emax) sx) = 0 := rfl
      rw [h_x_zero, zero_add]
      have h_Bplus_eq : Bplus hp hmax plus_nan m
            (B754_zero (prec := prec) (emax := emax) sx)
            (B754_finite sy my ey hy)
          = B754_finite sy my ey hy := rfl
      rw [h_Bplus_eq]
      have h_round_y : round radix2 (FLT_exp (3 - emax - prec) prec)
            (round_mode m) (B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy))
          = B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy) :=
        round_generic _ _ _ (generic_format_B2R _)
      rw [h_round_y]
      have h_abs_lt : |B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy)|
          < bpow radix2 emax :=
        abs_B2R_lt_emax hp hmax _
      rw [if_pos h_abs_lt]
      refine ⟨rfl, rfl, ?_⟩
      -- Bsign(B754_finite sy ...) = sy; need to show this matches compare.
      show sy = _
      -- B2R y > 0 iff sy = false; B2R y < 0 iff sy = true.
      have hmy_pos : 0 < my := by linarith [hy.1]
      have h_F2R_pos : 0 < F2R (beta := radix2) ⟨my, ey⟩ := F2R_gt_0 ⟨my, ey⟩ hmy_pos
      cases sy
      · -- sy = false: B2R y = F2R⟨my, ey⟩ > 0
        have : (0 : ℝ) < B2R (B754_finite (prec := prec) (emax := emax) false my ey hy) := by
          show 0 < F2R (beta := radix2) ⟨cond_Zopp false my, ey⟩
          exact h_F2R_pos
        rw [show compare (B2R (B754_finite (prec := prec) (emax := emax) false my ey hy)) (0 : ℝ)
              = Ordering.gt from compare_gt_iff_gt.mpr this]
      · -- sy = true: B2R y = F2R⟨-my, ey⟩ < 0
        have : B2R (B754_finite (prec := prec) (emax := emax) true my ey hy) < 0 := by
          show F2R (beta := radix2) ⟨cond_Zopp true my, ey⟩ < 0
          show F2R (beta := radix2) ⟨-my, ey⟩ < 0
          rw [F2R_Zopp]; linarith
        rw [show compare (B2R (B754_finite (prec := prec) (emax := emax) true my ey hy)) (0 : ℝ)
              = Ordering.lt from compare_lt_iff_lt.mpr this]
  | B754_finite sx mx ex hx =>
    cases y with
    | B754_nan _ _ _ => simp [is_finite] at Fy
    | B754_infinity _ => simp [is_finite] at Fy
    | B754_zero sy =>
      -- (finite, zero): Bplus returns x; symmetric to (zero, finite).
      have h_y_zero : B2R (B754_zero (prec := prec) (emax := emax) sy) = 0 := rfl
      rw [h_y_zero, add_zero]
      have h_Bplus_eq : Bplus hp hmax plus_nan m
            (B754_finite sx mx ex hx)
            (B754_zero (prec := prec) (emax := emax) sy)
          = B754_finite sx mx ex hx := rfl
      rw [h_Bplus_eq]
      have h_round_x : round radix2 (FLT_exp (3 - emax - prec) prec)
            (round_mode m) (B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx))
          = B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx) :=
        round_generic _ _ _ (generic_format_B2R _)
      rw [h_round_x]
      have h_abs_lt : |B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)|
          < bpow radix2 emax :=
        abs_B2R_lt_emax hp hmax _
      rw [if_pos h_abs_lt]
      refine ⟨rfl, rfl, ?_⟩
      show sx = _
      have hmx_pos : 0 < mx := by linarith [hx.1]
      have h_F2R_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ hmx_pos
      cases sx
      · have : (0 : ℝ) < B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx) := by
          show 0 < F2R (beta := radix2) ⟨cond_Zopp false mx, ex⟩; exact h_F2R_pos
        rw [show compare (B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx)) (0 : ℝ)
              = Ordering.gt from compare_gt_iff_gt.mpr this]
      · have : B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx) < 0 := by
          show F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩ < 0
          show F2R (beta := radix2) ⟨-mx, ex⟩ < 0
          rw [F2R_Zopp]; linarith
        rw [show compare (B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx)) (0 : ℝ)
              = Ordering.lt from compare_lt_iff_lt.mpr this]
    | B754_finite sy my ey hy =>
      -- The substantive case: align exponents, sum, apply binary_normalize_correct.
      have hmx_pos : 0 < mx := by linarith [hx.1]
      have hmy_pos : 0 < my := by linarith [hy.1]
      -- Setup: ez = min ex ey, shifted mantissas mxez, myez, sum mz, mode-zero sign.
      set ez := min ex ey with hez_def
      set mxez := shl_align mx ex ez with hmxez_def
      set myez := shl_align my ey ez with hmyez_def
      set mz : ℤ := cond_Zopp sx mxez.1 + cond_Zopp sy myez.1 with hmz_def
      set szero : Bool := match m with | .mode_DN => true | _ => false with hszero_def
      have h_ex_ge_ez : ez ≤ ex := min_le_left ex ey
      have h_ey_ge_ez : ez ≤ ey := min_le_right ex ey
      have h_mxez_exp : mxez.2 = ez := snd_shl_align mx ex ez h_ex_ge_ez
      have h_myez_exp : myez.2 = ez := snd_shl_align my ey ez h_ey_ge_ez
      have h_F2R_mx : F2R (beta := radix2) ⟨mx, ex⟩
          = F2R (beta := radix2) ⟨mxez.1, ez⟩ := by
        have h := (shl_align_correct mx ex ez).1
        rw [h_mxez_exp] at h; exact h
      have h_F2R_my : F2R (beta := radix2) ⟨my, ey⟩
          = F2R (beta := radix2) ⟨myez.1, ez⟩ := by
        have h := (shl_align_correct my ey ez).1
        rw [h_myez_exp] at h; exact h
      -- mxez.1 > 0 and myez.1 > 0 (preserved by shl_align since multiplier > 0).
      have h_mxez_pos : 0 < mxez.1 := by
        show 0 < (shl_align mx ex ez).1
        unfold shl_align
        by_cases h : ez < ex
        · rw [if_pos h]; show 0 < mx * 2 ^ (ex - ez).toNat
          have : 0 < (2 : ℤ) ^ (ex - ez).toNat := pow_pos (by norm_num) _
          exact mul_pos hmx_pos this
        · rw [if_neg h]; exact hmx_pos
      have h_myez_pos : 0 < myez.1 := by
        show 0 < (shl_align my ey ez).1
        unfold shl_align
        by_cases h : ez < ey
        · rw [if_pos h]; show 0 < my * 2 ^ (ey - ez).toNat
          have : 0 < (2 : ℤ) ^ (ey - ez).toNat := pow_pos (by norm_num) _
          exact mul_pos hmy_pos this
        · rw [if_neg h]; exact hmy_pos
      -- Hp: B2R x + B2R y = F2R⟨mz, ez⟩.
      have Hp : B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)
              + B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy)
            = F2R (beta := radix2) ⟨mz, ez⟩ := by
        show F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
            + F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩
            = F2R (beta := radix2) ⟨mz, ez⟩
        rw [F2R_cond_Zopp, F2R_cond_Zopp, h_F2R_mx, h_F2R_my,
            ← F2R_cond_Zopp, ← F2R_cond_Zopp]
        show F2R (beta := radix2) ⟨cond_Zopp sx mxez.1, ez⟩
            + F2R (beta := radix2) ⟨cond_Zopp sy myez.1, ez⟩
            = F2R (beta := radix2) ⟨cond_Zopp sx mxez.1 + cond_Zopp sy myez.1, ez⟩
        unfold F2R; push_cast; ring
      -- The Bplus result.
      have h_Bplus_eq : Bplus hp hmax plus_nan m
            (B754_finite sx mx ex hx) (B754_finite sy my ey hy)
          = binary_normalize hp hmax m mz ez szero := rfl
      rw [h_Bplus_eq, Hp]
      -- Apply binary_normalize_correct.
      have h_bn := binary_normalize_correct hp hmax m mz ez szero
      simp only [] at h_bn
      -- Sz lemma: if overflow then sx = decide(F2R⟨mz,ez⟩ < 0) ∧ sx = sy.
      -- We'll need this for the overflow case. Establish bounded-ness for input
      -- values (used in the proof of Sz).
      have hbBx : |B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)|
          < bpow radix2 emax := abs_B2R_lt_emax hp hmax _
      have hbBy : |B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy)|
          < bpow radix2 emax := abs_B2R_lt_emax hp hmax _
      have hgenBx : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)) :=
        generic_format_B2R _
      have hgenBy : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy)) :=
        generic_format_B2R _
      have hcanBx : canonical radix2 (FLT_exp (3 - emax - prec) prec)
          (⟨cond_Zopp sx mx, ex⟩ : float radix2) :=
        canonical_canonical_mantissa sx mx ex hx.2.1 hx.1
      have hcanBy : canonical radix2 (FLT_exp (3 - emax - prec) prec)
          (⟨cond_Zopp sy my, ey⟩ : float radix2) :=
        canonical_canonical_mantissa sy my ey hy.2.1 hy.1
      -- Cached bounds for the absolute values of F2R⟨mx, ex⟩ and F2R⟨my, ey⟩.
      have hF2R_mx_lt : F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) < bpow radix2 emax := by
        have h := hbBx
        cases sx
        · show F2R (beta := radix2) ⟨mx, ex⟩ < bpow radix2 emax
          have : |F2R (beta := radix2) (⟨mx, ex⟩ : float radix2)| < bpow radix2 emax := h
          rw [abs_of_pos (F2R_gt_0 ⟨mx, ex⟩ hmx_pos)] at this; exact this
        · have hF : |F2R (beta := radix2) (⟨-mx, ex⟩ : float radix2)| < bpow radix2 emax := h
          rw [F2R_Zopp, abs_neg, abs_of_pos (F2R_gt_0 ⟨mx, ex⟩ hmx_pos)] at hF; exact hF
      have hF2R_my_lt : F2R (beta := radix2) (⟨my, ey⟩ : float radix2) < bpow radix2 emax := by
        have h := hbBy
        cases sy
        · show F2R (beta := radix2) ⟨my, ey⟩ < bpow radix2 emax
          have : |F2R (beta := radix2) (⟨my, ey⟩ : float radix2)| < bpow radix2 emax := h
          rw [abs_of_pos (F2R_gt_0 ⟨my, ey⟩ hmy_pos)] at this; exact this
        · have hF : |F2R (beta := radix2) (⟨-my, ey⟩ : float radix2)| < bpow radix2 emax := h
          rw [F2R_Zopp, abs_neg, abs_of_pos (F2R_gt_0 ⟨my, ey⟩ hmy_pos)] at hF; exact hF
      -- Generic-format containers for ±F2R⟨mx, ex⟩ and ±F2R⟨my, ey⟩.
      have hgen_pos_mx : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (F2R (beta := radix2) (⟨mx, ex⟩ : float radix2)) := by
        apply generic_format_canonical
        exact canonical_canonical_mantissa (prec := prec) (emax := emax)
          false mx ex hx.2.1 hx.1
      have hgen_pos_my : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (F2R (beta := radix2) (⟨my, ey⟩ : float radix2)) := by
        apply generic_format_canonical
        exact canonical_canonical_mantissa (prec := prec) (emax := emax)
          false my ey hy.2.1 hy.1
      have hgen_neg_mx : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (-F2R (beta := radix2) (⟨mx, ex⟩ : float radix2)) := by
        rw [show -F2R (beta := radix2) (⟨mx, ex⟩ : float radix2)
              = F2R (beta := radix2) (⟨-mx, ex⟩ : float radix2)
            from (F2R_Zopp mx ex).symm]
        apply generic_format_canonical
        exact canonical_canonical_mantissa (prec := prec) (emax := emax)
          true mx ex hx.2.1 hx.1
      have hgen_neg_my : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (-F2R (beta := radix2) (⟨my, ey⟩ : float radix2)) := by
        rw [show -F2R (beta := radix2) (⟨my, ey⟩ : float radix2)
              = F2R (beta := radix2) (⟨-my, ey⟩ : float radix2)
            from (F2R_Zopp my ey).symm]
        apply generic_format_canonical
        exact canonical_canonical_mantissa (prec := prec) (emax := emax)
          true my ey hy.2.1 hy.1
      -- Sz: |round F2R⟨mz,ez⟩| ≥ bpow emax → sx = decide(F2R⟨mz,ez⟩ < 0) ∧ sx = sy.
      have Sz : bpow radix2 emax ≤
          |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
              (F2R (beta := radix2) (⟨mz, ez⟩ : float radix2))| →
          sx = decide (F2R (beta := radix2) (⟨mz, ez⟩ : float radix2) < 0) ∧ sx = sy := by
        intro Bz
        -- B2R x + B2R y as a real number; substitute via Hp.
        have hBx_def : B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)
            = F2R (beta := radix2) (⟨cond_Zopp sx mx, ex⟩ : float radix2) := rfl
        have hBy_def : B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy)
            = F2R (beta := radix2) (⟨cond_Zopp sy my, ey⟩ : float radix2) := rfl
        by_cases Hs : sx = sy
        · refine ⟨?_, Hs⟩
          subst Hs
          -- Same sign: sum has the same sign as sx.
          cases sx
          · -- sx = sy = false: sum ≥ 0 ⇒ decide(<0) = false.
            have hsum_ge :
                0 ≤ F2R (beta := radix2) (⟨mz, ez⟩ : float radix2) := by
              rw [← Hp, hBx_def, hBy_def]
              show 0 ≤ F2R (beta := radix2) ⟨cond_Zopp false mx, ex⟩
                    + F2R (beta := radix2) ⟨cond_Zopp false my, ey⟩
              show 0 ≤ F2R (beta := radix2) ⟨mx, ex⟩
                    + F2R (beta := radix2) ⟨my, ey⟩
              linarith [F2R_ge_0 (⟨mx, ex⟩ : float radix2) (le_of_lt hmx_pos),
                        F2R_ge_0 (⟨my, ey⟩ : float radix2) (le_of_lt hmy_pos)]
            exact (decide_eq_false (not_lt.mpr hsum_ge)).symm
          · -- sx = sy = true: sum < 0.
            have hsum_lt : F2R (beta := radix2) (⟨mz, ez⟩ : float radix2) < 0 := by
              rw [← Hp, hBx_def, hBy_def]
              show F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩
                    + F2R (beta := radix2) ⟨cond_Zopp true my, ey⟩ < 0
              show F2R (beta := radix2) ⟨-mx, ex⟩
                    + F2R (beta := radix2) ⟨-my, ey⟩ < 0
              rw [F2R_Zopp, F2R_Zopp]
              linarith [F2R_gt_0 (⟨mx, ex⟩ : float radix2) hmx_pos,
                        F2R_gt_0 (⟨my, ey⟩ : float radix2) hmy_pos]
            exact (decide_eq_true hsum_lt).symm
        · -- sx ≠ sy: sandwich the round between -bpow emax and bpow emax.
          exfalso
          apply absurd Bz (not_le.mpr ?_)
          -- The sum is bounded between -bpow emax and bpow emax (strict).
          rw [abs_lt]
          have h_sum_eq : F2R (beta := radix2) (⟨mz, ez⟩ : float radix2)
              = B2R (B754_finite (prec := prec) (emax := emax) sx mx ex hx)
                + B2R (B754_finite (prec := prec) (emax := emax) sy my ey hy) := Hp.symm
          rw [h_sum_eq]
          refine ⟨?_, ?_⟩
          · -- Lower bound: round sum > -bpow emax.
            cases hsx : sx
            · -- sx = false, so sy = true.
              have hsy : sy = true := by
                cases sy
                · subst hsx; exact absurd rfl Hs
                · rfl
              subst hsy
              -- sum ≥ -F2R⟨my, ey⟩ since B2R x ≥ 0.
              have h_lower :
                  -F2R (beta := radix2) (⟨my, ey⟩ : float radix2) ≤
                  B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx)
                  + B2R (B754_finite (prec := prec) (emax := emax) true my ey hy) := by
                show -F2R (beta := radix2) (⟨my, ey⟩ : float radix2) ≤
                    F2R (beta := radix2) ⟨cond_Zopp false mx, ex⟩
                    + F2R (beta := radix2) ⟨cond_Zopp true my, ey⟩
                show -F2R (beta := radix2) (⟨my, ey⟩ : float radix2) ≤
                    F2R (beta := radix2) ⟨mx, ex⟩
                    + F2R (beta := radix2) ⟨-my, ey⟩
                rw [F2R_Zopp]
                linarith [F2R_ge_0 (⟨mx, ex⟩ : float radix2) (le_of_lt hmx_pos)]
              have h_round_ge :
                  -F2R (beta := radix2) (⟨my, ey⟩ : float radix2) ≤
                  round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
                    (B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx)
                    + B2R (B754_finite (prec := prec) (emax := emax) true my ey hy)) :=
                round_ge_generic radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp) (round_mode m)
                  hgen_neg_my h_lower
              linarith
            · -- sx = true, so sy = false.
              have hsy : sy = false := by
                cases sy
                · rfl
                · subst hsx; exact absurd rfl Hs
              subst hsy
              have h_lower :
                  -F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) ≤
                  B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx)
                  + B2R (B754_finite (prec := prec) (emax := emax) false my ey hy) := by
                show -F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) ≤
                    F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩
                    + F2R (beta := radix2) ⟨cond_Zopp false my, ey⟩
                show -F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) ≤
                    F2R (beta := radix2) ⟨-mx, ex⟩
                    + F2R (beta := radix2) ⟨my, ey⟩
                rw [F2R_Zopp]
                linarith [F2R_ge_0 (⟨my, ey⟩ : float radix2) (le_of_lt hmy_pos)]
              have h_round_ge :
                  -F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) ≤
                  round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
                    (B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx)
                    + B2R (B754_finite (prec := prec) (emax := emax) false my ey hy)) :=
                round_ge_generic radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp) (round_mode m)
                  hgen_neg_mx h_lower
              linarith
          · -- Upper bound: round sum < bpow emax.
            cases hsx : sx
            · have hsy : sy = true := by
                cases sy
                · subst hsx; exact absurd rfl Hs
                · rfl
              subst hsy
              have h_upper :
                  B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx)
                  + B2R (B754_finite (prec := prec) (emax := emax) true my ey hy) ≤
                  F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) := by
                show F2R (beta := radix2) ⟨cond_Zopp false mx, ex⟩
                    + F2R (beta := radix2) ⟨cond_Zopp true my, ey⟩
                    ≤ F2R (beta := radix2) (⟨mx, ex⟩ : float radix2)
                show F2R (beta := radix2) ⟨mx, ex⟩
                    + F2R (beta := radix2) ⟨-my, ey⟩
                    ≤ F2R (beta := radix2) (⟨mx, ex⟩ : float radix2)
                rw [F2R_Zopp]
                linarith [F2R_ge_0 (⟨my, ey⟩ : float radix2) (le_of_lt hmy_pos)]
              have h_round_le :
                  round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
                    (B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx)
                    + B2R (B754_finite (prec := prec) (emax := emax) true my ey hy)) ≤
                  F2R (beta := radix2) (⟨mx, ex⟩ : float radix2) :=
                round_le_generic radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp) (round_mode m)
                  hgen_pos_mx h_upper
              linarith
            · have hsy : sy = false := by
                cases sy
                · rfl
                · subst hsx; exact absurd rfl Hs
              subst hsy
              have h_upper :
                  B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx)
                  + B2R (B754_finite (prec := prec) (emax := emax) false my ey hy) ≤
                  F2R (beta := radix2) (⟨my, ey⟩ : float radix2) := by
                show F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩
                    + F2R (beta := radix2) ⟨cond_Zopp false my, ey⟩
                    ≤ F2R (beta := radix2) (⟨my, ey⟩ : float radix2)
                show F2R (beta := radix2) ⟨-mx, ex⟩
                    + F2R (beta := radix2) ⟨my, ey⟩
                    ≤ F2R (beta := radix2) (⟨my, ey⟩ : float radix2)
                rw [F2R_Zopp]
                linarith [F2R_ge_0 (⟨mx, ex⟩ : float radix2) (le_of_lt hmx_pos)]
              have h_round_le :
                  round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
                    (B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx)
                    + B2R (B754_finite (prec := prec) (emax := emax) false my ey hy)) ≤
                  F2R (beta := radix2) (⟨my, ey⟩ : float radix2) :=
                round_le_generic radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp) (round_mode m)
                  hgen_pos_my h_upper
              linarith
      -- Cases on whether |round F2R⟨mz,ez⟩| < bpow emax.
      split_ifs with h_lt
      · -- Bounded case.
        rw [if_pos h_lt] at h_bn
        obtain ⟨h_B2R, h_finite, h_sign⟩ := h_bn
        refine ⟨h_B2R, h_finite, ?_⟩
        rw [h_sign]
        -- compare (F2R⟨mz,ez⟩) 0: three cases.
        rcases lt_trichotomy (F2R (beta := radix2) (⟨mz, ez⟩ : float radix2)) 0
          with hlt | heq | hgt
        · rw [show compare (F2R (beta := radix2) (⟨mz, ez⟩ : float radix2)) (0 : ℝ)
              = Ordering.lt from compare_lt_iff_lt.mpr hlt]
        · -- F2R⟨mz, ez⟩ = 0: must have sx ≠ sy.
          rw [show compare (F2R (beta := radix2) (⟨mz, ez⟩ : float radix2)) (0 : ℝ)
              = Ordering.eq from compare_eq_iff_eq.mpr heq]
          -- Derive sx ≠ sy.
          have hxy_ne : sx ≠ sy := by
            intro Hs
            -- If sx = sy, sum is strictly positive or strictly negative, ≠ 0.
            have h_sum_ne : F2R (beta := radix2) (⟨mz, ez⟩ : float radix2) ≠ 0 := by
              rw [← Hp]; subst Hs
              cases sx
              · -- Both terms ≥ 0, but at least one > 0 (e.g., F2R⟨mx, ex⟩ > 0).
                have hBx_gt : 0 < B2R (B754_finite (prec := prec) (emax := emax) false mx ex hx) :=
                  F2R_gt_0 ⟨mx, ex⟩ hmx_pos
                have hBy_ge : 0 ≤ B2R (B754_finite (prec := prec) (emax := emax) false my ey hy) :=
                  F2R_ge_0 ⟨my, ey⟩ (le_of_lt hmy_pos)
                linarith
              · have hBx_lt : B2R (B754_finite (prec := prec) (emax := emax) true mx ex hx) < 0 := by
                  show F2R (beta := radix2) ⟨-mx, ex⟩ < 0
                  rw [F2R_Zopp]; linarith [F2R_gt_0 (⟨mx, ex⟩ : float radix2) hmx_pos]
                have hBy_le : B2R (B754_finite (prec := prec) (emax := emax) true my ey hy) ≤ 0 := by
                  show F2R (beta := radix2) ⟨-my, ey⟩ ≤ 0
                  rw [F2R_Zopp]; linarith [F2R_ge_0 (⟨my, ey⟩ : float radix2) (le_of_lt hmy_pos)]
                linarith
            exact h_sum_ne heq
          -- With sx ≠ sy, szero = (DN ? sx∨sy : sx∧sy).
          show (match m with | .mode_DN => (true : Bool) | _ => false) = _
          cases m <;> cases sx <;> cases sy <;>
            first | rfl | exact absurd rfl hxy_ne
        · rw [show compare (F2R (beta := radix2) (⟨mz, ez⟩ : float radix2)) (0 : ℝ)
              = Ordering.gt from compare_gt_iff_gt.mpr hgt]
      · -- Overflow case.
        rw [if_neg h_lt] at h_bn
        push_neg at h_lt
        obtain ⟨h_sx_sign, h_sx_sy⟩ := Sz h_lt
        refine ⟨?_, ?_⟩
        · -- B2FF Bplus = binary_overflow m (Bsign x). The bn gives Bsign-via-decide.
          rw [h_bn]
          show binary_overflow prec emax m (decide _) = binary_overflow prec emax m sx
          rw [← h_sx_sign]
        · -- Bsign x = Bsign y: from sx = sy.
          show sx = sy; exact h_sx_sy

/-- **`Bminus_eq_Bplus_Bopp`**: for non-NaN inputs, subtraction equals addition
of the negation. The NaN policies are irrelevant since NaN inputs never occur. -/
private theorem Bminus_eq_Bplus_Bopp (hp : 0 < prec) (hmax : prec < emax)
    (minus_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (plus_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (opp_nan : binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax)
    (Fx : is_finite x = true) (Fy : is_finite y = true) :
    Bminus hp hmax minus_nan m x y = Bplus hp hmax plus_nan m x (Bopp opp_nan y) := by
  cases x with
  | B754_nan _ _ _ => simp [is_finite] at Fx
  | B754_infinity _ => simp [is_finite] at Fx
  | B754_zero sx =>
    cases y with
    | B754_nan _ _ _ => simp [is_finite] at Fy
    | B754_infinity _ => simp [is_finite] at Fy
    | B754_zero sy => rfl
    | B754_finite sy my ey hy => rfl
  | B754_finite sx mx ex hx =>
    cases y with
    | B754_nan _ _ _ => simp [is_finite] at Fy
    | B754_infinity _ => simp [is_finite] at Fy
    | B754_zero sy => rfl
    | B754_finite sy my ey hy =>
      -- The substantive case: both call binary_normalize with the same mantissa
      -- (since cond_Zopp (!sy) m' = -cond_Zopp sy m', so subtraction = addition of opp).
      show binary_normalize hp hmax m
            (cond_Zopp sx (shl_align mx ex (min ex ey)).1
              - cond_Zopp sy (shl_align my ey (min ex ey)).1)
            (min ex ey)
            (match m with | .mode_DN => true | _ => false)
        = binary_normalize hp hmax m
            (cond_Zopp sx (shl_align mx ex (min ex ey)).1
              + cond_Zopp (!sy) (shl_align my ey (min ex ey)).1)
            (min ex ey)
            (match m with | .mode_DN => true | _ => false)
      congr 1
      cases sy <;> simp [cond_Zopp] <;> ring

/-- **`Bminus_correct`** (Coq line 1813): IEEE-754 subtraction correctness.

Derived from `Bplus_correct` applied to `(x, Bopp y)`. The sum becomes a
difference, the sign of the second operand flips, and the rest of the
correctness statement follows. -/
theorem Bminus_correct (hp : 0 < prec) (hmax : prec < emax)
    (minus_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax)
    (Fx : is_finite x = true) (Fy : is_finite y = true) :
    if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (B2R x - B2R y)| < bpow radix2 emax then
      B2R (Bminus hp hmax minus_nan m x y) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
          (B2R x - B2R y) ∧
      is_finite (Bminus hp hmax minus_nan m x y) = true ∧
      Bsign (Bminus hp hmax minus_nan m x y) =
        (match compare (B2R x - B2R y) (0 : ℝ) with
         | Ordering.eq =>
            match m with
            | .mode_DN => Bsign x || !(Bsign y)
            | _ => Bsign x && !(Bsign y)
         | Ordering.lt => true
         | Ordering.gt => false)
    else
      B2FF (Bminus hp hmax minus_nan m x y) = binary_overflow prec emax m (Bsign x)
        ∧ Bsign x = !(Bsign y) := by
  -- Build a dummy opp_nan policy (we know y is finite, so opp_nan is never used).
  let opp_nan : binary_float prec emax →
      {x : binary_float prec emax // is_nan x = true} := fun n => minus_nan n (B754_zero false)
  -- Apply Bplus_correct on (x, Bopp opp_nan y).
  have h_fin_neg_y : is_finite (Bopp opp_nan y) = true := by
    rw [is_finite_Bopp]; exact Fy
  have h_bplus := Bplus_correct hp hmax minus_nan m x (Bopp opp_nan y) Fx h_fin_neg_y
  -- Substitute B2R(Bopp y) = -B2R y, equivalently B2R x + B2R(Bopp y) = B2R x - B2R y.
  rw [B2R_Bopp] at h_bplus
  rw [show B2R x + -B2R y = B2R x - B2R y from by ring] at h_bplus
  -- Substitute Bsign(Bopp y) = !Bsign y (using is_nan y = false from Fy).
  have hy_not_nan : is_nan y = false := by
    cases y with
    | B754_zero _ => rfl
    | B754_infinity _ => simp [is_finite] at Fy
    | B754_nan _ _ _ => simp [is_finite] at Fy
    | B754_finite _ _ _ _ => rfl
  rw [show Bsign (Bopp opp_nan y) = !(Bsign y) from Bsign_Bopp opp_nan y hy_not_nan] at h_bplus
  -- Bridge Bminus to Bplus on (x, Bopp y).
  rw [Bminus_eq_Bplus_Bopp hp hmax minus_nan minus_nan opp_nan m x y Fx Fy]
  -- Now h_bplus matches the goal directly.
  exact h_bplus

/-! ## Bnormfr_mantissa: extract the integer mantissa of a normalized fraction -/

/-- **`Bnormfr_mantissa`** (Coq line 2249): for a finite float with canonical
exponent `-prec` (i.e., a value in `[1/2, 1)`), return the integer mantissa
`mx`. For any other input (zero/infinity/NaN, or a finite float with a
different exponent), return `0`. -/
def Bnormfr_mantissa (x : binary_float prec emax) : ℤ :=
  match x with
  | B754_finite _ mx ex _ => if ex = -prec then mx else 0
  | _ => 0

/-! ## Bldexp: scale by a power of two -/

/-- **`Bldexp`** (Coq line 2256): `Bldexp m f e = f · 2^e`, rounded under mode `m`.

For finite `f`, this re-uses `binary_round_correct` with the original mantissa
and adjusted exponent `ex + e`. For zero/infinity/nan, the result is `f`
itself (since multiplying by `2^e` preserves zero/infinity/nan). -/
noncomputable def Bldexp (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (f : binary_float prec emax) (e : ℤ) : binary_float prec emax :=
  match f with
  | B754_finite sx mx ex hb =>
    FF2B _ (binary_round_correct hp hmax m sx mx (ex + e) hb.1).1
  | _ => f

/-- **`Bldexp_correct`** (Coq line 2263): correctness of `Bldexp`.

When the rounded scaled value fits, `B2R (Bldexp m f e) = round (B2R f · 2^e)`,
finiteness is preserved, and the sign matches `f`. Otherwise, the result encodes
`binary_overflow` with `Bsign f`. -/
theorem Bldexp_correct (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (f : binary_float prec emax) (e : ℤ) :
    if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (B2R f * bpow radix2 e)| < bpow radix2 emax then
      B2R (Bldexp hp hmax m f e) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
          (B2R f * bpow radix2 e) ∧
      is_finite (Bldexp hp hmax m f e) = is_finite f ∧
      Bsign (Bldexp hp hmax m f e) = Bsign f
    else
      B2FF (Bldexp hp hmax m f e) = binary_overflow prec emax m (Bsign f) := by
  cases f with
  | B754_zero s =>
    -- B2R = 0, so the rounded value is 0, |0| < bpow emax, if-true branch.
    show (if _ < _ then _ else _)
    have h_B2R_zero : B2R (B754_zero s : binary_float prec emax) = 0 := rfl
    rw [h_B2R_zero, zero_mul, round_0, abs_zero, if_pos (bpow_gt_0 radix2 emax)]
    -- Bldexp on a zero returns the zero unchanged.
    have h_Bldexp_eq : Bldexp hp hmax m (B754_zero s : binary_float prec emax) e
        = B754_zero s := rfl
    rw [h_Bldexp_eq]
    exact ⟨rfl, rfl, rfl⟩
  | B754_infinity s =>
    show (if _ < _ then _ else _)
    have h_B2R_zero : B2R (B754_infinity s : binary_float prec emax) = 0 := rfl
    rw [h_B2R_zero, zero_mul, round_0, abs_zero, if_pos (bpow_gt_0 radix2 emax)]
    have h_Bldexp_eq : Bldexp hp hmax m (B754_infinity s : binary_float prec emax) e
        = B754_infinity s := rfl
    rw [h_Bldexp_eq]
    exact ⟨rfl, rfl, rfl⟩
  | B754_nan s pl h_pl =>
    show (if _ < _ then _ else _)
    have h_B2R_zero : B2R (B754_nan s pl h_pl : binary_float prec emax) = 0 := rfl
    rw [h_B2R_zero, zero_mul, round_0, abs_zero, if_pos (bpow_gt_0 radix2 emax)]
    have h_Bldexp_eq : Bldexp hp hmax m (B754_nan s pl h_pl : binary_float prec emax) e
        = B754_nan s pl h_pl := rfl
    rw [h_Bldexp_eq]
    exact ⟨rfl, rfl, rfl⟩
  | B754_finite sx mx ex hb =>
    -- B2R = F2R⟨cond_Zopp sx mx, ex⟩, so B2R * bpow e = F2R⟨cond_Zopp sx mx, ex + e⟩.
    have h_B2R_eq : B2R (B754_finite sx mx ex hb : binary_float prec emax) * bpow radix2 e
        = F2R (beta := radix2) ⟨cond_Zopp sx mx, ex + e⟩ := by
      show F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ * bpow radix2 e
          = F2R (beta := radix2) ⟨cond_Zopp sx mx, ex + e⟩
      unfold F2R
      show ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 ex * bpow radix2 e
          = ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 (ex + e)
      rw [bpow_plus, ← mul_assoc]
    rw [h_B2R_eq]
    -- Apply binary_round_correct.
    have h_brc := binary_round_correct hp hmax m sx mx (ex + e) hb.1
    simp only [] at h_brc
    obtain ⟨h_valid, h_cond⟩ := h_brc
    -- Bldexp on this finite float reduces to FF2B of the binary_round.
    have h_Bldexp_eq : Bldexp hp hmax m (B754_finite sx mx ex hb : binary_float prec emax) e
        = FF2B _ h_valid := rfl
    rw [h_Bldexp_eq]
    split_ifs with h_lt
    · rw [if_pos h_lt] at h_cond
      obtain ⟨h_F2R_round, h_finite, h_sign⟩ := h_cond
      refine ⟨?_, ?_, ?_⟩
      · rw [show B2R (FF2B _ _) = FF2R radix2 _ from B2R_FF2B _ _]
        exact h_F2R_round
      · rw [is_finite_FF2B]; exact h_finite
      · rw [Bsign_FF2B, h_sign]; rfl
    · rw [if_neg h_lt] at h_cond
      rw [B2FF_FF2B, h_cond]
      rfl

/-! ## Bfrexp: extract mantissa and exponent -/

/-- The integer core of `Bfrexp` (Coq lines 2302–2307). Two cases on the
mantissa's digit count: if `mx` already has `prec` digits, we keep it as
the F754_finite at exponent `-prec`; otherwise we left-shift it by
`d = prec - Zdigits mx` so the result is precisely `prec`-bit. -/
noncomputable def Ffrexp_core_binary (prec : ℤ) (s : Bool) (m e : ℤ) : full_float × ℤ :=
  if prec ≤ Zdigits radix2 m then
    (full_float.F754_finite s m (-prec), e + prec)
  else
    let d := prec - Zdigits radix2 m
    (full_float.F754_finite s (m * (radix2.val : ℤ)^d.toNat) (-prec), e + prec - d)

/-- **`Bfrexp_correct_aux`** (Coq line 2309): correctness of the integer
core for `Bfrexp`. Returns a `full_float` whose absolute value lies in
`[1/2, 1)` and whose product with `bpow e_out` equals the original
`F2R⟨cond_Zopp sx mx, ex⟩`.

The hypothesis `3 ≤ emax` (Coq's `Hemax`) is needed because we need
`emin = 3 - emax - prec ≤ -prec` so that `FLT_exp(0) = -prec` (not the
`emin` floor). -/
theorem Bfrexp_correct_aux (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (sx : Bool) (mx ex : ℤ) (hb : bounded prec emax mx ex) :
    valid_binary prec emax (Ffrexp_core_binary prec sx mx ex).1 ∧
    ((1/2 ≤ |FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1| ∧
      |FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1| < 1) ∧
     F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
       = FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1
         * bpow radix2 (Ffrexp_core_binary prec sx mx ex).2) := by
  -- Common facts.
  have h_mx_pos : 0 < mx := hb.1
  have h_mx_ne : mx ≠ 0 := by omega
  have h_mx_real_ne : (mx : ℝ) ≠ 0 := by exact_mod_cast h_mx_ne
  have h_abs_mx : |(mx : ℝ)| = (mx : ℝ) := abs_of_pos (by exact_mod_cast h_mx_pos)
  have h_Zdigits_pos : 0 < Zdigits radix2 mx := Zdigits_gt_0 radix2 h_mx_ne
  have h_emin_le : (3 - emax - prec) ≤ -prec := by omega
  -- Bound `Zdigits mx ≤ prec` from the canonical_mantissa condition.
  have h_Zdigits_le : Zdigits radix2 mx ≤ prec := by
    have hcm : FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex) = ex := hb.2.1
    unfold FLT_exp at hcm
    by_contra h_gt
    push_neg at h_gt
    have h_max_ge : max ((Zdigits radix2 mx + ex) - prec) (3 - emax - prec) ≥
        (Zdigits radix2 mx + ex) - prec := le_max_left _ _
    omega
  -- Magnitude bounds for `mx` from `Zdigits_correct`.
  obtain ⟨h_mx_low, h_mx_high⟩ := Zdigits_correct radix2 h_mx_ne
  rw [h_abs_mx] at h_mx_low h_mx_high
  -- `|cond_Zopp b m| = m` when `m ≥ 0`. We use it via F2R_Zabs + cond_Zopp.
  have h_abs_F2R : ∀ (b : Bool) (n e : ℤ) (_ : 0 ≤ n),
      |F2R (beta := radix2) ⟨cond_Zopp b n, e⟩| = F2R (beta := radix2) ⟨n, e⟩ := by
    intros b n e hn
    rw [← F2R_Zabs]
    have h_eq : |cond_Zopp b n| = n := by
      cases b
      · exact abs_of_nonneg hn
      · show |(-n)| = n; rw [abs_neg]; exact abs_of_nonneg hn
    rw [h_eq]
  -- Now dispatch on `Ffrexp_core_binary`.
  unfold Ffrexp_core_binary
  split_ifs with h_case
  · -- Case A: prec ≤ Zdigits mx, so equality with `h_Zdigits_le` gives Zdigits mx = prec.
    have h_Z_eq : Zdigits radix2 mx = prec := le_antisymm h_Zdigits_le h_case
    -- The `.1` and `.2` reduce iota.
    simp only [Prod.fst, Prod.snd]
    -- FF2R of F754_finite = F2R⟨cond_Zopp sx mx, -prec⟩.
    have h_FF2R : FF2R radix2 (full_float.F754_finite sx mx (-prec))
        = F2R (beta := radix2) ⟨cond_Zopp sx mx, -prec⟩ := rfl
    rw [h_FF2R]
    -- Bound: |F2R⟨cond_Zopp sx mx, -prec⟩| = mx * bpow(-prec).
    have h_abs_eq : |F2R (beta := radix2) ⟨cond_Zopp sx mx, -prec⟩|
        = (mx : ℝ) * bpow radix2 (-prec) := by
      rw [h_abs_F2R sx mx (-prec) (le_of_lt h_mx_pos)]
      rfl
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · -- F1: valid_binary = bounded prec emax mx (-prec)
      show bounded prec emax mx (-prec)
      refine ⟨h_mx_pos, ?_, by omega⟩
      show FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + (-prec)) = -prec
      rw [h_Z_eq]
      unfold FLT_exp
      have h_arg : prec + (-prec) - prec = -prec := by ring
      rw [h_arg]
      exact max_eq_left h_emin_le
    · -- F2: 1/2 ≤ |F2R⟨cond_Zopp sx mx, -prec⟩|
      rw [h_abs_eq]
      -- mx ≥ bpow(prec - 1) → mx * bpow(-prec) ≥ bpow(prec - 1) * bpow(-prec) = bpow(-1) = 1/2.
      have h_lower : bpow radix2 (prec - 1) ≤ (mx : ℝ) := by
        rw [← h_Z_eq]; exact h_mx_low
      have h_prod : bpow radix2 (prec - 1) * bpow radix2 (-prec) ≤ (mx : ℝ) * bpow radix2 (-prec) :=
        mul_le_mul_of_nonneg_right h_lower (bpow_ge_0 _ _)
      have h_eq : bpow radix2 (prec - 1) * bpow radix2 (-prec) = bpow radix2 (-1) := by
        rw [← bpow_plus]; congr 1; ring
      rw [h_eq] at h_prod
      have h_half : bpow radix2 (-1) = (1 : ℝ) / 2 := by
        unfold bpow
        show ((radix2.val : ℝ))^(-1 : ℤ) = 1/2
        show ((2 : ℤ) : ℝ)^(-1 : ℤ) = 1/2
        push_cast
        rw [zpow_neg, zpow_one]
        norm_num
      rw [h_half] at h_prod
      exact h_prod
    · -- F3: |F2R⟨cond_Zopp sx mx, -prec⟩| < 1
      rw [h_abs_eq]
      have h_upper : (mx : ℝ) < bpow radix2 prec := by
        rw [← h_Z_eq]; exact h_mx_high
      have h_prod : (mx : ℝ) * bpow radix2 (-prec) < bpow radix2 prec * bpow radix2 (-prec) :=
        mul_lt_mul_of_pos_right h_upper (bpow_gt_0 _ _)
      have h_eq : bpow radix2 prec * bpow radix2 (-prec) = 1 := by
        rw [← bpow_plus, show prec + (-prec) = 0 from by ring, bpow_zero]
      rw [h_eq] at h_prod
      exact h_prod
    · -- F4: F2R⟨cond_Zopp sx mx, ex⟩ = F2R⟨cond_Zopp sx mx, -prec⟩ * bpow(ex + prec)
      unfold F2R
      show ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 ex
          = ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 (-prec) * bpow radix2 (ex + prec)
      rw [mul_assoc, ← bpow_plus]
      congr 2; ring
  · -- Case B: prec > Zdigits mx.
    push_neg at h_case
    have h_Z_lt : Zdigits radix2 mx < prec := h_case
    -- Set d = prec - Zdigits mx > 0.
    set d : ℤ := prec - Zdigits radix2 mx with hd_def
    have hd_pos : 0 < d := by simp [hd_def]; omega
    have hd_nn : 0 ≤ d := le_of_lt hd_pos
    -- Shifted mantissa.
    set ms : ℤ := mx * (radix2.val : ℤ)^d.toNat with hms_def
    have h_pow_pos : 0 < ((radix2.val : ℤ)^d.toNat : ℤ) := by
      apply pow_pos; exact radix2.radix_gt_0
    have h_ms_pos : 0 < ms := by
      simp [hms_def]; exact mul_pos h_mx_pos h_pow_pos
    have h_ms_ne : ms ≠ 0 := by omega
    have h_ms_real_ne : (ms : ℝ) ≠ 0 := by exact_mod_cast h_ms_ne
    -- Key: Zdigits ms = Zdigits mx + d = prec.
    have h_Zd_ms : Zdigits radix2 ms = prec := by
      rw [hms_def, Zdigits_mult_Zpower radix2 h_mx_ne hd_nn]
      simp [hd_def]
    simp only [Prod.fst, Prod.snd]
    -- FF2R of F754_finite = F2R⟨cond_Zopp sx ms, -prec⟩.
    have h_FF2R : FF2R radix2 (full_float.F754_finite sx ms (-prec))
        = F2R (beta := radix2) ⟨cond_Zopp sx ms, -prec⟩ := rfl
    rw [h_FF2R]
    -- Bound: |F2R⟨cond_Zopp sx ms, -prec⟩| = ms * bpow(-prec) = mx * bpow(-Zdigits mx).
    have h_ms_cast : ((ms : ℤ) : ℝ) = (mx : ℝ) * bpow radix2 d := by
      rw [hms_def, ← IZR_Zpower radix2 hd_nn]
      push_cast; ring
    have h_abs_eq : |F2R (beta := radix2) ⟨cond_Zopp sx ms, -prec⟩|
        = (mx : ℝ) * bpow radix2 (- Zdigits radix2 mx) := by
      rw [h_abs_F2R sx ms (-prec) (le_of_lt h_ms_pos)]
      show ((ms : ℤ) : ℝ) * bpow radix2 (-prec)
          = (mx : ℝ) * bpow radix2 (- Zdigits radix2 mx)
      rw [h_ms_cast, mul_assoc, ← bpow_plus]
      rw [show d + (-prec) = - Zdigits radix2 mx from by simp [hd_def]; ring]
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · -- F1: bounded prec emax ms (-prec).
      show bounded prec emax ms (-prec)
      refine ⟨h_ms_pos, ?_, by omega⟩
      show FLT_exp (3 - emax - prec) prec (Zdigits radix2 ms + (-prec)) = -prec
      rw [h_Zd_ms]
      unfold FLT_exp
      have h_arg : prec + (-prec) - prec = -prec := by ring
      rw [h_arg]
      exact max_eq_left h_emin_le
    · -- F2: 1/2 ≤ mx * bpow(-Zdigits mx).
      rw [h_abs_eq]
      have h_prod :
          bpow radix2 (Zdigits radix2 mx - 1) * bpow radix2 (- Zdigits radix2 mx) ≤
            (mx : ℝ) * bpow radix2 (- Zdigits radix2 mx) :=
        mul_le_mul_of_nonneg_right h_mx_low (bpow_ge_0 _ _)
      have h_eq : bpow radix2 (Zdigits radix2 mx - 1) * bpow radix2 (- Zdigits radix2 mx)
          = bpow radix2 (-1) := by
        rw [← bpow_plus]; congr 1; ring
      rw [h_eq] at h_prod
      have h_half : bpow radix2 (-1) = (1 : ℝ) / 2 := by
        unfold bpow
        show ((2 : ℤ) : ℝ)^(-1 : ℤ) = 1/2
        push_cast
        rw [zpow_neg, zpow_one]
        norm_num
      rw [h_half] at h_prod
      exact h_prod
    · -- F3: mx * bpow(-Zdigits mx) < 1.
      rw [h_abs_eq]
      have h_prod : (mx : ℝ) * bpow radix2 (- Zdigits radix2 mx) <
          bpow radix2 (Zdigits radix2 mx) * bpow radix2 (- Zdigits radix2 mx) :=
        mul_lt_mul_of_pos_right h_mx_high (bpow_gt_0 _ _)
      have h_eq : bpow radix2 (Zdigits radix2 mx) * bpow radix2 (- Zdigits radix2 mx) = 1 := by
        rw [← bpow_plus, show Zdigits radix2 mx + (-Zdigits radix2 mx) = 0 from by ring,
            bpow_zero]
      rw [h_eq] at h_prod
      exact h_prod
    · -- F4: F2R⟨cond_Zopp sx mx, ex⟩ = F2R⟨cond_Zopp sx ms, -prec⟩ * bpow(ex + prec - d).
      unfold F2R
      show ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 ex
          = ((cond_Zopp sx ms : ℤ) : ℝ) * bpow radix2 (-prec) * bpow radix2 (ex + prec - d)
      -- cond_Zopp sx ms = cond_Zopp sx mx * 2^d.toNat (algebraic).
      have h_cond_Zopp_cast : ((cond_Zopp sx ms : ℤ) : ℝ)
          = ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 d := by
        have h_int : cond_Zopp sx ms = cond_Zopp sx mx * (radix2.val : ℤ)^d.toNat := by
          cases sx
          · simp [hms_def]
          · show -ms = -mx * (radix2.val : ℤ)^d.toNat
            rw [hms_def]; ring
        rw [h_int, ← IZR_Zpower radix2 hd_nn]
        push_cast; ring
      rw [h_cond_Zopp_cast]
      rw [show ((cond_Zopp sx mx : ℤ) : ℝ) * bpow radix2 d * bpow radix2 (-prec)
              * bpow radix2 (ex + prec - d)
            = ((cond_Zopp sx mx : ℤ) : ℝ)
              * (bpow radix2 d * bpow radix2 (-prec) * bpow radix2 (ex + prec - d))
            from by ring]
      congr 1
      rw [← bpow_plus, ← bpow_plus]
      congr 1
      simp [hd_def]; ring

/-- **`Bfrexp`** (Coq line 2406): split a finite float into a normalized
mantissa in `[1/2, 1)` and an integer exponent. Non-finite floats are
returned unchanged with a sentinel exponent `-2·emax - prec`. -/
noncomputable def Bfrexp (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (f : binary_float prec emax) : binary_float prec emax × ℤ :=
  match f with
  | B754_finite sx mx ex hb =>
    (FF2B (Ffrexp_core_binary prec sx mx ex).1
       (Bfrexp_correct_aux hp hmax hemax sx mx ex hb).1,
     (Ffrexp_core_binary prec sx mx ex).2)
  | _ => (f, -2 * emax - prec)

/-- **`Bfrexp_correct`** (Coq line 2414): on strictly-finite floats,
`Bfrexp f = (z, e)` satisfies `1/2 ≤ |B2R z| < 1`, `B2R f = B2R z · 2^e`,
and `e = mag (B2R f)`. -/
theorem Bfrexp_correct (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (f : binary_float prec emax) (hf : is_finite_strict f = true) :
    (1/2 ≤ |B2R (Bfrexp hp hmax hemax f).1| ∧
     |B2R (Bfrexp hp hmax hemax f).1| < 1) ∧
    B2R f = B2R (Bfrexp hp hmax hemax f).1 * bpow radix2 (Bfrexp hp hmax hemax f).2 ∧
    (Bfrexp hp hmax hemax f).2 = mag radix2 (B2R f) := by
  cases f with
  | B754_zero _ => simp [is_finite_strict] at hf
  | B754_infinity _ => simp [is_finite_strict] at hf
  | B754_nan _ _ _ => simp [is_finite_strict] at hf
  | B754_finite sx mx ex hb =>
    obtain ⟨_, ⟨h_low, h_high⟩, h_eq⟩ :=
      Bfrexp_correct_aux hp hmax hemax sx mx ex hb
    have h_Bfrexp : Bfrexp hp hmax hemax (B754_finite sx mx ex hb : binary_float prec emax)
        = (FF2B (Ffrexp_core_binary prec sx mx ex).1
            (Bfrexp_correct_aux hp hmax hemax sx mx ex hb).1,
           (Ffrexp_core_binary prec sx mx ex).2) := rfl
    rw [h_Bfrexp]
    have h_B2R_FF2B : B2R (FF2B (Ffrexp_core_binary prec sx mx ex).1
          (Bfrexp_correct_aux hp hmax hemax sx mx ex hb).1 : binary_float prec emax)
        = FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1 := B2R_FF2B _ _
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h_B2R_FF2B]; exact h_low
    · rw [h_B2R_FF2B]; exact h_high
    · rw [h_B2R_FF2B]
      show F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
          = FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1
            * bpow radix2 (Ffrexp_core_binary prec sx mx ex).2
      exact h_eq
    · -- e_out = mag(B2R f). From h_eq: B2R f = FF2R z * bpow e_out.
      -- |FF2R z| ∈ [1/2, 1) → FF2R z ≠ 0 → mag(FF2R z) = 0.
      have h_z_ne : FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1 ≠ 0 := by
        intro h_z_eq
        rw [h_z_eq, abs_zero] at h_low
        linarith
      have h_half_eq : bpow radix2 (-1) = (1 : ℝ) / 2 := by
        unfold bpow
        show ((2 : ℤ) : ℝ)^(-1 : ℤ) = 1/2
        push_cast; rw [zpow_neg, zpow_one]; norm_num
      have h_mag_z : mag radix2 (FF2R radix2 (Ffrexp_core_binary prec sx mx ex).1) = 0 := by
        apply mag_unique radix2
        · rw [show (0 : ℤ) - 1 = -1 from by ring, h_half_eq]; exact h_low
        · rw [bpow_zero]; exact h_high
      show (Ffrexp_core_binary prec sx mx ex).2
          = mag radix2 (F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩)
      rw [h_eq, mag_mult_bpow radix2 h_z_ne, h_mag_z]
      ring

/-! ## Bone: the constant 1 -/

/-- Internal helper: the three facts about `binary_round ... false 1 0`
that the `Bone_*` lemmas all rely on. Established by `binary_round_correct`
combined with `round_generic` (since `1` is already in `FLT` format). -/
private lemma Bone_aux (hp : 0 < prec) (hmax : prec < emax) :
    FF2R radix2 (binary_round prec emax mode.mode_NE false 1 0) = 1 ∧
    is_finite_FF (binary_round prec emax mode.mode_NE false 1 0) = true ∧
    sign_FF (binary_round prec emax mode.mode_NE false 1 0) = false := by
  have h_brc := binary_round_correct hp hmax mode.mode_NE false 1 0 Int.one_pos
  simp only [cond_Zopp_false] at h_brc
  obtain ⟨_, h_cond⟩ := h_brc
  have h_F2R_1 : F2R (beta := radix2) ⟨(1 : ℤ), 0⟩ = (1 : ℝ) := by
    show ((1 : ℤ) : ℝ) * bpow radix2 0 = 1
    rw [bpow_zero]; norm_num
  have h_1_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec) 1 := by
    rw [← h_F2R_1]
    apply generic_format_F2R radix2 (FLT_exp (3 - emax - prec) prec) 1 0
    intro _
    rw [h_F2R_1]
    show FLT_exp (3 - emax - prec) prec (mag radix2 1) ≤ 0
    rw [mag_1]
    unfold FLT_exp
    omega
  have h_round_1 : round radix2 (FLT_exp (3 - emax - prec) prec)
      (round_mode mode.mode_NE) 1 = 1 :=
    round_generic radix2 _ _ h_1_fmt
  have h_abs_1 : |(1 : ℝ)| < bpow radix2 emax := by
    rw [abs_one]
    have h_pos : bpow radix2 0 < bpow radix2 emax :=
      bpow_lt radix2 (by omega : (0 : ℤ) < emax)
    rwa [bpow_zero] at h_pos
  rw [h_F2R_1, h_round_1] at h_cond
  rw [if_pos h_abs_1] at h_cond
  exact h_cond

/-- **`Bone`** (Coq line 2170): the IEEE float representing `1`. -/
noncomputable def Bone (hp : 0 < prec) (hmax : prec < emax) : binary_float prec emax :=
  FF2B (binary_round prec emax mode.mode_NE false 1 0)
    (binary_round_correct hp hmax mode.mode_NE false 1 0 Int.one_pos).1

/-- **`Bone_correct`** (Coq line 2172): `B2R Bone = 1`. -/
theorem Bone_correct (hp : 0 < prec) (hmax : prec < emax) :
    B2R (Bone hp hmax : binary_float prec emax) = 1 := by
  unfold Bone
  rw [B2R_FF2B]
  exact (Bone_aux hp hmax).1

/-- **`is_finite_Bone`** (Coq line 2192): `Bone` is finite. -/
theorem is_finite_Bone (hp : 0 < prec) (hmax : prec < emax) :
    is_finite (Bone hp hmax : binary_float prec emax) = true := by
  unfold Bone
  rw [is_finite_FF2B]
  exact (Bone_aux hp hmax).2.1

/-- **`Bsign_Bone`** (Coq line 2198): `Bsign Bone = false`. -/
theorem Bsign_Bone (hp : 0 < prec) (hmax : prec < emax) :
    Bsign (Bone hp hmax : binary_float prec emax) = false := by
  unfold Bone
  rw [Bsign_FF2B]
  exact (Bone_aux hp hmax).2.2

/-! ## Bulp: unit in the last place -/

/-- **`Bulp`** (Coq line 2436): the unit in the last place of `x`. Computed
as `Bone · 2^(fexp e)` where `e = (Bfrexp x).2`. -/
noncomputable def Bulp (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (x : binary_float prec emax) : binary_float prec emax :=
  Bldexp hp hmax mode.mode_NE (Bone hp hmax)
    (FLT_exp (3 - emax - prec) prec (Bfrexp hp hmax hemax x).2)

/-- Internal helper: applying `Bldexp` to `Bone` with an exponent whose
`bpow` is in format and bounded by `bpow emax` yields exactly `bpow e'`,
preserving finiteness and the sign of `Bone`. -/
private lemma Bldexp_Bone_eq (hp : 0 < prec) (hmax : prec < emax) (e' : ℤ)
    (h_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec) (bpow radix2 e'))
    (h_bnd : bpow radix2 e' < bpow radix2 emax) :
    B2R (Bldexp hp hmax mode.mode_NE (Bone hp hmax) e' : binary_float prec emax)
      = bpow radix2 e' ∧
    is_finite (Bldexp hp hmax mode.mode_NE (Bone hp hmax) e' : binary_float prec emax)
      = true ∧
    Bsign (Bldexp hp hmax mode.mode_NE (Bone hp hmax) e' : binary_float prec emax)
      = false := by
  have h_bldexp := Bldexp_correct hp hmax mode.mode_NE (Bone hp hmax) e'
  rw [Bone_correct hp hmax, one_mul] at h_bldexp
  have h_round_eq : round radix2 (FLT_exp (3 - emax - prec) prec)
      (round_mode mode.mode_NE) (bpow radix2 e') = bpow radix2 e' :=
    round_generic radix2 _ _ h_fmt
  rw [h_round_eq] at h_bldexp
  have h_abs_bnd : |bpow radix2 e'| < bpow radix2 emax := by
    rw [abs_of_pos (bpow_gt_0 _ _)]; exact h_bnd
  rw [if_pos h_abs_bnd] at h_bldexp
  obtain ⟨h_b2r, h_fin, h_sign⟩ := h_bldexp
  refine ⟨h_b2r, ?_, ?_⟩
  · rw [h_fin]; exact is_finite_Bone hp hmax
  · rw [h_sign]; exact Bsign_Bone hp hmax

/-- **`Bulp_correct`** (Coq line 2438): on finite floats,
`B2R (Bulp x) = ulp (B2R x)`, plus finiteness and sign = false. -/
theorem Bulp_correct (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (x : binary_float prec emax) (hf : is_finite x = true) :
    B2R (Bulp hp hmax hemax x)
      = ulp radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
    is_finite (Bulp hp hmax hemax x) = true ∧
    Bsign (Bulp hp hmax hemax x) = false := by
  cases x with
  | B754_infinity s => simp [is_finite] at hf
  | B754_nan s pl pl_h => simp [is_finite] at hf
  | B754_zero s =>
    -- Bfrexp returns (B754_zero s, -2*emax - prec).
    have h_Bfrexp_snd : (Bfrexp hp hmax hemax (B754_zero s : binary_float prec emax)).2
        = -2 * emax - prec := rfl
    -- fexp(-2*emax - prec) = 3 - emax - prec = emin.
    have h_fexp_eq : FLT_exp (3 - emax - prec) prec (-2 * emax - prec) = 3 - emax - prec := by
      unfold FLT_exp; apply max_eq_right; omega
    unfold Bulp
    rw [h_Bfrexp_snd, h_fexp_eq]
    -- bpow(emin) in format.
    have h_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
        (bpow radix2 (3 - emax - prec)) := by
      apply generic_format_bpow' radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp)
      unfold FLT_exp; apply max_le _ (le_refl _); omega
    have h_bnd : bpow radix2 (3 - emax - prec) < bpow radix2 emax :=
      bpow_lt radix2 (by omega)
    obtain ⟨h_b2r, h_fin, h_sign⟩ := Bldexp_Bone_eq hp hmax (3 - emax - prec) h_fmt h_bnd
    refine ⟨?_, h_fin, h_sign⟩
    rw [h_b2r]
    -- ulp(0) = bpow(emin) since negligible_exp witness n ≤ emin gives fexp n = emin.
    show bpow radix2 (3 - emax - prec)
        = ulp radix2 (FLT_exp (3 - emax - prec) prec)
            (B2R (B754_zero s : binary_float prec emax))
    have h_B2R_zero : B2R (B754_zero s : binary_float prec emax) = 0 := rfl
    rw [h_B2R_zero]
    unfold ulp
    rw [if_pos rfl]
    obtain ⟨n, h_neg, h_n_le⟩ := negligible_exp_FLT radix2 (3 - emax - prec) prec hp
    rw [h_neg]
    show bpow radix2 (3 - emax - prec)
        = bpow radix2 (FLT_exp (3 - emax - prec) prec n)
    have h_fexp_n : FLT_exp (3 - emax - prec) prec n = 3 - emax - prec := by
      unfold FLT_exp; apply max_eq_right; omega
    rw [h_fexp_n]
  | B754_finite sx mx ex hb =>
    -- B2R x = F2R⟨cond_Zopp sx mx, ex⟩ ≠ 0.
    have h_mx_pos : 0 < mx := hb.1
    have h_B2R_ne : B2R (B754_finite sx mx ex hb : binary_float prec emax) ≠ 0 := by
      show F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ ≠ 0
      apply F2R_neq_0
      show cond_Zopp sx mx ≠ 0
      cases sx
      · show mx ≠ 0; omega
      · show -mx ≠ 0; omega
    -- is_finite_strict.
    have h_finite_strict : is_finite_strict
        (B754_finite sx mx ex hb : binary_float prec emax) = true := rfl
    -- (Bfrexp x).2 = mag (B2R x).
    obtain ⟨_, _, h_mag_eq⟩ := Bfrexp_correct hp hmax hemax
        (B754_finite sx mx ex hb : binary_float prec emax) h_finite_strict
    -- Let e' = fexp((Bfrexp x).2) = fexp(mag (B2R x)) = cexp (B2R x).
    set e' := FLT_exp (3 - emax - prec) prec
      (Bfrexp hp hmax hemax (B754_finite sx mx ex hb : binary_float prec emax)).2 with he'_def
    have h_e'_eq : e' = cexp radix2 (FLT_exp (3 - emax - prec) prec)
        (B2R (B754_finite sx mx ex hb : binary_float prec emax)) := by
      rw [he'_def, h_mag_eq]; rfl
    -- bpow e' in format.
    have h_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec) (bpow radix2 e') := by
      apply generic_format_bpow' radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp)
      rw [h_e'_eq]
      -- fexp(cexp x) ≤ cexp x. This is small-regime stability or direct from Valid_exp.
      show FLT_exp (3 - emax - prec) prec
          (FLT_exp (3 - emax - prec) prec
            (mag radix2 (B2R (B754_finite sx mx ex hb : binary_float prec emax))))
        ≤ FLT_exp (3 - emax - prec) prec
            (mag radix2 (B2R (B754_finite sx mx ex hb : binary_float prec emax)))
      -- FLT_exp(FLT_exp k) ≤ FLT_exp k: FLT_exp k = max(k - prec, emin).
      -- FLT_exp(max(k-prec, emin)) = max(max(k-prec, emin) - prec, emin).
      -- ≤ max(k-prec, emin) iff max(k-prec, emin) - prec ≤ max(k-prec, emin), i.e., prec ≥ 0 ✓.
      unfold FLT_exp; omega
    -- |bpow e'| < bpow emax: need e' < emax.
    have h_mag_le : mag radix2 (B2R (B754_finite sx mx ex hb : binary_float prec emax)) ≤ emax := by
      apply mag_le_bpow radix2 h_B2R_ne
      exact abs_B2R_lt_emax hp hmax _
    have h_e'_lt : e' < emax := by
      rw [h_e'_eq]
      show FLT_exp (3 - emax - prec) prec _ < emax
      unfold FLT_exp
      have h1 : mag radix2 (B2R (B754_finite sx mx ex hb : binary_float prec emax)) - prec < emax := by
        omega
      have h2 : (3 - emax - prec) < emax := by omega
      exact max_lt h1 h2
    have h_bnd : bpow radix2 e' < bpow radix2 emax := bpow_lt radix2 h_e'_lt
    unfold Bulp
    rw [← he'_def]
    obtain ⟨h_b2r, h_fin, h_sign⟩ := Bldexp_Bone_eq hp hmax e' h_fmt h_bnd
    refine ⟨?_, h_fin, h_sign⟩
    rw [h_b2r]
    -- ulp(B2R x) = bpow(cexp(B2R x)) = bpow e' (since B2R x ≠ 0).
    rw [ulp_neq_0 radix2 _ h_B2R_ne, ← h_e'_eq]

/-! ## Bpred_pos: predecessor for positive finite floats -/

/-- **`Bpred_pos`** (Coq line 2496): the predecessor of a positive finite float.

For `B754_finite _ mx _ _`: if `2 · mx = 2^prec` (the float is exactly a power
of two — `mx` is at its minimum value with the leading bit set), then the
predecessor straddles an exponent boundary, so subtract `bpow(fexp(e-1))`
where `e = (Bfrexp x).2`. Otherwise the predecessor is one ulp below `x`.
Non-finite inputs are returned unchanged (only meaningful for positive finite). -/
noncomputable def Bpred_pos (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (pred_pos_nan : binary_float prec emax →
                      {z : binary_float prec emax // is_nan z = true})
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | B754_finite _ mx _ _ =>
    let d :=
      if 2 * mx = 2 ^ prec.toNat then
        Bldexp hp hmax mode.mode_NE (Bone hp hmax)
          (FLT_exp (3 - emax - prec) prec ((Bfrexp hp hmax hemax x).2 - 1))
      else
        Bulp hp hmax hemax x
    Bminus hp hmax (fun a _ => pred_pos_nan a) mode.mode_NE x d
  | _ => x

/-- **`Bpred_pos_correct`** (Coq line 2508): on a positive finite float,
`Bpred_pos` computes the predecessor in the FLT format, is finite, and
has positive sign.

The conclusion `B2R = pred_pos` splits four ways on `(2·mx = 2^prec, Hd)` and
`(B2R x = bpow(mag-1), Hpred)`:
- `(Hd, Hpred)`: `d = bpow(fexp(mag-1))` and `x = bpow(mag-1)`. Match by
  `generic_format_pred_pos`.
- `(Hd, ¬Hpred)`: impossible — `Hd` forces `mx = 2^(prec-1)`, hence
  `x = bpow(prec-1+ex) = bpow(mag-1)`.
- `(¬Hd, Hpred)`: `d = ulp(x)` and `x = bpow(mag-1)`. The trick: in this
  subcase `mag(x) ≤ emin + prec`, so `fexp(mag) = fexp(mag-1) = emin`,
  and `ulp(x) = bpow(fexp(mag-1))`.
- `(¬Hd, ¬Hpred)`: `d = ulp(x)` and `pred_pos = x - ulp(x)`. Direct. -/
theorem Bpred_pos_correct (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (pred_pos_nan : binary_float prec emax →
                      {z : binary_float prec emax // is_nan z = true})
    (x : binary_float prec emax) (hpos : 0 < B2R x) :
    B2R (Bpred_pos hp hmax hemax pred_pos_nan x)
      = pred_pos radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
    is_finite (Bpred_pos hp hmax hemax pred_pos_nan x) = true ∧
    Bsign (Bpred_pos hp hmax hemax pred_pos_nan x) = false := by
  -- The three non-finite cases have B2R = 0, contradicting hpos.
  cases x with
  | B754_zero s =>
    have h_b2r : B2R (B754_zero s : binary_float prec emax) = 0 := rfl
    linarith
  | B754_infinity s =>
    have h_b2r : B2R (B754_infinity s : binary_float prec emax) = 0 := rfl
    linarith
  | B754_nan s pl hpl =>
    have h_b2r : B2R (B754_nan s pl hpl : binary_float prec emax) = 0 := rfl
    linarith
  | B754_finite sx mx ex hb =>
    -- Derive sx = false from 0 < B2R.
    have h_sx : sx = false := by
      cases sx
      · rfl
      · exfalso
        have h_neg : B2R (B754_finite true mx ex hb : binary_float prec emax) ≤ 0 := by
          show F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩ ≤ 0
          show ((cond_Zopp true mx : ℤ) : ℝ) * bpow radix2 ex ≤ 0
          have h_cz : (cond_Zopp true mx : ℤ) = -mx := rfl
          rw [h_cz]
          have hmx_pos : (0 : ℤ) ≤ mx := by linarith [hb.1]
          have h_mx_real_nn : (0 : ℝ) ≤ (mx : ℝ) := by exact_mod_cast hmx_pos
          have h_neg_mx : ((-mx : ℤ) : ℝ) ≤ 0 := by push_cast; linarith
          exact mul_nonpos_of_nonpos_of_nonneg h_neg_mx (le_of_lt (bpow_gt_0 _ _))
        linarith
    subst h_sx
    -- Abbreviations and base facts.
    set x' := (B754_finite false mx ex hb : binary_float prec emax) with hx'_def
    have h_x'_fin_strict : is_finite_strict x' = true := rfl
    have h_x'_fin : is_finite x' = true := rfl
    have hpos_x' : 0 < B2R x' := hpos
    have h_B2R_ne : B2R x' ≠ 0 := ne_of_gt hpos_x'
    have h_x'_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec) (B2R x') :=
      generic_format_B2R x'
    -- Bfrexp_correct: (Bfrexp x').2 = mag(B2R x').
    obtain ⟨_, _, h_mag_eq⟩ := Bfrexp_correct hp hmax hemax x' h_x'_fin_strict
    -- Set e = (Bfrexp x').2 = mag(B2R x').
    set e := (Bfrexp hp hmax hemax x').2 with he_def
    have h_e_mag : e = mag radix2 (B2R x') := h_mag_eq
    -- abs_B2R_lt_emax: |B2R x'| < bpow emax, so mag(B2R x') ≤ emax.
    have h_mag_le_emax : mag radix2 (B2R x') ≤ emax :=
      mag_le_bpow radix2 h_B2R_ne (abs_B2R_lt_emax hp hmax x')
    -- abs_B2R_ge_emin + mag_ge_bpow: emin + 1 ≤ mag(B2R x'), i.e., emin ≤ mag - 1.
    have h_emin_le_mag : (3 - emax - prec) + 1 ≤ mag radix2 (B2R x') := by
      apply mag_ge_bpow radix2
      have h_eq : (3 - emax - prec) + 1 - 1 = 3 - emax - prec := by ring
      rw [h_eq]
      exact abs_B2R_ge_emin hp x' h_x'_fin_strict
    -- Let fexp_em1 := FLT_exp(e - 1). It's the exponent for the "boundary" branch.
    set fexp_em1 := FLT_exp (3 - emax - prec) prec (e - 1) with hfexp_em1_def
    -- fexp_em1 ≤ e - 1: both arguments of max are ≤ e - 1.
    have h_fexp_em1_le : fexp_em1 ≤ e - 1 := by
      rw [hfexp_em1_def, h_e_mag]
      unfold FLT_exp
      have h1 : mag radix2 (B2R x') - 1 - prec ≤ mag radix2 (B2R x') - 1 := by linarith
      have h2 : (3 - emax - prec) ≤ mag radix2 (B2R x') - 1 := by linarith
      exact max_le h1 h2
    -- bpow(fexp_em1) is in format.
    have h_fmt_bpow : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
        (bpow radix2 fexp_em1) := by
      apply generic_format_bpow' radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp)
      rw [hfexp_em1_def]; unfold FLT_exp; omega
    -- round(bpow(fexp_em1)) = bpow(fexp_em1) (in format), and bpow < bpow emax.
    have h_bpow_lt_emax : bpow radix2 fexp_em1 < bpow radix2 emax := by
      apply bpow_lt
      rw [hfexp_em1_def, h_e_mag]
      unfold FLT_exp
      have h1 : mag radix2 (B2R x') - 1 - prec < emax := by linarith
      have h2 : 3 - emax - prec < emax := by linarith
      exact max_lt h1 h2
    have h_round_bpow_lt : |round radix2 (FLT_exp (3 - emax - prec) prec)
        (round_mode mode.mode_NE) (bpow radix2 fexp_em1)| < bpow radix2 emax := by
      rw [round_generic _ _ _ h_fmt_bpow, abs_of_pos (bpow_gt_0 _ _)]
      exact h_bpow_lt_emax
    -- Bldexp(Bone, fexp_em1) is well-defined.
    have h_bldexp := Bldexp_correct hp hmax mode.mode_NE (Bone hp hmax) fexp_em1
    rw [Bone_correct, one_mul, if_pos h_round_bpow_lt] at h_bldexp
    obtain ⟨h_bldexp_b2r, h_bldexp_fin_eq, h_bldexp_sign_eq⟩ := h_bldexp
    have h_bldexp_b2r' : B2R (Bldexp hp hmax mode.mode_NE (Bone hp hmax) fexp_em1
                                : binary_float prec emax) = bpow radix2 fexp_em1 := by
      rw [h_bldexp_b2r, round_generic _ _ _ h_fmt_bpow]
    have h_bldexp_fin : is_finite (Bldexp hp hmax mode.mode_NE (Bone hp hmax) fexp_em1
                                    : binary_float prec emax) = true := by
      rw [h_bldexp_fin_eq]; exact is_finite_Bone hp hmax
    -- Bulp_correct.
    obtain ⟨h_bulp_b2r, h_bulp_fin, _⟩ := Bulp_correct hp hmax hemax x' h_x'_fin
    -- Set d.
    set d := (if 2 * mx = 2 ^ prec.toNat then
                Bldexp hp hmax mode.mode_NE (Bone hp hmax) fexp_em1
              else
                Bulp hp hmax hemax x' : binary_float prec emax) with hd_def
    -- is_finite d.
    have h_d_fin : is_finite d = true := by
      rw [hd_def]; split_ifs
      · exact h_bldexp_fin
      · exact h_bulp_fin
    -- 0 ≤ B2R d.
    have h_d_nonneg : 0 ≤ B2R d := by
      rw [hd_def]; split_ifs
      · rw [h_bldexp_b2r']; exact le_of_lt (bpow_gt_0 _ _)
      · rw [h_bulp_b2r]; exact ulp_ge_0 radix2 _ _
    -- B2R d ≤ B2R x'.
    have h_d_le_x : B2R d ≤ B2R x' := by
      rw [hd_def]; split_ifs
      · -- Bldexp case: B2R d = bpow(fexp_em1) ≤ bpow(e - 1) ≤ B2R x'.
        rw [h_bldexp_b2r']
        calc bpow radix2 fexp_em1
            ≤ bpow radix2 (e - 1) := bpow_le radix2 h_fexp_em1_le
          _ = bpow radix2 (mag radix2 (B2R x') - 1) := by rw [h_e_mag]
          _ ≤ |B2R x'| := bpow_mag_le radix2 h_B2R_ne
          _ = B2R x' := abs_of_pos hpos_x'
      · -- Bulp case: B2R d = ulp(x') ≤ x' since x' > 0 and x' ∈ format.
        rw [h_bulp_b2r]
        exact ulp_le_id radix2 _ hpos_x' h_x'_fmt
    -- |round (B2R x' - B2R d)| < bpow emax. Used to fire Bminus_correct's if-true.
    have h_x_minus_d_nonneg : 0 ≤ B2R x' - B2R d := by linarith
    have h_round_xmd_lt : |round radix2 (FLT_exp (3 - emax - prec) prec)
        (round_mode mode.mode_NE) (B2R x' - B2R d)| < bpow radix2 emax := by
      rw [abs_of_nonneg]
      · -- round(B2R x' - B2R d) ≤ B2R x' < bpow emax.
        calc round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode mode.mode_NE)
                  (B2R x' - B2R d)
            ≤ B2R x' := round_le_generic radix2 _
                (FLT_exp_valid (3 - emax - prec) prec hp) _ h_x'_fmt (by linarith)
          _ ≤ |B2R x'| := le_abs_self _
          _ < bpow radix2 emax := abs_B2R_lt_emax hp hmax x'
      · -- 0 ≤ round (B2R x' - B2R d).
        rw [show (0 : ℝ) = round radix2 (FLT_exp (3 - emax - prec) prec)
            (round_mode mode.mode_NE) 0 from
          (round_0 radix2 _ _).symm]
        exact round_le radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp) _
          h_x_minus_d_nonneg
    -- Apply Bminus_correct.
    have h_bminus := Bminus_correct hp hmax (fun a _ => pred_pos_nan a)
      mode.mode_NE x' d h_x'_fin h_d_fin
    rw [if_pos h_round_xmd_lt] at h_bminus
    obtain ⟨h_bminus_b2r, h_bminus_fin, h_bminus_sign⟩ := h_bminus
    -- Now unfold Bpred_pos to expose the Bminus call.
    show B2R (Bminus hp hmax (fun a _ => pred_pos_nan a) mode.mode_NE x' d) =
        pred_pos radix2 (FLT_exp (3 - emax - prec) prec) (B2R x') ∧
        is_finite (Bminus hp hmax (fun a _ => pred_pos_nan a) mode.mode_NE x' d)
          = true ∧
        Bsign (Bminus hp hmax (fun a _ => pred_pos_nan a) mode.mode_NE x' d)
          = false
    refine ⟨?_, h_bminus_fin, ?_⟩
    · -- B2R = pred_pos. Use the four-case dispatch.
      rw [h_bminus_b2r]
      -- round(B2R x' - B2R d) = B2R x' - B2R d since B2R x' - B2R d ∈ format.
      -- We'll show this by establishing that B2R x' - B2R d = pred_pos x'
      -- (which is in format by generic_format_pred_pos).
      have h_diff_eq_pred_pos : B2R x' - B2R d
          = pred_pos radix2 (FLT_exp (3 - emax - prec) prec) (B2R x') := by
        rw [hd_def]
        unfold pred_pos
        split_ifs with h_d h_pred h_pred
        · -- Hd=true, Hpred=true: d = Bldexp ⟹ B2R d = bpow(fexp_em1); pred_pos uses bpow(fexp(mag-1)).
          rw [h_bldexp_b2r', hfexp_em1_def, h_e_mag]
        · -- Hd=true, Hpred=false: contradiction.
          exfalso; apply h_pred
          -- mx = 2^(prec-1) from Hd, so B2R x' = bpow(prec - 1 + ex), mag = prec + ex.
          have h_prec_toNat : 1 ≤ prec.toNat := by omega
          have h_prec_nn : 0 ≤ prec - 1 := by linarith
          have h_2_pm1 : (2 : ℤ) * 2 ^ (prec - 1).toNat = 2 ^ prec.toNat := by
            have h_pn : prec.toNat = (prec - 1).toNat + 1 := by omega
            rw [h_pn, pow_succ]; ring
          have h_mx_eq : mx = (2 : ℤ) ^ (prec - 1).toNat := by linarith
          have h_pow_cast : (((2 : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) = bpow radix2 (prec - 1) := by
            show ((radix2.val ^ (prec - 1).toNat : ℤ) : ℝ) = _
            exact IZR_Zpower radix2 h_prec_nn
          have h_B2R_eq : B2R x' = bpow radix2 (prec - 1 + ex) := by
            show ((cond_Zopp false mx : ℤ) : ℝ) * bpow radix2 ex = _
            rw [cond_Zopp_false, h_mx_eq, h_pow_cast, ← bpow_plus]
          have h_mag_x : mag radix2 (B2R x') = prec + ex := by
            rw [h_B2R_eq, mag_bpow]; ring
          calc B2R x' = bpow radix2 (prec - 1 + ex) := h_B2R_eq
            _ = bpow radix2 (mag radix2 (B2R x') - 1) := by
                rw [h_mag_x]; congr 1; ring
        · -- Hd=false, Hpred=true: d = Bulp ⟹ B2R d = ulp(x'); pred_pos uses bpow(fexp(mag-1)).
          -- Need: x' - ulp(x') = x' - bpow(fexp(mag-1)), i.e., ulp(x') = bpow(fexp(mag-1)).
          -- Key fact: in this subcase, mag(x') ≤ emin + prec.
          rw [h_bulp_b2r]
          -- ulp(x') = bpow(cexp x') = bpow(fexp(mag x')) since x' ≠ 0.
          rw [ulp_neq_0 radix2 _ h_B2R_ne]
          -- Need: bpow(fexp(mag x')) = bpow(fexp(mag x' - 1)).
          -- This holds when both arguments saturate to emin.
          -- Claim: mag(x') ≤ emin + prec (proof by contradiction from h_d, h_pred).
          have h_mag_le : mag radix2 (B2R x') ≤ (3 - emax - prec) + prec := by
            by_contra h_not_le
            push_neg at h_not_le
            -- Derive 2*mx = 2^prec, contradicting h_d.
            have h_canon : canonical_mantissa prec emax mx ex := hb.2.1
            have h_fexp_mag : FLT_exp (3 - emax - prec) prec (mag radix2 (B2R x'))
                = mag radix2 (B2R x') - prec := by
              unfold FLT_exp; apply max_eq_left; linarith
            have h_mx_ne : (mx : ℤ) ≠ 0 := by linarith [hb.1]
            have h_mag_eq_2 : mag radix2 (B2R x') = Zdigits radix2 mx + ex := by
              show mag radix2 (F2R (beta := radix2) ⟨cond_Zopp false mx, ex⟩) = _
              rw [mag_F2R_Zdigits (cond_Zopp false mx) ex
                (by show cond_Zopp false mx ≠ 0; exact h_mx_ne)]
              rfl
            have h_ex_eq : ex = mag radix2 (B2R x') - prec := by
              have h1 : FLT_exp (3 - emax - prec) prec (Zdigits radix2 mx + ex) = ex :=
                h_canon
              rw [← h_mag_eq_2] at h1
              linarith [h1.symm, h_fexp_mag]
            -- B2R x' = bpow(mag - 1) (from h_pred) and B2R x' = mx · bpow(ex).
            -- So mx · bpow(ex) = bpow(mag - 1), i.e., mx = bpow(mag - 1 - ex) = bpow(prec - 1).
            have h_B2R_pow : B2R x' = bpow radix2 (mag radix2 (B2R x') - 1) := h_pred
            have h_step : (mx : ℝ) * bpow radix2 ex
                = bpow radix2 (mag radix2 (B2R x') - 1) := by
              have h_b2r_eq : B2R x' = (mx : ℝ) * bpow radix2 ex := by
                show ((cond_Zopp false mx : ℤ) : ℝ) * bpow radix2 ex = _
                rw [cond_Zopp_false]
              rw [← h_b2r_eq]; exact h_B2R_pow
            -- Substitute ex = mag - prec: mx · bpow(mag - prec) = bpow(mag - 1).
            -- Multiply both sides by bpow(-(mag - prec)) = bpow(prec - mag):
            -- mx = bpow(mag - 1 - (mag - prec)) = bpow(prec - 1).
            have h_prec_nn : 0 ≤ prec - 1 := by linarith
            have h_mx_real : (mx : ℝ) = bpow radix2 (prec - 1) := by
              have h_step' : (mx : ℝ) * bpow radix2 (mag radix2 (B2R x') - prec)
                  = bpow radix2 (mag radix2 (B2R x') - 1) := by
                rw [← h_ex_eq]; exact h_step
              have h_bp_ne : bpow radix2 (mag radix2 (B2R x') - prec) ≠ 0 :=
                (bpow_gt_0 _ _).ne'
              have h_div_eq : (mx : ℝ) = bpow radix2 (mag radix2 (B2R x') - 1)
                  / bpow radix2 (mag radix2 (B2R x') - prec) := by
                rw [eq_div_iff h_bp_ne]; exact h_step'
              rw [h_div_eq,
                show mag radix2 (B2R x') - 1
                  = (prec - 1) + (mag radix2 (B2R x') - prec) from by ring,
                bpow_plus]
              field_simp
            have h_pow_cast : (((2 : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ)
                = bpow radix2 (prec - 1) := by
              show ((radix2.val ^ (prec - 1).toNat : ℤ) : ℝ) = _
              exact IZR_Zpower radix2 h_prec_nn
            have h_mx_int : mx = (2 : ℤ) ^ (prec - 1).toNat := by
              have h_cast : ((mx : ℤ) : ℝ) = (((2 : ℤ) ^ (prec - 1).toNat : ℤ) : ℝ) := by
                rw [h_mx_real, ← h_pow_cast]
              exact_mod_cast h_cast
            have h_2mx : 2 * mx = 2 ^ prec.toNat := by
              rw [h_mx_int]
              have h_pn : prec.toNat = (prec - 1).toNat + 1 := by omega
              rw [h_pn, pow_succ]; ring
            exact h_d h_2mx
          -- Now use h_mag_le to conclude fexp(mag) = fexp(mag-1) = emin.
          have h_fexp_mag : FLT_exp (3 - emax - prec) prec (mag radix2 (B2R x'))
              = 3 - emax - prec := by
            unfold FLT_exp; apply max_eq_right; linarith
          have h_fexp_mag1 : FLT_exp (3 - emax - prec) prec (mag radix2 (B2R x') - 1)
              = 3 - emax - prec := by
            unfold FLT_exp; apply max_eq_right; linarith
          show B2R x' - bpow radix2 (cexp radix2 (FLT_exp (3 - emax - prec) prec) (B2R x'))
            = B2R x' - bpow radix2 (FLT_exp (3 - emax - prec) prec
                (mag radix2 (B2R x') - 1))
          congr 1
          congr 1
          show FLT_exp (3 - emax - prec) prec (mag radix2 (B2R x'))
            = FLT_exp (3 - emax - prec) prec (mag radix2 (B2R x') - 1)
          rw [h_fexp_mag, h_fexp_mag1]
        · -- Hd=false, Hpred=false: d = Bulp ⟹ B2R d = ulp(x'); pred_pos = x' - ulp(x').
          rw [h_bulp_b2r]
      -- The pred_pos result is in format, so rounding is identity.
      have h_pred_pos_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (pred_pos radix2 (FLT_exp (3 - emax - prec) prec) (B2R x')) :=
        generic_format_pred_pos radix2 _ (FLT_exp_valid _ _ hp) h_x'_fmt hpos_x'
      rw [h_diff_eq_pred_pos]
      exact round_generic _ _ _ h_pred_pos_fmt
    · -- Bsign = false.
      rw [h_bminus_sign]
      have h_sign_eq : Bsign x' = false := rfl
      rcases lt_trichotomy (B2R x' - B2R d) 0 with h_lt | h_eq | h_gt
      · linarith
      · have h_cmp : compare (B2R x' - B2R d) (0 : ℝ) = Ordering.eq :=
          compare_eq_iff_eq.mpr h_eq
        rw [h_cmp]; simp [h_sign_eq]
      · have h_cmp : compare (B2R x' - B2R d) (0 : ℝ) = Ordering.gt :=
          compare_gt_iff_gt.mpr h_gt
        rw [h_cmp]

/-! ## Bmax_float: the largest representable finite -/

/-- **`Bmax_float_valid`** (Coq `Bmax_float_proof`, line 2209): the float
`+(2^prec - 1) · 2^(emax - prec)` is a valid binary float. The three
conjuncts of `bounded`: mantissa ≥ 1 (needs `prec ≥ 1`); canonical mantissa
(reduces to `Zdigits(2^prec - 1) = prec` and `FLT_exp(emax) = emax - prec`);
exponent at the cap `emax - prec`. -/
private theorem Bmax_float_valid (hp : 0 < prec) (hmax : prec < emax) :
    valid_binary prec emax
      (full_float.F754_finite false (2 ^ prec.toNat - 1) (emax - prec)) := by
  show bounded prec emax (2 ^ prec.toNat - 1) (emax - prec)
  have h_prec_toNat : 1 ≤ prec.toNat := by omega
  have h_pow_ge_2 : (2 : ℤ) ≤ 2 ^ prec.toNat := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ prec.toNat :=
        pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_prec_toNat
  have h_mant_ge_1 : 1 ≤ (2 : ℤ) ^ prec.toNat - 1 := by linarith
  have h_zd : Zdigits radix2 (2 ^ prec.toNat - 1) = prec := by
    apply Zdigits_unique radix2
    · have h_abs : |((2 ^ prec.toNat - 1 : ℤ) : ℝ)|
                = ((2 ^ prec.toNat - 1 : ℤ) : ℝ) := by
        apply abs_of_pos
        exact_mod_cast (by linarith : (0 : ℤ) < 2 ^ prec.toNat - 1)
      rw [h_abs]
      have h_prec_sub_nn : 0 ≤ prec - 1 := by linarith
      rw [show bpow radix2 (prec - 1)
          = ((2 ^ (prec - 1).toNat : ℤ) : ℝ) from
            (IZR_Zpower radix2 h_prec_sub_nn).symm]
      have h_tn_sub : (prec - 1).toNat = prec.toNat - 1 := by omega
      rw [h_tn_sub]
      have h_nat : ((2 : ℤ) ^ (prec.toNat - 1) : ℤ) ≤ 2 ^ prec.toNat - 1 := by
        set n := prec.toNat - 1 with hn_def
        have hN : prec.toNat = n + 1 := by omega
        rw [hN, pow_succ]
        have h_pos : (1 : ℤ) ≤ 2 ^ n :=
          calc (1 : ℤ) = 2 ^ 0 := by norm_num
            _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
        linarith
      exact_mod_cast h_nat
    · have h_abs : |((2 ^ prec.toNat - 1 : ℤ) : ℝ)|
                = ((2 ^ prec.toNat - 1 : ℤ) : ℝ) := by
        apply abs_of_pos
        exact_mod_cast (by linarith : (0 : ℤ) < 2 ^ prec.toNat - 1)
      rw [h_abs]
      have h_prec_nn : 0 ≤ prec := le_of_lt hp
      rw [show bpow radix2 prec = ((2 ^ prec.toNat : ℤ) : ℝ) from
            (IZR_Zpower radix2 h_prec_nn).symm]
      exact_mod_cast (by linarith : (2 ^ prec.toNat - 1 : ℤ) < 2 ^ prec.toNat)
  refine ⟨h_mant_ge_1, ?_, le_refl _⟩
  show FLT_exp (3 - emax - prec) prec
      (Zdigits radix2 (2 ^ prec.toNat - 1) + (emax - prec)) = emax - prec
  rw [h_zd]
  show FLT_exp (3 - emax - prec) prec (prec + (emax - prec)) = emax - prec
  have h_simp : prec + (emax - prec) = emax := by ring
  rw [h_simp]
  unfold FLT_exp
  exact max_eq_left (by linarith)

/-- **`Bmax_float`** (Coq line 2245): the largest representable finite float,
`+(2^prec - 1) · 2^(emax - prec)`. Used by `Bsucc` to compute the successor
of `-∞`. -/
noncomputable def Bmax_float (hp : 0 < prec) (hmax : prec < emax) :
    binary_float prec emax :=
  FF2B (full_float.F754_finite false (2 ^ prec.toNat - 1) (emax - prec))
    (Bmax_float_valid hp hmax)

/-! ## Bsucc: successor in the IEEE format -/

/-- **`Bsucc`** (Coq line 2681): the successor of a binary float.

- `B754_zero _` → `Bldexp Bone emin = bpow(emin)`, the smallest positive subnormal.
- `B754_infinity false` (+∞) → +∞ itself.
- `B754_infinity true` (-∞) → `-Bmax_float`, the largest negative finite.
- `B754_nan` → propagated NaN via `succ_nan`.
- Positive finite → `Bplus x (Bulp x)`.
- Negative finite → `-(Bpred_pos(-x))`. -/
noncomputable def Bsucc (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (succ_nan : binary_float prec emax →
                  {z : binary_float prec emax // is_nan z = true})
    (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | B754_zero _ => Bldexp hp hmax mode.mode_NE (Bone hp hmax) (3 - emax - prec)
  | B754_infinity false => B754_infinity false
  | B754_infinity true => Bopp succ_nan (Bmax_float hp hmax)
  | B754_nan _ _ _ => build_nan (succ_nan x)
  | B754_finite false mx ex hb =>
    Bplus hp hmax (fun a _ => succ_nan a) mode.mode_NE (B754_finite false mx ex hb)
      (Bulp hp hmax hemax (B754_finite false mx ex hb))
  | B754_finite true mx ex hb =>
    Bopp succ_nan (Bpred_pos hp hmax hemax succ_nan
      (Bopp succ_nan (B754_finite true mx ex hb)))

/-- **`Bsucc_correct`** (Coq line 2693): correctness of `Bsucc`.

If `succ(B2R x) < bpow emax` (no overflow), then `B2R (Bsucc x) = succ(B2R x)`,
`is_finite (Bsucc x) = true`, and `Bsign (Bsucc x) = Bsign x ∧ is_finite_strict x`.
Otherwise, `Bsucc x` encodes `+∞`.

The four input cases (after ruling out non-finite by `hf`):
- **Zero**: `succ 0 = bpow(emin)` (via `negligible_exp_FLT`); `Bsucc` returns `Bldexp Bone emin`.
- **Positive finite**: `succ x = x + ulp(x)`; `Bsucc` is `Bplus x (Bulp x)`, and the
  sum is in format (via `generic_format_succ`), so `round = identity`.
- **Negative finite**: `succ x = -(pred_pos(-x))`; `Bsucc` is `-(Bpred_pos(-x))`,
  reducing to `Bpred_pos_correct`. No overflow (succ of negative is ≤ 0). -/
theorem Bsucc_correct (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (succ_nan : binary_float prec emax →
                  {z : binary_float prec emax // is_nan z = true})
    (x : binary_float prec emax) (hf : is_finite x = true) :
    if succ radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) < bpow radix2 emax then
      B2R (Bsucc hp hmax hemax succ_nan x)
        = succ radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
      is_finite (Bsucc hp hmax hemax succ_nan x) = true ∧
      Bsign (Bsucc hp hmax hemax succ_nan x) = (Bsign x && is_finite_strict x)
    else
      B2FF (Bsucc hp hmax hemax succ_nan x) = full_float.F754_infinity false := by
  -- Establish succ 0 = bpow(emin) once for the zero case.
  have h_succ_0 : succ radix2 (FLT_exp (3 - emax - prec) prec) 0
      = bpow radix2 (3 - emax - prec) := by
    unfold succ
    rw [if_pos (le_refl 0), zero_add]
    unfold ulp
    rw [if_pos rfl]
    obtain ⟨n, h_neg, h_n_le⟩ := negligible_exp_FLT radix2 (3 - emax - prec) prec hp
    rw [h_neg]
    show bpow radix2 (FLT_exp (3 - emax - prec) prec n) = bpow radix2 (3 - emax - prec)
    have h_fexp_n : FLT_exp (3 - emax - prec) prec n = 3 - emax - prec := by
      unfold FLT_exp; apply max_eq_right; linarith
    rw [h_fexp_n]
  -- bpow(emin) in format and < bpow emax.
  have h_emin_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
      (bpow radix2 (3 - emax - prec)) := by
    apply generic_format_bpow' radix2 _ (FLT_exp_valid (3 - emax - prec) prec hp)
    unfold FLT_exp; apply max_le _ (le_refl _); omega
  have h_emin_bnd : bpow radix2 (3 - emax - prec) < bpow radix2 emax :=
    bpow_lt radix2 (by omega)
  cases x with
  | B754_infinity _ => simp [is_finite] at hf
  | B754_nan _ _ _ => simp [is_finite] at hf
  | B754_zero s =>
    -- B2R x = 0, succ 0 = bpow(emin) < bpow(emax) (always no overflow).
    have h_B2R_zero : B2R (B754_zero s : binary_float prec emax) = 0 := rfl
    rw [h_B2R_zero, h_succ_0, if_pos h_emin_bnd]
    have h_is_fin_strict : is_finite_strict (B754_zero s : binary_float prec emax) = false := rfl
    show B2R (Bldexp hp hmax mode.mode_NE (Bone hp hmax) (3 - emax - prec)
            : binary_float prec emax) = bpow radix2 (3 - emax - prec) ∧
        is_finite (Bldexp hp hmax mode.mode_NE (Bone hp hmax) (3 - emax - prec)
            : binary_float prec emax) = true ∧
        Bsign (Bldexp hp hmax mode.mode_NE (Bone hp hmax) (3 - emax - prec)
            : binary_float prec emax)
          = (Bsign (B754_zero s : binary_float prec emax)
              && is_finite_strict (B754_zero s : binary_float prec emax))
    rw [h_is_fin_strict, Bool.and_false]
    obtain ⟨h_b2r, h_fin, h_sign⟩ :=
      Bldexp_Bone_eq hp hmax (3 - emax - prec) h_emin_fmt h_emin_bnd
    exact ⟨h_b2r, h_fin, h_sign⟩
  | B754_finite sx mx ex hb =>
    -- Common: mx > 0, B2R = (cond_Zopp sx mx : ℝ) * bpow ex.
    have h_mx_pos : 0 < mx := by linarith [hb.1]
    cases sx with
    | false =>
      -- Positive finite: Bsucc reduces to Bplus x (Bulp x). succ x = x + ulp x.
      have h_B2R_pos : 0 < B2R (B754_finite false mx ex hb : binary_float prec emax) := by
        show 0 < F2R (beta := radix2) ⟨mx, ex⟩
        exact F2R_gt_0 _ h_mx_pos
      have h_B2R_nn : 0 ≤ B2R (B754_finite false mx ex hb : binary_float prec emax) :=
        le_of_lt h_B2R_pos
      have h_xf_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite false mx ex hb : binary_float prec emax)) :=
        generic_format_B2R _
      have h_ulp_nn : 0 ≤ ulp radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite false mx ex hb : binary_float prec emax)) := ulp_ge_0 _ _ _
      have h_succ_eq : succ radix2 (FLT_exp (3 - emax - prec) prec)
            (B2R (B754_finite false mx ex hb : binary_float prec emax))
          = B2R (B754_finite false mx ex hb : binary_float prec emax)
            + ulp radix2 (FLT_exp (3 - emax - prec) prec)
                (B2R (B754_finite false mx ex hb : binary_float prec emax)) := by
        unfold succ; rw [if_pos h_B2R_nn]
      have h_succ_nn : 0 ≤ succ radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite false mx ex hb : binary_float prec emax)) := by
        rw [h_succ_eq]; linarith
      have h_succ_fmt : generic_format radix2 (FLT_exp (3 - emax - prec) prec)
          (succ radix2 (FLT_exp (3 - emax - prec) prec)
            (B2R (B754_finite false mx ex hb : binary_float prec emax))) :=
        generic_format_succ radix2 _ (FLT_exp_valid _ _ hp) h_xf_fmt
      obtain ⟨h_bulp_b2r, h_bulp_fin, _⟩ :=
        Bulp_correct hp hmax hemax (B754_finite false mx ex hb) rfl
      have h_bplus := Bplus_correct hp hmax (fun a _ => succ_nan a) mode.mode_NE
        (B754_finite false mx ex hb)
        (Bulp hp hmax hemax (B754_finite false mx ex hb)) rfl h_bulp_fin
      rw [h_bulp_b2r] at h_bplus
      have h_round_eq : round radix2 (FLT_exp (3 - emax - prec) prec)
          (round_mode mode.mode_NE)
          (B2R (B754_finite false mx ex hb : binary_float prec emax)
            + ulp radix2 (FLT_exp (3 - emax - prec) prec)
                (B2R (B754_finite false mx ex hb : binary_float prec emax)))
          = succ radix2 (FLT_exp (3 - emax - prec) prec)
              (B2R (B754_finite false mx ex hb : binary_float prec emax)) := by
        rw [← h_succ_eq]; exact round_generic _ _ _ h_succ_fmt
      rw [h_round_eq, abs_of_nonneg h_succ_nn] at h_bplus
      -- Bsucc reduces to Bplus x (Bulp x).
      have h_bsucc : Bsucc hp hmax hemax succ_nan (B754_finite false mx ex hb)
          = Bplus hp hmax (fun a _ => succ_nan a) mode.mode_NE
              (B754_finite false mx ex hb)
              (Bulp hp hmax hemax (B754_finite false mx ex hb)) := rfl
      rw [h_bsucc]
      by_cases h_no_ovf : succ radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite false mx ex hb : binary_float prec emax)) < bpow radix2 emax
      · rw [if_pos h_no_ovf]
        rw [if_pos h_no_ovf] at h_bplus
        obtain ⟨h_b2r, h_fin, h_sign⟩ := h_bplus
        refine ⟨h_b2r, h_fin, ?_⟩
        have h_sum_pos : 0 < B2R (B754_finite false mx ex hb : binary_float prec emax)
            + ulp radix2 (FLT_exp (3 - emax - prec) prec)
                (B2R (B754_finite false mx ex hb : binary_float prec emax)) := by linarith
        have h_cmp : compare (B2R (B754_finite false mx ex hb : binary_float prec emax)
              + ulp radix2 (FLT_exp (3 - emax - prec) prec)
                (B2R (B754_finite false mx ex hb : binary_float prec emax))) (0 : ℝ)
            = Ordering.gt := compare_gt_iff_gt.mpr h_sum_pos
        rw [h_sign, h_cmp]
        rfl
      · rw [if_neg h_no_ovf]
        rw [if_neg h_no_ovf] at h_bplus
        obtain ⟨h_b2ff, _⟩ := h_bplus
        rw [h_b2ff]
        show binary_overflow prec emax mode.mode_NE
            (Bsign (B754_finite false mx ex hb : binary_float prec emax))
          = full_float.F754_infinity false
        rfl
    | true =>
      -- Negative finite: Bsucc reduces to Bopp(Bpred_pos(Bopp x)). succ x = -pred_pos(-x).
      have h_B2R_neg : B2R (B754_finite true mx ex hb : binary_float prec emax) < 0 := by
        show F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩ < 0
        show ((cond_Zopp true mx : ℤ) : ℝ) * bpow radix2 ex < 0
        rw [show (cond_Zopp true mx : ℤ) = -mx from rfl]
        have h_neg : ((-mx : ℤ) : ℝ) < 0 := by
          push_cast
          have h_mx_r : (1 : ℝ) ≤ (mx : ℝ) := by exact_mod_cast hb.1
          linarith
        exact mul_neg_of_neg_of_pos h_neg (bpow_gt_0 _ _)
      have h_succ_eq : succ radix2 (FLT_exp (3 - emax - prec) prec)
            (B2R (B754_finite true mx ex hb : binary_float prec emax))
          = -(pred_pos radix2 (FLT_exp (3 - emax - prec) prec)
              (-(B2R (B754_finite true mx ex hb : binary_float prec emax)))) := by
        unfold succ; rw [if_neg (by linarith)]
      have h_neg_x_pos : 0 < B2R (Bopp succ_nan (B754_finite true mx ex hb)) := by
        rw [B2R_Bopp]; linarith
      obtain ⟨h_bpp_b2r, h_bpp_fin, h_bpp_sign⟩ := Bpred_pos_correct hp hmax hemax succ_nan
        (Bopp succ_nan (B754_finite true mx ex hb)) h_neg_x_pos
      have h_succ_lt : succ radix2 (FLT_exp (3 - emax - prec) prec)
          (B2R (B754_finite true mx ex hb : binary_float prec emax)) < bpow radix2 emax := by
        rw [h_succ_eq]
        have h_pred_pos_nn :
            0 ≤ pred_pos radix2 (FLT_exp (3 - emax - prec) prec)
              (B2R (Bopp succ_nan (B754_finite true mx ex hb))) :=
          pred_pos_ge_0 radix2 _ (FLT_exp_valid _ _ hp) h_neg_x_pos (generic_format_B2R _)
        have h_eq : B2R (Bopp succ_nan (B754_finite true mx ex hb))
            = -(B2R (B754_finite true mx ex hb : binary_float prec emax)) := B2R_Bopp _ _
        rw [h_eq] at h_pred_pos_nn
        have : (0 : ℝ) < bpow radix2 emax := bpow_gt_0 _ _
        linarith
      rw [if_pos h_succ_lt]
      -- Bsucc reduces to Bopp(Bpred_pos(Bopp x)).
      have h_bsucc : Bsucc hp hmax hemax succ_nan (B754_finite true mx ex hb)
          = Bopp succ_nan
              (Bpred_pos hp hmax hemax succ_nan
                (Bopp succ_nan (B754_finite true mx ex hb))) := rfl
      rw [h_bsucc]
      have h_bpp_not_nan : is_nan
          (Bpred_pos hp hmax hemax succ_nan
            (Bopp succ_nan (B754_finite true mx ex hb))) = false := by
        cases hres : Bpred_pos hp hmax hemax succ_nan
            (Bopp succ_nan (B754_finite true mx ex hb)) with
        | B754_zero _ => rfl
        | B754_infinity _ => rw [hres] at h_bpp_fin; simp [is_finite] at h_bpp_fin
        | B754_nan _ _ _ => rw [hres] at h_bpp_fin; simp [is_finite] at h_bpp_fin
        | B754_finite _ _ _ _ => rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [B2R_Bopp, h_bpp_b2r, B2R_Bopp, ← h_succ_eq]
      · rw [is_finite_Bopp]; exact h_bpp_fin
      · rw [Bsign_Bopp _ _ h_bpp_not_nan, h_bpp_sign]
        rfl

/-! ## Bpred: predecessor in the IEEE format -/

/-- **`Bpred`** (Coq line 2780): the predecessor of a binary float,
defined as `-(Bsucc(-x))`. -/
noncomputable def Bpred (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (pred_nan : binary_float prec emax →
                  {z : binary_float prec emax // is_nan z = true})
    (x : binary_float prec emax) : binary_float prec emax :=
  Bopp pred_nan (Bsucc hp hmax hemax pred_nan (Bopp pred_nan x))

/-- **`Bpred_correct`** (Coq line 2783): correctness of `Bpred`. Dual of
`Bsucc_correct` via `Bopp` (using `pred = -succ(-·)`). -/
theorem Bpred_correct (hp : 0 < prec) (hmax : prec < emax) (hemax : 3 ≤ emax)
    (pred_nan : binary_float prec emax →
                  {z : binary_float prec emax // is_nan z = true})
    (x : binary_float prec emax) (hf : is_finite x = true) :
    if -(bpow radix2 emax) < pred radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) then
      B2R (Bpred hp hmax hemax pred_nan x)
        = pred radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) ∧
      is_finite (Bpred hp hmax hemax pred_nan x) = true ∧
      Bsign (Bpred hp hmax hemax pred_nan x) = (Bsign x || !(is_finite_strict x))
    else
      B2FF (Bpred hp hmax hemax pred_nan x) = full_float.F754_infinity true := by
  have h_neg_xf_fin : is_finite (Bopp pred_nan x) = true := by
    rw [is_finite_Bopp]; exact hf
  have h_succ := Bsucc_correct hp hmax hemax pred_nan (Bopp pred_nan x) h_neg_xf_fin
  -- pred x = -(succ(-x)). The if-condition `-bpow emax < pred x` matches
  -- Bsucc_correct's `succ(-x) < bpow emax` via negation.
  have h_pred_eq : pred radix2 (FLT_exp (3 - emax - prec) prec) (B2R x)
      = -(succ radix2 (FLT_exp (3 - emax - prec) prec) (-(B2R x))) := rfl
  rw [B2R_Bopp] at h_succ
  -- The condition: -bpow emax < pred x ↔ -bpow emax < -succ(-x) ↔ succ(-x) < bpow emax.
  have h_cond_iff : (-(bpow radix2 emax)
        < pred radix2 (FLT_exp (3 - emax - prec) prec) (B2R x))
      ↔ (succ radix2 (FLT_exp (3 - emax - prec) prec) (-(B2R x))
        < bpow radix2 emax) := by
    rw [h_pred_eq]; constructor <;> intro h <;> linarith
  by_cases h_no_ovf : succ radix2 (FLT_exp (3 - emax - prec) prec) (-(B2R x))
      < bpow radix2 emax
  · have h_no_ovf' : -(bpow radix2 emax)
        < pred radix2 (FLT_exp (3 - emax - prec) prec) (B2R x) :=
      h_cond_iff.mpr h_no_ovf
    rw [if_pos h_no_ovf']
    rw [if_pos h_no_ovf] at h_succ
    obtain ⟨h_b2r, h_fin, h_sign⟩ := h_succ
    have h_succ_not_nan : is_nan
        (Bsucc hp hmax hemax pred_nan (Bopp pred_nan x)) = false := by
      cases hres : Bsucc hp hmax hemax pred_nan (Bopp pred_nan x) with
      | B754_zero _ => rfl
      | B754_infinity _ => rw [hres] at h_fin; simp [is_finite] at h_fin
      | B754_nan _ _ _ => rw [hres] at h_fin; simp [is_finite] at h_fin
      | B754_finite _ _ _ _ => rfl
    have hx_not_nan : is_nan x = false := by
      cases x with
      | B754_zero _ => rfl
      | B754_infinity _ => simp [is_finite] at hf
      | B754_nan _ _ _ => simp [is_finite] at hf
      | B754_finite _ _ _ _ => rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [show Bpred hp hmax hemax pred_nan x
          = Bopp pred_nan (Bsucc hp hmax hemax pred_nan (Bopp pred_nan x)) from rfl,
        B2R_Bopp, h_b2r, h_pred_eq]
    · rw [show Bpred hp hmax hemax pred_nan x
          = Bopp pred_nan (Bsucc hp hmax hemax pred_nan (Bopp pred_nan x)) from rfl,
        is_finite_Bopp]; exact h_fin
    · rw [show Bpred hp hmax hemax pred_nan x
          = Bopp pred_nan (Bsucc hp hmax hemax pred_nan (Bopp pred_nan x)) from rfl,
        Bsign_Bopp _ _ h_succ_not_nan, h_sign, Bsign_Bopp _ _ hx_not_nan]
      -- !(Bsign(Bopp x) && is_finite_strict(Bopp x)) = Bsign x || !(is_finite_strict x).
      -- is_finite_strict is preserved by Bopp (when not nan).
      have h_fs_eq : is_finite_strict (Bopp pred_nan x) = is_finite_strict x := by
        cases x with
        | B754_zero _ => rfl
        | B754_infinity _ => simp [is_finite] at hf
        | B754_nan _ _ _ => simp [is_finite] at hf
        | B754_finite _ _ _ _ => rfl
      rw [h_fs_eq]
      cases hbs : Bsign x <;> cases hfs : is_finite_strict x <;> simp
  · have h_no_ovf' : ¬ (-(bpow radix2 emax)
        < pred radix2 (FLT_exp (3 - emax - prec) prec) (B2R x)) := by
      intro h; exact h_no_ovf (h_cond_iff.mp h)
    rw [if_neg h_no_ovf']
    rw [if_neg h_no_ovf] at h_succ
    show B2FF (Bopp pred_nan (Bsucc hp hmax hemax pred_nan (Bopp pred_nan x)))
        = full_float.F754_infinity true
    cases hres : Bsucc hp hmax hemax pred_nan (Bopp pred_nan x) with
    | B754_zero _ => rw [hres] at h_succ; simp [B2FF] at h_succ
    | B754_infinity s =>
      rw [hres] at h_succ; simp [B2FF] at h_succ
      subst h_succ
      show B2FF (Bopp pred_nan (B754_infinity false : binary_float prec emax))
          = full_float.F754_infinity true
      rfl
    | B754_nan _ _ _ => rw [hres] at h_succ; simp [B2FF] at h_succ
    | B754_finite _ _ _ _ => rw [hres] at h_succ; simp [B2FF] at h_succ

/-! ## Bdiv: IEEE-754 binary division

So far we have the kernel exponent picker `Fdiv_core_binary`. The next
session can pick this up to prove `Bdiv_correct_aux`, then `Bdiv` +
`Bdiv_correct` as small wrappers. The proof structure mirrors
`Bmult_correct_aux` (xor sign, F2R relation, apply
`binary_round_aux_correct'`), with one twist: the `e'` precondition

  `e' ≤ cexp(x/y)`

reduces via `e' = min(FLT_exp(D), ex-ey) ≤ FLT_exp(D)` and
`FLT_exp_monotone` plus `mag_div_F2R`'s lower bound `D ≤ mag(x/y)`
(where `D = Zdigits mx + ex - (Zdigits my + ey)`). The Lean
`mag_div_F2R` returns a sandwich `D ≤ mag(x/y) ≤ D+1`; the lower bound
is what's needed. -/

/-- **`Fdiv_core_binary`** (Coq line 1844): pick the canonical exponent for
the division `(m1·2^e1) / (m2·2^e2)` — the min of `fexp(Zdigits + (e1-e2))`
(the format-suggested exponent) and `e1 - e2` (the natural exponent from
the float arithmetic) — and apply `Fdiv_core` to get the bracketing
mantissa and location. -/
noncomputable def Fdiv_core_binary (prec emax : ℤ) (m1 e1 m2 e2 : ℤ) :
    ℤ × ℤ × location :=
  let d1 := Zdigits radix2 m1
  let d2 := Zdigits radix2 m2
  let e' := min (FLT_exp (3 - emax - prec) prec (d1 + e1 - (d2 + e2))) (e1 - e2)
  let r := Fdiv_core radix2 m1 e1 m2 e2 e'
  (r.1, e', r.2)

/-- **`Bdiv_correct_aux`** (Coq lines 1858–1949): the rounding-kernel
correctness statement for the quotient of two finite bounded floats.
Reduces to `binary_round_aux_correct'` applied to the `Fdiv_core_binary`
output. The key precondition `e' ≤ cexp(x/y)` reduces via `e' ≤ FLT_exp(D)`
(from `min_le_left`) plus `FLT_exp_monotone` plus `mag_div_F2R`'s lower
bound `D ≤ mag(x/y)`. -/
theorem Bdiv_correct_aux (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (sx : Bool) (mx ex : ℤ) (Hx : bounded prec emax mx ex)
    (sy : Bool) (my ey : ℤ) (Hy : bounded prec emax my ey) :
    let x := F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
    let y := F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩
    let mze := Fdiv_core_binary prec emax mx ex my ey
    let z := binary_round_aux prec emax m (xor sx sy) mze.1 mze.2.1 mze.2.2
    valid_binary prec emax z ∧
    (if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (x / y)|
        < bpow radix2 emax then
      FF2R radix2 z =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (x / y) ∧
      is_finite_FF z = true ∧
      sign_FF z = xor sx sy
    else
      z = binary_overflow prec emax m (xor sx sy)) := by
  intro x y mze z
  -- Positivity from bounded.
  have h_mx_pos : 0 < mx := Hx.1
  have h_my_pos : 0 < my := Hy.1
  have h_F2R_mx_pos : 0 < F2R (beta := radix2) ⟨mx, ex⟩ := F2R_gt_0 ⟨mx, ex⟩ h_mx_pos
  have h_F2R_my_pos : 0 < F2R (beta := radix2) ⟨my, ey⟩ := F2R_gt_0 ⟨my, ey⟩ h_my_pos
  -- Sign-stripped equalities.
  have hx_eq : x = cond_Ropp sx (F2R (beta := radix2) ⟨mx, ex⟩) :=
    F2R_cond_Zopp sx mx ex
  have hy_eq : y = cond_Ropp sy (F2R (beta := radix2) ⟨my, ey⟩) :=
    F2R_cond_Zopp sy my ey
  -- x ≠ 0, y ≠ 0, x/y ≠ 0.
  have hx_ne : x ≠ 0 := by
    rw [hx_eq]
    cases sx <;> simp [cond_Ropp, ne_of_gt h_F2R_mx_pos]
  have hy_ne : y ≠ 0 := by
    rw [hy_eq]
    cases sy <;> simp [cond_Ropp, ne_of_gt h_F2R_my_pos]
  have hxy_ne : x / y ≠ 0 := div_ne_zero hx_ne hy_ne
  -- |x| = F2R⟨mx, ex⟩, |y| = F2R⟨my, ey⟩.
  have h_abs_x : |x| = F2R (beta := radix2) ⟨mx, ex⟩ := by
    rw [hx_eq]; cases sx <;> simp [cond_Ropp, abs_of_pos h_F2R_mx_pos]
  have h_abs_y : |y| = F2R (beta := radix2) ⟨my, ey⟩ := by
    rw [hy_eq]; cases sy <;> simp [cond_Ropp, abs_of_pos h_F2R_my_pos]
  -- |x/y| = F2R⟨mx, ex⟩ / F2R⟨my, ey⟩.
  have h_abs_xy : |x / y| =
      F2R (beta := radix2) ⟨mx, ex⟩ / F2R (beta := radix2) ⟨my, ey⟩ := by
    rw [abs_div, h_abs_x, h_abs_y]
  -- Unfold `mze` so we can reason about its components.
  -- `mze.1 = (Fdiv_core radix2 mx ex my ey e').1`
  -- `mze.2.1 = e'`
  -- `mze.2.2 = (Fdiv_core radix2 mx ex my ey e').2`
  -- where `e' = min(FLT_exp(D), ex - ey)` and `D = Zdigits mx + ex - (Zdigits my + ey)`.
  set e' : ℤ := min (FLT_exp (3 - emax - prec) prec
        (Zdigits radix2 mx + ex - (Zdigits radix2 my + ey)))
      (ex - ey) with he'_def
  set r := Fdiv_core radix2 mx ex my ey e' with hr_def
  have h_mze : mze = (r.1, e', r.2) := rfl
  -- Bracket on |x/y| from Fdiv_core_correct.
  have h_bracket :
      inbetween_float radix2 r.1 e' |x / y| r.2 := by
    rw [h_abs_xy]
    exact Fdiv_core_correct radix2 mx ex my ey e' h_mx_pos h_my_pos
  -- e' ≤ cexp(x/y).
  have h_e'_le_cexp : e' ≤
      cexp radix2 (FLT_exp (3 - emax - prec) prec) (x / y) := by
    rw [← cexp_abs, h_abs_xy]
    unfold cexp
    have h_mag := mag_div_F2R radix2 mx ex my ey h_mx_pos h_my_pos
    have h_min_le : e' ≤ FLT_exp (3 - emax - prec) prec
        (Zdigits radix2 mx + ex - (Zdigits radix2 my + ey)) := by
      rw [he'_def]; exact min_le_left _ _
    calc e' ≤ FLT_exp (3 - emax - prec) prec
          (Zdigits radix2 mx + ex - (Zdigits radix2 my + ey)) := h_min_le
      _ ≤ FLT_exp (3 - emax - prec) prec
          (mag radix2 (F2R (beta := radix2) ⟨mx, ex⟩
                        / F2R (beta := radix2) ⟨my, ey⟩)) :=
          FLT_exp_monotone (3 - emax - prec) prec _ _ h_mag.1
  -- Sign: xor sx sy = decide (x/y < 0).
  have h_sign : xor sx sy = decide (x / y < 0) := by
    rw [hx_eq, hy_eq]
    cases sx <;> cases sy <;> simp [cond_Ropp] <;>
      first
        | (apply div_pos h_F2R_mx_pos h_F2R_my_pos)
        | (apply le_of_lt; apply div_pos h_F2R_mx_pos h_F2R_my_pos)
        | (rw [div_neg_iff]; left
           exact ⟨h_F2R_mx_pos, neg_neg_iff_pos.mpr h_F2R_my_pos⟩)
        | (rw [neg_div]
           exact neg_neg_of_pos (div_pos h_F2R_mx_pos h_F2R_my_pos))
  -- Apply binary_round_aux_correct'.
  have h_main := binary_round_aux_correct' hp hmax m (x / y) r.1 e' r.2
                  hxy_ne h_bracket h_e'_le_cexp
  rw [← h_sign] at h_main
  -- Bridge mze to (r.1, e', r.2).
  show valid_binary prec emax
        (binary_round_aux prec emax m (xor sx sy) mze.1 mze.2.1 mze.2.2) ∧ _
  rw [h_mze]
  exact h_main

/-- **`Bdiv`** (Coq line 1951): IEEE-754 division of two binary floats.
NaN propagates; ∞/∞ and 0/0 are NaN. Two finite inputs go through
`Bdiv_correct_aux`. Note that the result type is `binary_float`, so the
"divide by zero" case (finite/0) is encoded as `±∞`. -/
noncomputable def Bdiv (hp : 0 < prec) (hmax : prec < emax)
    (div_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax) : binary_float prec emax :=
  match x, y with
  | B754_nan _ _ _, _ => build_nan (div_nan x y)
  | _, B754_nan _ _ _ => build_nan (div_nan x y)
  | B754_infinity _, B754_infinity _ => build_nan (div_nan x y)
  | B754_infinity sx, B754_finite sy _ _ _ => B754_infinity (xor sx sy)
  | B754_finite sx _ _ _, B754_infinity sy => B754_zero (xor sx sy)
  | B754_infinity sx, B754_zero sy => B754_infinity (xor sx sy)
  | B754_zero sx, B754_infinity sy => B754_zero (xor sx sy)
  | B754_finite sx _ _ _, B754_zero sy => B754_infinity (xor sx sy)
  | B754_zero sx, B754_finite sy _ _ _ => B754_zero (xor sx sy)
  | B754_zero _, B754_zero _ => build_nan (div_nan x y)
  | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
    FF2B _ (Bdiv_correct_aux hp hmax m sx mx ex Hx sy my ey Hy).1

/-! ## Bsqrt: IEEE-754 binary square root

Square root of a non-negative finite float. The exponent picker
`Fsqrt_core_binary` ensures `2·e' ≤ ex` so that `Fsqrt_core` brackets
the real square root at exponent `e'`. The proof of correctness uses
`binary_round_aux_correct'` (primed: location is not Exact), with the
precondition `e' ≤ cexp(√x)` reducing via `e' ≤ FLT_exp((d+e+1)/2)` from
`min_le_left` plus `FLT_exp_monotone` plus `mag_sqrt_F2R`.

Unlike division, sqrt of a bounded float never overflows: `sqrt x ≤
sqrt(bpow emax) < bpow emax` since `emax ≥ 1`, and the rounding error
stays controlled. This means `Bsqrt_correct_aux` strengthens the
`binary_round_aux_correct'` conditional to an unconditional finite-result. -/

/-- **`Fsqrt_core_binary`** (Coq line 1999): pick the canonical exponent
for `sqrt(m · 2^e)` — the min of `fexp((d + e + 1)/2)` (the format-suggested
exponent) and `e/2` (the natural exponent from `sqrt`) — and apply
`Fsqrt_core` to get the bracketing mantissa and location. -/
noncomputable def Fsqrt_core_binary (prec emax : ℤ) (m e : ℤ) :
    ℤ × ℤ × location :=
  let d := Zdigits radix2 m
  let e' := min (FLT_exp (3 - emax - prec) prec ((d + e + 1) / 2)) (e / 2)
  let r := Fsqrt_core radix2 m e e'
  (r.1, e', r.2)

/-- **`Bsqrt_correct_aux`** (Coq lines 2015–2123): the rounding-kernel
correctness for `sqrt` of a bounded float. Strengthens
`binary_round_aux_correct'` to unconditional finite-result by proving
no-overflow: `sqrt x ≤ bpow(emax - 1)` (in FLT format), hence
`|round (sqrt x)| ≤ bpow(emax - 1) < bpow emax`. -/
theorem Bsqrt_correct_aux (hp : 0 < prec) (hmax : prec < emax)
    (m : mode) (mx ex : ℤ) (Hx : bounded prec emax mx ex) :
    let x := F2R (beta := radix2) ⟨mx, ex⟩
    let mze := Fsqrt_core_binary prec emax mx ex
    let z := binary_round_aux prec emax m false mze.1 mze.2.1 mze.2.2
    valid_binary prec emax z ∧
    FF2R radix2 z =
      round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (Real.sqrt x) ∧
    is_finite_FF z = true ∧
    sign_FF z = false := by
  intro x mze z
  -- Setup: x > 0, sqrt x > 0.
  have h_mx_pos : 0 < mx := Hx.1
  have h_x_pos : 0 < x := F2R_gt_0 ⟨mx, ex⟩ h_mx_pos
  have h_x_nonneg : 0 ≤ x := le_of_lt h_x_pos
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr h_x_pos
  have h_sqrt_nonneg : 0 ≤ Real.sqrt x := le_of_lt h_sqrt_pos
  have h_sqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt h_sqrt_pos
  have h_abs_sqrt : |Real.sqrt x| = Real.sqrt x := abs_of_nonneg h_sqrt_nonneg
  -- Unpack mze: mze = (r.1, e', r.2).
  set e' : ℤ := min (FLT_exp (3 - emax - prec) prec
                ((Zdigits radix2 mx + ex + 1) / 2)) (ex / 2) with he'_def
  set r := Fsqrt_core radix2 mx ex e' with hr_def
  have h_mze : mze = (r.1, e', r.2) := rfl
  -- 2 * e' ≤ ex from e' ≤ ex / 2.
  have h_2e'_le_ex : 2 * e' ≤ ex := by
    have h_le_div2 : e' ≤ ex / 2 := by rw [he'_def]; exact min_le_right _ _
    omega
  -- Bracket from Fsqrt_core_correct.
  have h_bracket :
      inbetween_float radix2 r.1 e' (Real.sqrt x) r.2 :=
    Fsqrt_core_correct radix2 mx ex e' h_mx_pos h_2e'_le_ex
  have h_bracket_abs :
      inbetween_float radix2 r.1 e' |Real.sqrt x| r.2 := by
    rw [h_abs_sqrt]; exact h_bracket
  -- e' ≤ cexp(sqrt x).
  have h_e'_le_cexp : e' ≤
      cexp radix2 (FLT_exp (3 - emax - prec) prec) (Real.sqrt x) := by
    unfold cexp
    rw [mag_sqrt_F2R radix2 mx ex h_mx_pos]
    rw [he'_def]; exact min_le_left _ _
  -- decide(sqrt x < 0) = false.
  have h_sign : decide (Real.sqrt x < 0) = false := by
    simp [not_lt.mpr h_sqrt_nonneg]
  -- Apply binary_round_aux_correct'.
  have h_main := binary_round_aux_correct' hp hmax m (Real.sqrt x) r.1 e' r.2
                  h_sqrt_ne h_bracket_abs h_e'_le_cexp
  rw [h_sign] at h_main
  -- No-overflow: |round (sqrt x)| ≤ bpow(emax - 1) < bpow emax.
  have h_emax_ge_2 : 2 ≤ emax := by linarith
  have h_emax_minus_1_ge_emin : 3 - emax - prec ≤ emax - 1 := by linarith
  have h_x_lt : x < bpow radix2 emax := bounded_lt_emax hp hmax mx ex Hx
  have h_K_nonneg : 0 ≤ bpow radix2 (emax - 1) := bpow_ge_0 _ _
  have h_K_sq : (bpow radix2 (emax - 1))^2 = bpow radix2 (2 * emax - 2) := by
    rw [sq, ← bpow_plus]; congr 1; ring
  -- x ≤ bpow(2 * emax - 2).
  have h_x_le_K_sq : x ≤ bpow radix2 (2 * emax - 2) := by
    have h_bound : emax ≤ 2 * emax - 2 := by linarith
    calc x ≤ bpow radix2 emax := le_of_lt h_x_lt
      _ ≤ bpow radix2 (2 * emax - 2) := bpow_le radix2 h_bound
  -- sqrt x ≤ bpow(emax - 1).
  have h_sqrt_le_K : Real.sqrt x ≤ bpow radix2 (emax - 1) := by
    have h_sqrt_le : Real.sqrt x ≤ Real.sqrt ((bpow radix2 (emax - 1))^2) := by
      rw [h_K_sq]; exact Real.sqrt_le_sqrt h_x_le_K_sq
    rw [Real.sqrt_sq h_K_nonneg] at h_sqrt_le
    exact h_sqrt_le
  -- bpow(emax - 1) is in FLT format.
  have h_K_format :
      generic_format radix2 (FLT_exp (3 - emax - prec) prec)
        (bpow radix2 (emax - 1)) := by
    apply generic_format_bpow' radix2 _
      (FLT_exp_valid (3 - emax - prec) prec hp) (emax - 1)
    unfold FLT_exp
    simp only [max_def]; split_ifs <;> linarith
  -- |round (sqrt x)| ≤ bpow(emax - 1).
  have h_round_abs_le :
      |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (Real.sqrt x)|
        ≤ bpow radix2 (emax - 1) := by
    apply abs_round_le_generic radix2 _
      (FLT_exp_valid (3 - emax - prec) prec hp) (round_mode m) h_K_format
    rw [h_abs_sqrt]; exact h_sqrt_le_K
  -- bpow(emax - 1) < bpow emax.
  have h_K_lt_emax : bpow radix2 (emax - 1) < bpow radix2 emax := by
    apply bpow_lt; linarith
  have h_round_lt : |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
                      (Real.sqrt x)| < bpow radix2 emax :=
    lt_of_le_of_lt h_round_abs_le h_K_lt_emax
  -- Extract the if-true branch.
  obtain ⟨h_valid, h_cond⟩ := h_main
  rw [if_pos h_round_lt] at h_cond
  obtain ⟨h_round_eq, h_finite, h_sign_eq⟩ := h_cond
  exact ⟨h_valid, h_round_eq, h_finite, h_sign_eq⟩

/-- **`Bdiv_correct`** (Coq lines 1966–1995): the user-facing correctness
theorem for `Bdiv`. Given a nonzero divisor `y`, the result either:

* equals `round (x / y)` when that fits in `[0, β^emax)`, is finite iff `x`
  is, and has sign `xor (Bsign x) (Bsign y)` (when not NaN);
* otherwise has `B2FF = binary_overflow`.

The hypothesis `B2R y ≠ 0` forces `y` to be `B754_finite`. The non-finite
cases of `x` (`zero`, `infinity`, `nan`) all give `B2R x = 0`, hence
`B2R x / B2R y = 0`, `round 0 = 0`, and the if-true branch trivially holds. -/
theorem Bdiv_correct (hp : 0 < prec) (hmax : prec < emax)
    (div_nan : binary_float prec emax → binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x y : binary_float prec emax)
    (hy : B2R y ≠ 0) :
    if |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
            (B2R x / B2R y)| < bpow radix2 emax then
      B2R (Bdiv hp hmax div_nan m x y) =
        round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
          (B2R x / B2R y) ∧
      is_finite (Bdiv hp hmax div_nan m x y) = is_finite x ∧
      (is_nan (Bdiv hp hmax div_nan m x y) = false →
        Bsign (Bdiv hp hmax div_nan m x y) = xor (Bsign x) (Bsign y))
    else
      B2FF (Bdiv hp hmax div_nan m x y) =
        binary_overflow prec emax m (xor (Bsign x) (Bsign y)) := by
  -- y must be finite (else B2R y = 0, contradicting hy).
  cases y with
  | B754_zero _ => exfalso; exact hy rfl
  | B754_infinity _ => exfalso; exact hy rfl
  | B754_nan _ _ _ => exfalso; exact hy rfl
  | B754_finite sy my ey Hy =>
    -- For x non-finite, B2R x = 0, so the quotient is 0, round 0 = 0,
    -- and the condition holds (|0| < bpow emax).
    cases x with
    | B754_nan sx plx hplx =>
      -- Bdiv reduces to `build_nan (div_nan _ _)`.
      have h_Bdiv_eq : Bdiv hp hmax div_nan m (B754_nan sx plx hplx)
                        (B754_finite sy my ey Hy)
                      = build_nan (div_nan (B754_nan sx plx hplx)
                                           (B754_finite sy my ey Hy)) := rfl
      have h_B2R_x : B2R (B754_nan (prec := prec) (emax := emax) sx plx hplx)
                    = (0 : ℝ) := rfl
      rw [h_B2R_x, zero_div, round_0, abs_zero,
          if_pos (bpow_gt_0 radix2 emax)]
      rw [h_Bdiv_eq]
      refine ⟨B2R_build_nan _, by rw [is_finite_build_nan]; rfl, ?_⟩
      intro hcon
      rw [is_nan_build_nan] at hcon
      exact Bool.noConfusion hcon
    | B754_infinity sx =>
      -- Bdiv reduces to `B754_infinity (xor sx sy)`.
      have h_Bdiv_eq : Bdiv hp hmax div_nan m (B754_infinity sx)
                        (B754_finite sy my ey Hy)
                      = B754_infinity (xor sx sy) := rfl
      have h_B2R_x : B2R (B754_infinity (prec := prec) (emax := emax) sx)
                    = (0 : ℝ) := rfl
      rw [h_B2R_x, zero_div, round_0, abs_zero,
          if_pos (bpow_gt_0 radix2 emax)]
      rw [h_Bdiv_eq]
      refine ⟨rfl, rfl, ?_⟩
      intro _; rfl
    | B754_zero sx =>
      -- Bdiv reduces to `B754_zero (xor sx sy)`.
      have h_Bdiv_eq : Bdiv hp hmax div_nan m (B754_zero sx)
                        (B754_finite sy my ey Hy)
                      = B754_zero (xor sx sy) := rfl
      have h_B2R_x : B2R (B754_zero (prec := prec) (emax := emax) sx)
                    = (0 : ℝ) := rfl
      rw [h_B2R_x, zero_div, round_0, abs_zero,
          if_pos (bpow_gt_0 radix2 emax)]
      rw [h_Bdiv_eq]
      refine ⟨rfl, rfl, ?_⟩
      intro _; rfl
    | B754_finite sx mx ex Hx =>
      -- The main case: apply Bdiv_correct_aux.
      have h_aux := Bdiv_correct_aux hp hmax m sx mx ex Hx sy my ey Hy
      have h_Bdiv_eq : Bdiv hp hmax div_nan m (B754_finite sx mx ex Hx)
                        (B754_finite sy my ey Hy)
                      = FF2B _ h_aux.1 := rfl
      rw [h_Bdiv_eq]
      obtain ⟨h_valid, h_cond⟩ := h_aux
      have h_B2R_x : B2R (B754_finite (prec := prec) (emax := emax) sx mx ex Hx)
                    = F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩ := rfl
      have h_B2R_y : B2R (B754_finite (prec := prec) (emax := emax) sy my ey Hy)
                    = F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩ := rfl
      rw [h_B2R_x, h_B2R_y]
      by_cases h_lt : |round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
              (F2R (beta := radix2) ⟨cond_Zopp sx mx, ex⟩
                / F2R (beta := radix2) ⟨cond_Zopp sy my, ey⟩)|
            < bpow radix2 emax
      · rw [if_pos h_lt] at h_cond ⊢
        obtain ⟨h_round_eq, h_finite, h_sign⟩ := h_cond
        refine ⟨?_, ?_, ?_⟩
        · rw [B2R_FF2B]; exact h_round_eq
        · rw [is_finite_FF2B]; exact h_finite
        · intro _; rw [Bsign_FF2B]; exact h_sign
      · rw [if_neg h_lt] at h_cond ⊢
        rw [B2FF_FF2B]; exact h_cond

/-- **`Bsqrt`** (Coq line 2125): IEEE-754 square root.
NaN propagates; `+∞ → +∞`, `-∞ → NaN`, `±0 → ±0`, negative finite → NaN,
positive finite via `Bsqrt_correct_aux`. -/
noncomputable def Bsqrt (hp : 0 < prec) (hmax : prec < emax)
    (sqrt_nan : binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x : binary_float prec emax) : binary_float prec emax :=
  match x with
  | B754_nan _ _ _ => build_nan (sqrt_nan x)
  | B754_infinity false => B754_infinity false
  | B754_infinity true => build_nan (sqrt_nan x)
  | B754_zero sx => B754_zero sx
  | B754_finite true _ _ _ => build_nan (sqrt_nan x)
  | B754_finite false mx ex Hx =>
    FF2B _ (Bsqrt_correct_aux hp hmax m mx ex Hx).1

/-- **`Bsqrt_correct`** (Coq lines 2136–2179): the user-facing correctness
for `Bsqrt`. The result `B2R = round(sqrt(B2R x))` unconditionally,
`is_finite` matches the structural condition (zero or positive finite),
and (when not NaN) the sign is preserved. -/
theorem Bsqrt_correct (hp : 0 < prec) (hmax : prec < emax)
    (sqrt_nan : binary_float prec emax →
                  {x : binary_float prec emax // is_nan x = true})
    (m : mode) (x : binary_float prec emax) :
    B2R (Bsqrt hp hmax sqrt_nan m x) =
      round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
        (Real.sqrt (B2R x)) ∧
    is_finite (Bsqrt hp hmax sqrt_nan m x) =
      (match x with
       | B754_zero _ => true
       | B754_finite false _ _ _ => true
       | _ => false) ∧
    (is_nan (Bsqrt hp hmax sqrt_nan m x) = false →
      Bsign (Bsqrt hp hmax sqrt_nan m x) = Bsign x) := by
  cases x with
  | B754_nan sx plx hplx =>
    have h_Bsqrt_eq : Bsqrt hp hmax sqrt_nan m (B754_nan sx plx hplx)
                    = build_nan (sqrt_nan (B754_nan sx plx hplx)) := rfl
    rw [h_Bsqrt_eq]
    have h_B2R_x : B2R (B754_nan (prec := prec) (emax := emax) sx plx hplx)
                  = (0 : ℝ) := rfl
    rw [h_B2R_x, Real.sqrt_zero, round_0]
    refine ⟨B2R_build_nan _, ?_, ?_⟩
    · rw [is_finite_build_nan]
    · intro hcon
      rw [is_nan_build_nan] at hcon
      exact Bool.noConfusion hcon
  | B754_infinity sx =>
    cases sx with
    | false =>
      have h_Bsqrt_eq : Bsqrt hp hmax sqrt_nan m (B754_infinity (prec := prec) (emax := emax) false)
                      = B754_infinity false := rfl
      rw [h_Bsqrt_eq]
      have h_B2R_x : B2R (B754_infinity (prec := prec) (emax := emax) false)
                    = (0 : ℝ) := rfl
      rw [h_B2R_x, Real.sqrt_zero, round_0]
      refine ⟨rfl, rfl, ?_⟩
      intro _; rfl
    | true =>
      have h_Bsqrt_eq : Bsqrt hp hmax sqrt_nan m (B754_infinity (prec := prec) (emax := emax) true)
                      = build_nan (sqrt_nan (B754_infinity true)) := rfl
      rw [h_Bsqrt_eq]
      have h_B2R_x : B2R (B754_infinity (prec := prec) (emax := emax) true)
                    = (0 : ℝ) := rfl
      rw [h_B2R_x, Real.sqrt_zero, round_0]
      refine ⟨B2R_build_nan _, ?_, ?_⟩
      · rw [is_finite_build_nan]
      · intro hcon
        rw [is_nan_build_nan] at hcon
        exact Bool.noConfusion hcon
  | B754_zero sx =>
    have h_Bsqrt_eq : Bsqrt hp hmax sqrt_nan m (B754_zero (prec := prec) (emax := emax) sx)
                    = B754_zero sx := rfl
    rw [h_Bsqrt_eq]
    have h_B2R_x : B2R (B754_zero (prec := prec) (emax := emax) sx)
                  = (0 : ℝ) := rfl
    rw [h_B2R_x, Real.sqrt_zero, round_0]
    refine ⟨rfl, rfl, ?_⟩
    intro _; rfl
  | B754_finite sx mx ex Hx =>
    cases sx with
    | true =>
      -- Negative finite → build_nan. sqrt of negative = 0 in Real.
      have h_Bsqrt_eq : Bsqrt hp hmax sqrt_nan m (B754_finite true mx ex Hx)
                      = build_nan (sqrt_nan (B754_finite true mx ex Hx)) := rfl
      rw [h_Bsqrt_eq]
      have h_B2R_x : B2R (B754_finite (prec := prec) (emax := emax) true mx ex Hx)
                  = F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩ := rfl
      have h_mx_pos : 0 < mx := Hx.1
      have h_F2R_neg : F2R (beta := radix2) ⟨cond_Zopp true mx, ex⟩ < 0 := by
        show ((cond_Zopp true mx : ℤ) : ℝ) * bpow radix2 ex < 0
        have h_neg : ((cond_Zopp true mx : ℤ) : ℝ) < 0 := by
          show ((-mx : ℤ) : ℝ) < 0
          exact_mod_cast (by linarith : (-mx : ℤ) < 0)
        have h_bpow_pos : 0 < bpow radix2 ex := bpow_gt_0 _ _
        nlinarith
      rw [h_B2R_x, Real.sqrt_eq_zero'.mpr (le_of_lt h_F2R_neg), round_0]
      refine ⟨B2R_build_nan _, ?_, ?_⟩
      · rw [is_finite_build_nan]
      · intro hcon
        rw [is_nan_build_nan] at hcon
        exact Bool.noConfusion hcon
    | false =>
      -- Positive finite: apply Bsqrt_correct_aux.
      have h_aux := Bsqrt_correct_aux hp hmax m mx ex Hx
      have h_Bsqrt_eq : Bsqrt hp hmax sqrt_nan m (B754_finite false mx ex Hx)
                      = FF2B _ h_aux.1 := rfl
      rw [h_Bsqrt_eq]
      obtain ⟨h_valid, h_round_eq, h_finite, h_sign⟩ := h_aux
      have h_B2R_x : B2R (B754_finite (prec := prec) (emax := emax) false mx ex Hx)
                  = F2R (beta := radix2) ⟨mx, ex⟩ := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [B2R_FF2B, h_B2R_x]; exact h_round_eq
      · rw [is_finite_FF2B]; exact h_finite
      · intro _; rw [Bsign_FF2B]; exact h_sign

end binary_float

end LeanFlocq
