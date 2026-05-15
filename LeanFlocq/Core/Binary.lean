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

end binary_float

end LeanFlocq
