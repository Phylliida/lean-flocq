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

end shr_record

end LeanFlocq
