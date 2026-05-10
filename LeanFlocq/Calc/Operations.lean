/-
Port of `flocq/src/Calc/Operations.v` (Sylvie Boldo, Guillaume Melquiond, LGPL).

Basic arithmetic operations on floats: alignment, addition, subtraction,
multiplication, negation, absolute value. Each operation is paired with an
`F2R_*` correctness theorem giving its real-value semantics.
-/

import LeanFlocq.Core.Float_prop

namespace LeanFlocq

variable {beta : radix}

/-! ## Alignment

`Falign f1 f2` returns a triple `(m1', m2', e)` such that both `f1` and
`f2` have the same exponent `e = min(f1.Fexp, f2.Fexp)`, with appropriately
scaled mantissas `m1'` and `m2'`. -/

/-- Align two floats to a common exponent (the smaller of the two). -/
noncomputable def Falign (f1 f2 : float beta) : ℤ × ℤ × ℤ :=
  if f1.Fexp ≤ f2.Fexp then
    (f1.Fnum, f2.Fnum * (beta.val : ℤ) ^ (f2.Fexp - f1.Fexp).toNat, f1.Fexp)
  else
    (f1.Fnum * (beta.val : ℤ) ^ (f1.Fexp - f2.Fexp).toNat, f2.Fnum, f2.Fexp)

theorem Falign_spec (f1 f2 : float beta) :
    let (m1, m2, e) := Falign f1 f2
    F2R f1 = F2R (beta := beta) ⟨m1, e⟩ ∧ F2R f2 = F2R (beta := beta) ⟨m2, e⟩ := by
  unfold Falign
  by_cases h : f1.Fexp ≤ f2.Fexp
  · simp only [if_pos h]
    refine ⟨?_, ?_⟩
    · cases f1; trivial
    · cases f2 with | mk m2 e2 =>
      exact F2R_change_exp f1.Fexp m2 e2 h
  · simp only [if_neg h]
    refine ⟨?_, ?_⟩
    · cases f1 with | mk m1 e1 =>
      have h' : f2.Fexp ≤ e1 := by simp at h; omega
      exact F2R_change_exp f2.Fexp m1 e1 h'
    · cases f2; trivial

theorem Falign_spec_exp (f1 f2 : float beta) :
    (Falign f1 f2).2.2 = min f1.Fexp f2.Fexp := by
  unfold Falign
  by_cases h : f1.Fexp ≤ f2.Fexp
  · simp only [if_pos h]
    show f1.Fexp = min f1.Fexp f2.Fexp
    rw [min_eq_left h]
  · simp only [if_neg h]
    show f2.Fexp = min f1.Fexp f2.Fexp
    rw [min_eq_right (by omega)]

/-! ## Negation and absolute value -/

/-- Negate a float. -/
def Fopp (f : float beta) : float beta := ⟨-f.Fnum, f.Fexp⟩

theorem F2R_opp (f : float beta) : F2R (Fopp f) = -F2R f := by
  cases f with | mk m e =>
  exact F2R_Zopp m e

/-- Absolute value of a float. -/
def Fabs (f : float beta) : float beta := ⟨|f.Fnum|, f.Fexp⟩

theorem F2R_abs (f : float beta) : F2R (Fabs f) = |F2R f| := by
  cases f with | mk m e =>
  exact F2R_Zabs m e

/-! ## Addition -/

/-- Add two floats, aligning to the smaller exponent. -/
noncomputable def Fplus (f1 f2 : float beta) : float beta :=
  let a := Falign f1 f2
  ⟨a.1 + a.2.1, a.2.2⟩

theorem F2R_plus (f1 f2 : float beta) :
    F2R (Fplus f1 f2) = F2R f1 + F2R f2 := by
  unfold Fplus
  have hs := Falign_spec f1 f2
  set a := Falign f1 f2 with ha
  obtain ⟨h1, h2⟩ := hs
  rw [h1, h2]
  -- Goal: F2R ⟨a.1 + a.2.1, a.2.2⟩ = F2R ⟨a.1, a.2.2⟩ + F2R ⟨a.2.1, a.2.2⟩
  unfold F2R
  show ((a.1 + a.2.1 : ℤ) : ℝ) * bpow beta a.2.2
      = (a.1 : ℝ) * bpow beta a.2.2 + (a.2.1 : ℝ) * bpow beta a.2.2
  push_cast; ring

theorem Fplus_same_exp (m1 m2 e : ℤ) :
    Fplus (beta := beta) ⟨m1, e⟩ ⟨m2, e⟩ = ⟨m1 + m2, e⟩ := by
  unfold Fplus Falign
  simp

theorem Fexp_Fplus (f1 f2 : float beta) :
    (Fplus f1 f2).Fexp = min f1.Fexp f2.Fexp := by
  show (Falign f1 f2).2.2 = _
  exact Falign_spec_exp f1 f2

/-! ## Subtraction -/

/-- Subtract two floats: `f1 - f2 := f1 + (-f2)`. -/
noncomputable def Fminus (f1 f2 : float beta) : float beta :=
  Fplus f1 (Fopp f2)

theorem F2R_minus (f1 f2 : float beta) :
    F2R (Fminus f1 f2) = F2R f1 - F2R f2 := by
  unfold Fminus
  rw [F2R_plus, F2R_opp]; ring

theorem Fminus_same_exp (m1 m2 e : ℤ) :
    Fminus (beta := beta) ⟨m1, e⟩ ⟨m2, e⟩ = ⟨m1 - m2, e⟩ := by
  unfold Fminus Fopp
  rw [Fplus_same_exp]
  show (⟨m1 + (-m2), e⟩ : float beta) = ⟨m1 - m2, e⟩
  rw [show m1 + (-m2) = m1 - m2 from by ring]

/-! ## Multiplication -/

/-- Multiply two floats: mantissas multiply, exponents add. -/
def Fmult (f1 f2 : float beta) : float beta :=
  ⟨f1.Fnum * f2.Fnum, f1.Fexp + f2.Fexp⟩

theorem F2R_mult (f1 f2 : float beta) :
    F2R (Fmult f1 f2) = F2R f1 * F2R f2 := by
  cases f1 with | mk m1 e1 =>
  cases f2 with | mk m2 e2 =>
  unfold Fmult F2R
  show ((m1 * m2 : ℤ) : ℝ) * bpow beta (e1 + e2)
      = ((m1 : ℝ) * bpow beta e1) * ((m2 : ℝ) * bpow beta e2)
  rw [bpow_plus]
  push_cast
  ring

end LeanFlocq
