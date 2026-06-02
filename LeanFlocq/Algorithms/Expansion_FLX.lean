/-
# Floating-point expansions (Shewchuk) — the exactness layer, at FLX

A *floating-point expansion* is a list of FLX-representable reals `e = [e₀, …, eₙ]`
whose **exact sum** `Σ eᵢ` is the value it represents. Shewchuk's adaptive
geometric predicates (`orient2d`, `orient3d`, `incircle`, `insphere`) are built on
arithmetic over such expansions: growing in a single float, summing two expansions,
and scaling by a single float — each done so that the *value* is computed with **no
rounding error at all**, by carrying every rounding residual as an extra component.

This file builds the **exactness layer**: each operation is proved to produce an
expansion whose sum equals the exact mathematical value, and to preserve the
"every component is a float" invariant (`Expansion`). The two atoms are the
error-free transformations we already have as Flocq facts:

* `plus_error`     — `(a+b) − ◦(a+b) ∈ F`   (the TwoSum residual is a float)
* `mult_error_FLX` — `(a·b) − ◦(a·b) ∈ F`   (the TwoProduct residual is a float)

Because these are the *mathematical* error-representability facts (not the
operational Dekker/Knuth algorithms), the whole exactness layer works at **general
radix**, FLX, round-to-nearest. (The radix-2 restriction only ever came from the
*operational* `TwoProduct` kernel; the expansion value-theory does not need it.)

The headline results:

* `growExpansion_sum`   : `Σ grow(e, b)   = b + Σ e`
* `expansionSum_sum`    : `Σ (e ⊕ f)      = Σ e + Σ f`
* `scaleExpansion_sum`  : `Σ scale(e, b)  = b · Σ e`
* `det2_sum`            : `Σ det2(a,b,c,d) = a·d − b·c`   (the `orient2d` kernel)

each with the companion `…_format` (the result is again an `Expansion`).

**Scope (honest).** This is the *exactness* layer only. The structural theory —
nonoverlapping / nonadjacent invariants, `fast_expansion_sum` (the O(m+n) merge),
sign-reading, length bounds, `compress` — is deliberately *not* here; that is what
makes the predicates *adaptive/fast*, and it is the next arc. `expansionSum` here
is the O(m·n) grow-fold (value-equivalent to Shewchuk's `expansion_sum`);
`scaleExpansion` here is the simplest exact per-component split (value-equivalent to
Shewchuk's `scale_expansion`, but not yet compressed to a nonoverlapping result).
-/
import LeanFlocq.Core.FLX
import LeanFlocq.Prop.Mult_error
import LeanFlocq.Prop.Plus_error

namespace LeanFlocq

open Classical

noncomputable section

variable (beta : radix) (prec : ℤ) (hp : 0 < prec) (choice : ℤ → Bool)

/-- An **expansion** is a list of reals, each representable in `FLX prec`. Its value
is `List.sum`. -/
def Expansion (e : List ℝ) : Prop :=
  ∀ x ∈ e, generic_format beta (FLX_exp prec) x

/-! ### Atoms: the two error-free transformations as `hi + lo` splits -/

/-- High word of a TwoSum: `◦(a + b)`. -/
def twoSumHi (a b : ℝ) : ℝ := round beta (FLX_exp prec) (Znearest choice) (a + b)

/-- Low word of a TwoSum: the exact residual `(a + b) − ◦(a + b)`. -/
def twoSumLo (a b : ℝ) : ℝ := (a + b) - twoSumHi beta prec choice a b

/-- High word of a TwoProduct: `◦(a · b)`. -/
def twoProdHi (a b : ℝ) : ℝ := round beta (FLX_exp prec) (Znearest choice) (a * b)

/-- Low word of a TwoProduct: the exact residual `(a · b) − ◦(a · b)`. -/
def twoProdLo (a b : ℝ) : ℝ := (a * b) - twoProdHi beta prec choice a b

/-- TwoSum reconstructs the exact sum: `hi + lo = a + b`. -/
theorem twoSum_add (a b : ℝ) :
    twoSumHi beta prec choice a b + twoSumLo beta prec choice a b = a + b := by
  unfold twoSumLo; ring

/-- TwoProduct reconstructs the exact product: `hi + lo = a · b`. -/
theorem twoProd_add (a b : ℝ) :
    twoProdHi beta prec choice a b + twoProdLo beta prec choice a b = a * b := by
  unfold twoProdLo; ring

include hp in
/-- The TwoSum high word is a float. -/
theorem twoSumHi_format (a b : ℝ) :
    generic_format beta (FLX_exp prec) (twoSumHi beta prec choice a b) :=
  generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) (a + b)

include hp in
/-- The TwoSum low word (the residual) is a float — this is `plus_error`. -/
theorem twoSumLo_format {a b : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b) :
    generic_format beta (FLX_exp prec) (twoSumLo beta prec choice a b) := by
  unfold twoSumLo twoSumHi
  rw [show (a + b) - round beta (FLX_exp prec) (Znearest choice) (a + b)
        = -(round beta (FLX_exp prec) (Znearest choice) (a + b) - (a + b)) from by ring]
  exact generic_format_opp beta (FLX_exp prec)
    (plus_error beta (FLX_exp prec) (FLX_exp_valid prec hp) (FLX_exp_monotone prec) choice Fa Fb)

include hp in
/-- The TwoProduct high word is a float. -/
theorem twoProdHi_format (a b : ℝ) :
    generic_format beta (FLX_exp prec) (twoProdHi beta prec choice a b) :=
  generic_format_round beta (FLX_exp prec) (FLX_exp_valid prec hp) (Znearest choice) (a * b)

include hp in
/-- The TwoProduct low word (the residual) is a float — this is `mult_error_FLX`. -/
theorem twoProdLo_format {a b : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b) :
    generic_format beta (FLX_exp prec) (twoProdLo beta prec choice a b) := by
  unfold twoProdLo twoProdHi
  rw [show (a * b) - round beta (FLX_exp prec) (Znearest choice) (a * b)
        = -(round beta (FLX_exp prec) (Znearest choice) (a * b) - a * b) from by ring]
  exact generic_format_opp beta (FLX_exp prec)
    (mult_error_FLX beta prec hp (Znearest choice) Fa Fb)

/-! ### `grow_expansion` — Shewchuk's O(m) sweep of one float through an expansion -/

/-- Sweep a running carry `Q` through `e`, emitting each TwoSum residual and finally
the carry. `growAux Q e` has length `e.length + 1`. -/
def growAux (Q : ℝ) (e : List ℝ) : List ℝ :=
  match e with
  | [] => [Q]
  | x :: rest =>
      twoSumLo beta prec choice Q x :: growAux (twoSumHi beta prec choice Q x) rest

/-- `grow_expansion`: add a single float `b` to expansion `e`. -/
def growExpansion (e : List ℝ) (b : ℝ) : List ℝ := growAux beta prec choice b e

/-- The sweep is exact: `Σ growAux(Q, e) = Q + Σ e`. -/
theorem growAux_sum (Q : ℝ) (e : List ℝ) :
    (growAux beta prec choice Q e).sum = Q + e.sum := by
  induction e generalizing Q with
  | nil => simp only [growAux, List.sum_cons, List.sum_nil, add_zero]
  | cons x rest ih =>
      have hadd := twoSum_add beta prec choice Q x
      simp only [growAux, List.sum_cons, ih (twoSumHi beta prec choice Q x)]
      linarith [hadd]

include hp in
/-- The sweep preserves the float invariant. -/
theorem growAux_format :
    ∀ (e : List ℝ) (Q : ℝ), generic_format beta (FLX_exp prec) Q →
      (∀ x ∈ e, generic_format beta (FLX_exp prec) x) →
      ∀ y ∈ growAux beta prec choice Q e, generic_format beta (FLX_exp prec) y := by
  intro e
  induction e with
  | nil =>
      intro Q FQ _ y hy
      simp only [growAux, List.mem_singleton] at hy
      rw [hy]; exact FQ
  | cons x rest ih =>
      intro Q FQ Fe y hy
      have Fx : generic_format beta (FLX_exp prec) x := Fe x (by simp)
      have Frest : ∀ z ∈ rest, generic_format beta (FLX_exp prec) z :=
        fun z hz => Fe z (List.mem_cons_of_mem _ hz)
      simp only [growAux, List.mem_cons] at hy
      rcases hy with rfl | h
      · exact twoSumLo_format beta prec hp choice FQ Fx
      · exact ih (twoSumHi beta prec choice Q x)
          (twoSumHi_format beta prec hp choice Q x) Frest y h

/-- `Σ grow(e, b) = b + Σ e`. -/
theorem growExpansion_sum (e : List ℝ) (b : ℝ) :
    (growExpansion beta prec choice e b).sum = b + e.sum :=
  growAux_sum beta prec choice b e

include hp in
/-- `grow` preserves the expansion invariant. -/
theorem growExpansion_format {e : List ℝ} {b : ℝ}
    (Fe : Expansion beta prec e) (Fb : generic_format beta (FLX_exp prec) b) :
    Expansion beta prec (growExpansion beta prec choice e b) :=
  fun y hy => growAux_format beta prec hp choice e b Fb Fe y hy

/-! ### `expansion_sum` — add two expansions (the O(m·n) grow-fold) -/

/-- Add two expansions by growing each component of `f` into `e`. -/
def expansionSum (e f : List ℝ) : List ℝ :=
  f.foldl (fun acc b => growExpansion beta prec choice acc b) e

/-- `Σ (e ⊕ f) = Σ e + Σ f`. -/
theorem expansionSum_sum (e f : List ℝ) :
    (expansionSum beta prec choice e f).sum = e.sum + f.sum := by
  unfold expansionSum
  induction f generalizing e with
  | nil => simp
  | cons b rest ih =>
      simp only [List.foldl_cons]
      rw [ih (growExpansion beta prec choice e b),
          growExpansion_sum beta prec choice e b, List.sum_cons]
      ring

include hp in
/-- `expansion_sum` preserves the expansion invariant. -/
theorem expansionSum_format_aux :
    ∀ (f e : List ℝ), Expansion beta prec e → Expansion beta prec f →
      Expansion beta prec (expansionSum beta prec choice e f) := by
  intro f
  induction f with
  | nil => intro e Fe _; simpa [expansionSum] using Fe
  | cons b rest ih =>
      intro e Fe Fbf
      have Fb : generic_format beta (FLX_exp prec) b := Fbf b (by simp)
      have Frest : Expansion beta prec rest :=
        fun z hz => Fbf z (List.mem_cons_of_mem _ hz)
      have Fgrow : Expansion beta prec (growExpansion beta prec choice e b) :=
        growExpansion_format beta prec hp choice Fe Fb
      have hstep : expansionSum beta prec choice e (b :: rest)
          = expansionSum beta prec choice (growExpansion beta prec choice e b) rest := by
        simp [expansionSum, List.foldl_cons]
      rw [hstep]
      exact ih (growExpansion beta prec choice e b) Fgrow Frest

include hp in
/-- `expansion_sum` preserves the expansion invariant (clean argument order). -/
theorem expansionSum_format {e f : List ℝ}
    (Fe : Expansion beta prec e) (Ff : Expansion beta prec f) :
    Expansion beta prec (expansionSum beta prec choice e f) :=
  expansionSum_format_aux beta prec hp choice f e Fe Ff

/-! ### `scale_expansion` — multiply an expansion by a single float -/

/-- Scale each component `x` of `e` by `b`, emitting both words of `TwoProduct(x, b)`.
`scaleAux e b` has length `2 · e.length`. -/
def scaleAux (e : List ℝ) (b : ℝ) : List ℝ :=
  match e with
  | [] => []
  | x :: rest =>
      twoProdLo beta prec choice x b :: twoProdHi beta prec choice x b :: scaleAux rest b

/-- `scale_expansion`: multiply expansion `e` by a single float `b`. -/
def scaleExpansion (e : List ℝ) (b : ℝ) : List ℝ := scaleAux beta prec choice e b

/-- `Σ scale(e, b) = b · Σ e`. -/
theorem scaleAux_sum (e : List ℝ) (b : ℝ) :
    (scaleAux beta prec choice e b).sum = b * e.sum := by
  induction e with
  | nil => simp only [scaleAux, List.sum_nil, mul_zero]
  | cons x rest ih =>
      simp only [scaleAux, List.sum_cons, ih, mul_add]
      linear_combination twoProd_add beta prec choice x b

include hp in
/-- `scale_expansion` preserves the expansion invariant. -/
theorem scaleAux_format :
    ∀ (e : List ℝ) (b : ℝ), Expansion beta prec e →
      generic_format beta (FLX_exp prec) b →
      Expansion beta prec (scaleAux beta prec choice e b) := by
  intro e
  induction e with
  | nil => intro b _ _ y hy; simp only [scaleAux, List.not_mem_nil] at hy
  | cons x rest ih =>
      intro b Fe Fb y hy
      have Fx : generic_format beta (FLX_exp prec) x := Fe x (by simp)
      have Frest : Expansion beta prec rest :=
        fun z hz => Fe z (List.mem_cons_of_mem _ hz)
      simp only [scaleAux, List.mem_cons] at hy
      rcases hy with rfl | rfl | h
      · exact twoProdLo_format beta prec hp choice Fx Fb
      · exact twoProdHi_format beta prec hp choice x b
      · exact ih b Frest Fb y h

/-- `Σ scale(e, b) = b · Σ e`. -/
theorem scaleExpansion_sum (e : List ℝ) (b : ℝ) :
    (scaleExpansion beta prec choice e b).sum = b * e.sum :=
  scaleAux_sum beta prec choice e b

include hp in
/-- `scale` preserves the expansion invariant. -/
theorem scaleExpansion_format {e : List ℝ} {b : ℝ}
    (Fe : Expansion beta prec e) (Fb : generic_format beta (FLX_exp prec) b) :
    Expansion beta prec (scaleExpansion beta prec choice e b) :=
  scaleAux_format beta prec hp choice e b Fe Fb

/-! ### Negation of an expansion (component-wise) -/

/-- Negate every component. -/
def negExp (e : List ℝ) : List ℝ := e.map (fun x => -x)

/-- `Σ (−e) = −Σ e`. -/
theorem negExp_sum (e : List ℝ) : (negExp e).sum = -e.sum := by
  unfold negExp
  induction e with
  | nil => simp
  | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Negation preserves the expansion invariant. -/
theorem negExp_format {e : List ℝ} (Fe : Expansion beta prec e) :
    Expansion beta prec (negExp e) := by
  intro y hy
  simp only [negExp, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact generic_format_opp beta (FLX_exp prec) (Fe x hx)

/-! ### Capstone: the exact 2×2 determinant — the `orient2d` kernel -/

/-- The two-component expansion of an exact product `a · b`. -/
def prodExp (a b : ℝ) : List ℝ :=
  [twoProdLo beta prec choice a b, twoProdHi beta prec choice a b]

/-- `Σ prodExp(a, b) = a · b`. -/
theorem prodExp_sum (a b : ℝ) : (prodExp beta prec choice a b).sum = a * b := by
  simp only [prodExp, List.sum_cons, List.sum_nil, add_zero]
  linear_combination twoProd_add beta prec choice a b

include hp in
/-- `prodExp a b` is an expansion when `a, b` are floats. -/
theorem prodExp_format {a b : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b) :
    Expansion beta prec (prodExp beta prec choice a b) := by
  intro y hy
  simp only [prodExp, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact twoProdLo_format beta prec hp choice Fa Fb
  · exact twoProdHi_format beta prec hp choice a b

/-- The exact 2×2 determinant `a·d − b·c` as a floating-point expansion: the kernel
of the `orient2d` adaptive predicate. Built as `prodExp(a,d) ⊕ (−prodExp(b,c))`. -/
def det2 (a b c d : ℝ) : List ℝ :=
  expansionSum beta prec choice
    (prodExp beta prec choice a d) (negExp (prodExp beta prec choice b c))

/-- **The 2×2 determinant is computed exactly:** `Σ det2(a,b,c,d) = a·d − b·c`. -/
theorem det2_sum (a b c d : ℝ) :
    (det2 beta prec choice a b c d).sum = a * d - b * c := by
  unfold det2
  rw [expansionSum_sum, prodExp_sum, negExp_sum, prodExp_sum]
  ring

include hp in
/-- `det2` is an expansion when all four inputs are floats. -/
theorem det2_format {a b c d : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a)
    (Fb : generic_format beta (FLX_exp prec) b)
    (Fc : generic_format beta (FLX_exp prec) c)
    (Fd : generic_format beta (FLX_exp prec) d) :
    Expansion beta prec (det2 beta prec choice a b c d) :=
  expansionSum_format beta prec hp choice
    (prodExp_format beta prec hp choice Fa Fd)
    (negExp_format beta prec (prodExp_format beta prec hp choice Fb Fc))

end

end LeanFlocq
