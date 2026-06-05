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

/-! ## Stage 2 (begun): sign-reading

The keystone that makes expansions usable for *exact sign decisions* — the CAD
filter/fallback. If the leading (largest-magnitude) component `h` dominates the
combined magnitude of all the others, then the exact value `h + Σt` is nonzero and
shares `h`'s sign: the sign of the represented number can be read off one component.

`HeadDom` is the value-based, **radix-general** form of Shewchuk's
"sorted + nonoverlapping" condition. *Producing* it from the expansion operations
(`grow`/`fast_expansion_sum` preserve it) is the bit-level structural theory — the
larger next arc; here we establish the consumer side and ground it in the rounding
atoms. -/

/-- Triangle inequality for a list sum: `|Σ l| ≤ Σ |l|`. -/
theorem expansion_abs_sum_le (l : List ℝ) :
    |l.sum| ≤ (l.map (fun x => |x|)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.sum_cons, List.map_cons]
      calc |a + t.sum| ≤ |a| + |t.sum| := abs_add_le a t.sum
        _ ≤ |a| + (t.map (fun x => |x|)).sum := by linarith

/-- If a perturbation is strictly dominated in magnitude, `a + b` is nonzero and
keeps `a`'s sign. -/
theorem add_dominated_sign {a b : ℝ} (hab : |b| < |a|) :
    a + b ≠ 0 ∧ (0 < a + b ↔ 0 < a) ∧ (a + b < 0 ↔ a < 0) := by
  have hb := abs_lt.mp hab
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at hb
    have hlt : a + b < 0 := by linarith [hb.2]
    exact ⟨ne_of_lt hlt,
      ⟨fun hpos => by linarith, fun hpos => by linarith⟩,
      ⟨fun _ => ha, fun _ => hlt⟩⟩
  · exfalso
    rw [ha, abs_zero] at hab
    exact absurd hab (not_lt.mpr (abs_nonneg b))
  · rw [abs_of_pos ha] at hb
    have hgt : 0 < a + b := by linarith [hb.1]
    exact ⟨ne_of_gt hgt,
      ⟨fun _ => ha, fun _ => hgt⟩,
      ⟨fun hneg => by linarith, fun hneg => by linarith⟩⟩

/-- The leading component dominates the combined magnitude of the rest — the
condition that lets a sorted, nonoverlapping expansion's sign be read off its top
component. (Forces `h ≠ 0`; `t` may contain zeros.) -/
def HeadDom (h : ℝ) (t : List ℝ) : Prop := (t.map (fun x => |x|)).sum < |h|

/-- A dominating head is nonzero. -/
theorem headDom_ne_zero {h : ℝ} {t : List ℝ} (H : HeadDom h t) : h ≠ 0 := by
  have h0 : (0 : ℝ) ≤ (t.map (fun x => |x|)).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
    exact abs_nonneg y
  intro hh
  unfold HeadDom at H
  rw [hh, abs_zero] at H
  linarith

/-- Under domination, the tail sum is strictly smaller than the head in magnitude. -/
theorem headDom_tail_lt {h : ℝ} {t : List ℝ} (H : HeadDom h t) : |t.sum| < |h| :=
  lt_of_le_of_lt (expansion_abs_sum_le t) H

/-- **Sign-reading.** When the head dominates, the exact sum is nonzero and shares
the head's sign — so the sign of the value represented by `h :: t` is the sign of
`h` alone. -/
theorem headDom_sign {h : ℝ} {t : List ℝ} (H : HeadDom h t) :
    (h :: t).sum ≠ 0 ∧ (0 < (h :: t).sum ↔ 0 < h) ∧ ((h :: t).sum < 0 ↔ h < 0) := by
  have hcons : (h :: t).sum = h + t.sum := by simp
  rw [hcons]
  exact add_dominated_sign (headDom_tail_lt H)

/-- **Leading-term approximation (the filter primitive).** The head approximates the
exact value within the head's own magnitude (in fact within the tail's total
magnitude). -/
theorem headDom_approx {h : ℝ} {t : List ℝ} (H : HeadDom h t) :
    |(h :: t).sum - h| < |h| := by
  have : (h :: t).sum - h = t.sum := by simp
  rw [this]
  exact headDom_tail_lt H

/-! ### Grounding in the rounding atoms -/

include hp in
/-- A single rounding's residual is dominated by the rounded value: for `hi = ◦x`
and `lo = x − hi` with `hi ≠ 0`, `HeadDom hi [lo]` — i.e. `|lo| < |hi|` — via
`|x − ◦x| ≤ ½·ulp(◦x) ≤ ½·|◦x| < |◦x|`. -/
theorem round_residual_headDom {x : ℝ}
    (hx : round beta (FLX_exp prec) (Znearest choice) x ≠ 0) :
    HeadDom (round beta (FLX_exp prec) (Znearest choice) x)
      [x - round beta (FLX_exp prec) (Znearest choice) x] := by
  set hi := round beta (FLX_exp prec) (Znearest choice) x with hhi
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have herr : |hi - x| ≤ (1 / 2) * ulp beta (FLX_exp prec) hi :=
    error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice x
  have huf : ulp beta (FLX_exp prec) hi ≤ |hi| :=
    ulp_le_abs beta (FLX_exp prec) hx
      (generic_format_round beta (FLX_exp prec) hValid (Znearest choice) x)
  have hupos : 0 < |hi| := abs_pos.mpr hx
  unfold HeadDom
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show x - hi = -(hi - x) from by ring, abs_neg]
  linarith

include hp in
/-- The two words of a `TwoProduct` form a sign-readable pair: when `◦(a·b) ≠ 0`,
`HeadDom (twoProdHi a b) [twoProdLo a b]`. -/
theorem twoProd_headDom {a b : ℝ}
    (hab : twoProdHi beta prec choice a b ≠ 0) :
    HeadDom (twoProdHi beta prec choice a b) [twoProdLo beta prec choice a b] :=
  round_residual_headDom beta prec hp choice hab

include hp in
/-- **Reading the sign of a product off its rounded value:** `0 < a·b ↔ 0 < ◦(a·b)`
(when `◦(a·b) ≠ 0`), justified by the dominated residual. -/
theorem twoProd_sign {a b : ℝ}
    (hab : twoProdHi beta prec choice a b ≠ 0) :
    (0 < a * b ↔ 0 < twoProdHi beta prec choice a b) := by
  have hH := twoProd_headDom beta prec hp choice hab
  have hsumeq :
      (twoProdHi beta prec choice a b :: [twoProdLo beta prec choice a b]).sum = a * b := by
    simp only [List.sum_cons, List.sum_nil, add_zero]
    exact twoProd_add beta prec choice a b
  have := (headDom_sign hH).2.1
  rwa [hsumeq] at this

include hp in
/-- The two words of a `TwoSum` form a sign-readable pair: when `◦(a+b) ≠ 0`,
`HeadDom (twoSumHi a b) [twoSumLo a b]`. -/
theorem twoSum_headDom {a b : ℝ}
    (hab : twoSumHi beta prec choice a b ≠ 0) :
    HeadDom (twoSumHi beta prec choice a b) [twoSumLo beta prec choice a b] :=
  round_residual_headDom beta prec hp choice hab

include hp in
/-- **Reading the sign of a sum off its rounded value:** `0 < a+b ↔ 0 < ◦(a+b)`
(when `◦(a+b) ≠ 0`). -/
theorem twoSum_sign {a b : ℝ}
    (hab : twoSumHi beta prec choice a b ≠ 0) :
    (0 < a + b ↔ 0 < twoSumHi beta prec choice a b) := by
  have hH := twoSum_headDom beta prec hp choice hab
  have hsumeq :
      (twoSumHi beta prec choice a b :: [twoSumLo beta prec choice a b]).sum = a + b := by
    simp only [List.sum_cons, List.sum_nil, add_zero]
    exact twoSum_add beta prec choice a b
  have := (headDom_sign hH).2.1
  rwa [hsumeq] at this

/-! ### The structural invariant: `Separated` (sorted ulp-separation chain)

`HeadDom` (the sign-reading certificate) is *implied* by the structural invariant
Shewchuk's operations are designed to maintain: a **sorted, largest-first chain in
which each component is at most half the ulp of its predecessor**. This is the
value-based form of "sorted + nonoverlapping". Here we (a) define it, (b) prove it
implies `HeadDom` — so the keystone `headDom_sign` applies — and (c) discharge the
base case (a single `TwoSum`/`TwoProduct` is `Separated`). *Preserving* `Separated`
through `grow`/`fast_expansion_sum` (the bit-level sweep theorems) is the next arc. -/

/-- `SeparatedFrom prev t`: the list `t`, read largest-first, is a ulp-separation
chain whose first element is at most half the ulp of `prev`. -/
def SeparatedFrom (prev : ℝ) : List ℝ → Prop
  | [] => True
  | h :: t => |h| ≤ (1 / 2) * ulp beta (FLX_exp prec) prev ∧ SeparatedFrom h t

/-- `Separated e`: `e` is a sorted (largest-first) ulp-separation chain — each
component at most half the ulp of the one before it. -/
def Separated : List ℝ → Prop
  | [] => True
  | h :: t => SeparatedFrom beta prec h t

include hp in
/-- The technical heart: in a ulp-separation chain below `prev`, the total magnitude
of the chain is at most `ulp prev` (geometric domination, summed exactly). -/
theorem separatedFrom_abs_sum_le :
    ∀ (t : List ℝ) (prev : ℝ), SeparatedFrom beta prec prev t →
      (∀ x ∈ t, generic_format beta (FLX_exp prec) x) →
      (t.map (fun x => |x|)).sum ≤ ulp beta (FLX_exp prec) prev := by
  intro t
  induction t with
  | nil => intro prev _ _; simp only [List.map_nil, List.sum_nil]; exact ulp_ge_0 _ _ _
  | cons e1 t' ih =>
      intro prev Ht HF
      simp only [SeparatedFrom] at Ht
      obtain ⟨h1, h2⟩ := Ht
      have Fe1 : generic_format beta (FLX_exp prec) e1 := HF e1 (by simp)
      have HFt' : ∀ x ∈ t', generic_format beta (FLX_exp prec) x :=
        fun x hx => HF x (List.mem_cons_of_mem _ hx)
      have iht := ih e1 h2 HFt'
      have hule : ulp beta (FLX_exp prec) e1 ≤ (1 / 2) * ulp beta (FLX_exp prec) prev := by
        rcases eq_or_ne e1 0 with he | he
        · rw [he, ulp_FLX_0 beta prec hp]
          have := ulp_ge_0 beta (FLX_exp prec) prev
          linarith
        · exact le_trans (ulp_le_abs beta (FLX_exp prec) he Fe1) h1
      have hsum : ((e1 :: t').map (fun x => |x|)).sum
          = |e1| + (t'.map (fun x => |x|)).sum := by simp [List.sum_cons]
      rw [hsum]
      linarith [iht, h1, hule]

/-- In FLX with `prec ≥ 2`, a nonzero float's ulp is strictly below its magnitude
(`ulp x ≤ |x|·β^(1−prec) < |x|`). -/
theorem ulp_lt_abs_FLX (hp2 : 2 ≤ prec) {h : ℝ} (hh : h ≠ 0) :
    ulp beta (FLX_exp prec) h < |h| := by
  have h1 : ulp beta (FLX_exp prec) h ≤ |h| * bpow beta (1 - prec) :=
    ulp_FLX_le beta prec (by omega) h
  have h2 : bpow beta (1 - prec) < 1 := by
    have hlt : bpow beta (1 - prec) < bpow beta 0 := bpow_lt beta (by omega)
    rwa [bpow_zero] at hlt
  have h3 : 0 < |h| := abs_pos.mpr hh
  calc ulp beta (FLX_exp prec) h ≤ |h| * bpow beta (1 - prec) := h1
    _ < |h| * 1 := mul_lt_mul_of_pos_left h2 h3
    _ = |h| := mul_one _

include hp in
/-- **Structure ⟹ sign-reading certificate.** A `Separated` expansion with a nonzero
(hence leading) head satisfies `HeadDom`, so its sign is read off the head via
`headDom_sign`. Needs `prec ≥ 2` and the tail in-format. -/
theorem separated_headDom (hp2 : 2 ≤ prec) {h : ℝ} {t : List ℝ}
    (Hsep : Separated beta prec (h :: t)) (hh : h ≠ 0)
    (HF : ∀ x ∈ t, generic_format beta (FLX_exp prec) x) :
    HeadDom h t := by
  unfold Separated at Hsep
  have hbound : (t.map (fun x => |x|)).sum ≤ ulp beta (FLX_exp prec) h :=
    separatedFrom_abs_sum_le beta prec hp t h Hsep HF
  have hult : ulp beta (FLX_exp prec) h < |h| := ulp_lt_abs_FLX beta prec hp2 hh
  unfold HeadDom
  linarith

include hp in
/-- **Sign of a `Separated` expansion.** Nonzero, and the sign is the head's. -/
theorem separated_sign (hp2 : 2 ≤ prec) {h : ℝ} {t : List ℝ}
    (Hsep : Separated beta prec (h :: t)) (hh : h ≠ 0)
    (HF : ∀ x ∈ t, generic_format beta (FLX_exp prec) x) :
    (h :: t).sum ≠ 0 ∧ (0 < (h :: t).sum ↔ 0 < h) ∧ ((h :: t).sum < 0 ↔ h < 0) :=
  headDom_sign (separated_headDom beta prec hp hp2 Hsep hh HF)

include hp in
/-- **Base case of `Separated`:** the high/low words of a single rounding form a
ulp-separation chain (`|x − ◦x| ≤ ½·ulp(◦x)`), unconditionally. -/
theorem round_residual_separated {x : ℝ} :
    Separated beta prec
      [round beta (FLX_exp prec) (Znearest choice) x,
       x - round beta (FLX_exp prec) (Znearest choice) x] := by
  set hi := round beta (FLX_exp prec) (Znearest choice) x with hhi
  have hValid := FLX_exp_valid prec hp
  have hMon := FLX_exp_monotone prec
  have hNF := monotone_exp_not_FTZ hValid hMon
  have herr : |hi - x| ≤ (1 / 2) * ulp beta (FLX_exp prec) hi :=
    error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice x
  unfold Separated
  simp only [SeparatedFrom, and_true]
  rw [show x - hi = -(hi - x) from by ring, abs_neg]
  exact herr

include hp in
/-- The two words of a `TwoProduct` form a `Separated` 2-element expansion. -/
theorem twoProd_separated (a b : ℝ) :
    Separated beta prec [twoProdHi beta prec choice a b, twoProdLo beta prec choice a b] :=
  round_residual_separated beta prec hp choice

include hp in
/-- The two words of a `TwoSum` form a `Separated` 2-element expansion. -/
theorem twoSum_separated (a b : ℝ) :
    Separated beta prec [twoSumHi beta prec choice a b, twoSumLo beta prec choice a b] :=
  round_residual_separated beta prec hp choice

/-! ## Stage 2, the hard arc — faithful bit-level `Nonoverlapping` (begun)

`Separated` (the ½·ulp chain) is perfect for the base case and the structure→sign
bridge, but it is **too strong to be preserved by `grow`**: a sweep produces
residuals at the *same* scale (both `≲ ½ulp` of the running carry), which are
mutually *bit*-nonoverlapping (disjoint bit ranges) but not ulp-chain separated.
So faithful preservation needs Shewchuk's genuine **nonoverlapping** predicate.

This section lays its foundation: the predicate, its basic algebra, and the
rounding **atom** (`◦v` and its residual are nonoverlapping). The remaining work —
the list-level invariant with its 2-adic `HeadDom` bridge, and `grow`/`fast_expansion_sum`
*preserving* it (Shewchuk's Theorem 10 chaining) — is the next arc. -/

/-- `x` is an integer multiple of `β^s`. -/
def MultipleOfPow (s : ℤ) (x : ℝ) : Prop := ∃ m : ℤ, x = (m : ℝ) * bpow beta s

/-- Every float is a multiple of `β^cexp`. -/
theorem multipleOfPow_cexp {x : ℝ} (Fx : generic_format beta (FLX_exp prec) x) :
    MultipleOfPow beta (cexp beta (FLX_exp prec) x) x :=
  ⟨Ztrunc (scaled_mantissa beta (FLX_exp prec) x), Fx⟩

/-- **Nonoverlapping** (Shewchuk): the nonzero bits of `x` and `y` occupy disjoint
ranges. Encoded as: one is an integer multiple of `β^s` while the other is strictly
below `β^s` in magnitude (its bits lie strictly under the `β^s` place). Zero is
nonoverlapping with everything. -/
def Nonoverlapping (x y : ℝ) : Prop :=
  x = 0 ∨ y = 0 ∨
    (∃ s : ℤ, MultipleOfPow beta s x ∧ |y| < bpow beta s) ∨
    (∃ s : ℤ, MultipleOfPow beta s y ∧ |x| < bpow beta s)

/-- Nonoverlapping is symmetric. -/
theorem nonoverlapping_symm {x y : ℝ} (h : Nonoverlapping beta x y) :
    Nonoverlapping beta y x := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem nonoverlapping_zero_right (x : ℝ) : Nonoverlapping beta x 0 := Or.inr (Or.inl rfl)

theorem nonoverlapping_zero_left (x : ℝ) : Nonoverlapping beta 0 x := Or.inl rfl

/-- Sufficient condition: if `y` is strictly within the ulp of a float `x`, they are
nonoverlapping (witness `s = cexp x`, since a float is a multiple of `β^cexp` and
`ulp x = β^cexp x`). -/
theorem nonoverlapping_of_abs_lt_ulp {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (hxy : |y| < ulp beta (FLX_exp prec) x) :
    Nonoverlapping beta x y := by
  rcases eq_or_ne x 0 with hx | hx
  · exact Or.inl hx
  · refine Or.inr (Or.inr (Or.inl ⟨cexp beta (FLX_exp prec) x,
      multipleOfPow_cexp beta prec Fx, ?_⟩))
    rwa [ulp_neq_0 beta (FLX_exp prec) hx] at hxy

include hp in
/-- **The grow base case (faithful form):** a single rounding's high and low words
are nonoverlapping (`|v − ◦v| ≤ ½·ulp(◦v) < ulp(◦v)`). -/
theorem round_residual_nonoverlapping (v : ℝ) :
    Nonoverlapping beta (round beta (FLX_exp prec) (Znearest choice) v)
      (v - round beta (FLX_exp prec) (Znearest choice) v) := by
  set hi := round beta (FLX_exp prec) (Znearest choice) v with hhi
  rcases eq_or_ne hi 0 with h0 | h0
  · exact Or.inl h0
  · have hValid := FLX_exp_valid prec hp
    have hMon := FLX_exp_monotone prec
    have hNF := monotone_exp_not_FTZ hValid hMon
    have herr : |hi - v| ≤ (1 / 2) * ulp beta (FLX_exp prec) hi :=
      error_le_half_ulp_round beta (FLX_exp prec) hValid hNF hMon choice v
    have hupos : 0 < ulp beta (FLX_exp prec) hi := by
      rw [ulp_neq_0 beta (FLX_exp prec) h0]; exact bpow_gt_0 beta _
    have Fhi : generic_format beta (FLX_exp prec) hi :=
      generic_format_round beta (FLX_exp prec) hValid (Znearest choice) v
    apply nonoverlapping_of_abs_lt_ulp beta prec Fhi
    rw [show v - hi = -(hi - v) from by ring, abs_neg]
    linarith

include hp in
/-- The two words of a `TwoProduct` are nonoverlapping. -/
theorem twoProd_nonoverlapping (a b : ℝ) :
    Nonoverlapping beta (twoProdHi beta prec choice a b) (twoProdLo beta prec choice a b) :=
  round_residual_nonoverlapping beta prec hp choice (a * b)

include hp in
/-- The two words of a `TwoSum` are nonoverlapping. -/
theorem twoSum_nonoverlapping (a b : ℝ) :
    Nonoverlapping beta (twoSumHi beta prec choice a b) (twoSumLo beta prec choice a b) :=
  round_residual_nonoverlapping beta prec hp choice (a + b)

/-- Bridge: a `Separated` pair (the ½·ulp chain) is in particular nonoverlapping. -/
theorem separated_pair_nonoverlapping {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x)
    (Hsep : Separated beta prec [x, y]) :
    Nonoverlapping beta x y := by
  simp only [Separated, SeparatedFrom, and_true] at Hsep
  rcases eq_or_ne x 0 with hx | hx
  · exact Or.inl hx
  · have hupos : 0 < ulp beta (FLX_exp prec) x := by
      rw [ulp_neq_0 beta (FLX_exp prec) hx]; exact bpow_gt_0 beta _
    apply nonoverlapping_of_abs_lt_ulp beta prec Fx
    linarith

/-! ### The 2-adic bridge: dyadic packing ⟹ sign-readable

The list-level consequence of nonoverlapping: a sorted expansion whose components
pack into disjoint dyadic ranges has `Σ|tail| < |head|`, so its sign is read off the
head (`headDom_sign`). We formalize the "packed" form directly as `DyadicSep` (each
head a multiple of `β^s` whose power exceeds the total magnitude below it), prove the
bridge to `HeadDom`, and give the **dyadic kernel** — the integer-packing lemma
`(e = m·β^t, |e| < β^s, t ≤ s) ⟹ |e| ≤ β^s − β^t` — that powers the builder. -/

/-- A nonzero multiple of `β^s` has magnitude at least `β^s`. -/
theorem multipleOfPow_le_abs {x : ℝ} {s : ℤ}
    (hx : x ≠ 0) (h : MultipleOfPow beta s x) : bpow beta s ≤ |x| := by
  obtain ⟨m, rfl⟩ := h
  have hbs : (0 : ℝ) < bpow beta s := bpow_gt_0 beta s
  have hm0 : m ≠ 0 := by rintro rfl; simp at hx
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |(m : ℝ)| := by rw [Int.cast_abs]
  rw [abs_mul, abs_of_pos hbs]
  calc bpow beta s = 1 * bpow beta s := (one_mul _).symm
    _ ≤ |(m : ℝ)| * bpow beta s := mul_le_mul_of_nonneg_right hm1 (le_of_lt hbs)

/-- **The dyadic packing kernel.** If `e` is a multiple of `β^t`, strictly below
`β^s` in magnitude, with `t ≤ s`, then `|e| ≤ β^s − β^t` — there is at least a full
`β^t` of headroom below `β^s`. (General radix; the integer mantissa `|m|` satisfies
`|m| ≤ β^(s−t) − 1`.) -/
theorem dyadic_kernel {e : ℝ} {s t : ℤ}
    (hmult : MultipleOfPow beta t e) (hlt : |e| < bpow beta s) (hts : t ≤ s) :
    |e| ≤ bpow beta s - bpow beta t := by
  obtain ⟨m, rfl⟩ := hmult
  have hbt : (0 : ℝ) < bpow beta t := bpow_gt_0 beta t
  have hst : (0 : ℤ) ≤ s - t := by omega
  have hsplit : bpow beta s = bpow beta (s - t) * bpow beta t := by
    rw [← bpow_plus]; congr 1; omega
  rw [abs_mul, abs_of_pos hbt] at hlt ⊢
  rw [hsplit] at hlt
  have hmlt : |(m : ℝ)| < bpow beta (s - t) :=
    lt_of_mul_lt_mul_right hlt (le_of_lt hbt)
  have hNeq : bpow beta (s - t) = ((beta.val ^ (s - t).toNat : ℤ) : ℝ) :=
    (IZR_Zpower beta hst).symm
  have hmInt : |m| < (beta.val ^ (s - t).toNat : ℤ) := by
    have : ((|m| : ℤ) : ℝ) < ((beta.val ^ (s - t).toNat : ℤ) : ℝ) := by
      rw [Int.cast_abs, ← hNeq]; exact hmlt
    exact_mod_cast this
  have hmle : |(m : ℝ)| ≤ bpow beta (s - t) - 1 := by
    have h1 : (|m| : ℤ) ≤ (beta.val ^ (s - t).toNat : ℤ) - 1 := by omega
    have h2 : ((|m| : ℤ) : ℝ) ≤ ((beta.val ^ (s - t).toNat : ℤ) : ℝ) - 1 := by
      push_cast at h1 ⊢; exact_mod_cast h1
    rw [Int.cast_abs] at h2; rw [hNeq]; exact h2
  calc |(m : ℝ)| * bpow beta t
      ≤ (bpow beta (s - t) - 1) * bpow beta t :=
        mul_le_mul_of_nonneg_right hmle (le_of_lt hbt)
    _ = bpow beta (s - t) * bpow beta t - bpow beta t := by ring
    _ = bpow beta s - bpow beta t := by rw [← hsplit]

/-- Dyadically packed expansion: each component is a multiple of some `β^s` whose
power strictly exceeds the total magnitude of everything below it. The "strongly
packed" form of sorted-nonoverlapping — it directly certifies sign-readability. -/
def DyadicSep : List ℝ → Prop
  | [] => True
  | h :: t =>
      (∃ s : ℤ, MultipleOfPow beta s h ∧ (t.map (fun x => |x|)).sum < bpow beta s) ∧
        DyadicSep t

/-- **The 2-adic bridge:** a dyadically-packed expansion with nonzero head dominates
its tail (`HeadDom`), so its sign is read off the head. -/
theorem dyadicSep_headDom {h : ℝ} {t : List ℝ}
    (H : DyadicSep beta (h :: t)) (hh : h ≠ 0) : HeadDom h t := by
  simp only [DyadicSep] at H
  obtain ⟨⟨s, hmult, hsum⟩, _⟩ := H
  have hle : bpow beta s ≤ |h| := multipleOfPow_le_abs beta hh hmult
  unfold HeadDom
  linarith

/-- A dyadically-packed expansion with nonzero head is sign-readable. -/
theorem dyadicSep_sign {h : ℝ} {t : List ℝ}
    (H : DyadicSep beta (h :: t)) (hh : h ≠ 0) :
    (h :: t).sum ≠ 0 ∧ (0 < (h :: t).sum ↔ 0 < h) ∧ ((h :: t).sum < 0 ↔ h < 0) :=
  headDom_sign (dyadicSep_headDom beta H hh)

include hp in
/-- **Builder (kernel-powered):** prepending a dominant head `g` (a float whose ulp
exceeds `|h|`) to a packed expansion keeps it packed — the kernel supplies exactly
the `β^cexp(g)` headroom needed to absorb `|h|` plus the rest. -/
theorem dyadicSep_cons {g h : ℝ} {t : List ℝ}
    (Fg : generic_format beta (FLX_exp prec) g) (hh : h ≠ 0)
    (hgh : |h| < ulp beta (FLX_exp prec) g)
    (Ht : DyadicSep beta (h :: t)) :
    DyadicSep beta (g :: h :: t) := by
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [ulp_FLX_0 beta prec hp] at hgh; exact absurd hgh (not_lt.mpr (abs_nonneg h))
  have hgulp : ulp beta (FLX_exp prec) g = bpow beta (cexp beta (FLX_exp prec) g) :=
    ulp_neq_0 beta (FLX_exp prec) hg0
  simp only [DyadicSep] at Ht ⊢
  obtain ⟨⟨s_h, hmult_h, hsum_t⟩, Ht'⟩ := Ht
  refine ⟨⟨cexp beta (FLX_exp prec) g, multipleOfPow_cexp beta prec Fg, ?_⟩,
    ⟨s_h, hmult_h, hsum_t⟩, Ht'⟩
  have hgh' : |h| < bpow beta (cexp beta (FLX_exp prec) g) := by rwa [hgulp] at hgh
  have hbsh : bpow beta s_h ≤ |h| := multipleOfPow_le_abs beta hh hmult_h
  have hsh_le : s_h ≤ cexp beta (FLX_exp prec) g := by
    by_contra hcon
    push_neg at hcon
    have := bpow_lt beta hcon
    linarith
  have hker : |h| ≤ bpow beta (cexp beta (FLX_exp prec) g) - bpow beta s_h :=
    dyadic_kernel beta hmult_h hgh' hsh_le
  have hsumcons : ((h :: t).map (fun x => |x|)).sum
      = |h| + (t.map (fun x => |x|)).sum := by simp [List.sum_cons]
  rw [hsumcons]
  linarith

/-- **2-element base case:** two floats with `x ≠ 0` and `|y| < ulp x` form a packed
expansion (`DyadicSep [x, y]`). -/
theorem dyadicSep_pair {x y : ℝ}
    (Fx : generic_format beta (FLX_exp prec) x) (Fy : generic_format beta (FLX_exp prec) y)
    (hx : x ≠ 0) (hxy : |y| < ulp beta (FLX_exp prec) x) :
    DyadicSep beta [x, y] := by
  have hxulp : ulp beta (FLX_exp prec) x = bpow beta (cexp beta (FLX_exp prec) x) :=
    ulp_neq_0 beta (FLX_exp prec) hx
  simp only [DyadicSep]
  refine ⟨⟨cexp beta (FLX_exp prec) x, multipleOfPow_cexp beta prec Fx, ?_⟩,
    ⟨cexp beta (FLX_exp prec) y, multipleOfPow_cexp beta prec Fy, ?_⟩, trivial⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rwa [hxulp] at hxy
  · simp only [List.map_nil, List.sum_nil]
    exact bpow_gt_0 beta _

/-! ### Toward grow-preservation (Shewchuk Theorem 10): the building blocks

Shewchuk's `GROW-EXPANSION` adds a single float `b` to a nonoverlapping expansion `e`
(sorted increasing), sweeping `Q ← TWO-SUM(Q, eᵢ)` and emitting the residuals `hᵢ`
plus the final carry. The output is nonoverlapping. His proof rests on two facts,
ported here (the inductive assembly over the list is the remaining step):

* **Lemma 1** — the round-to-nearest error of `a + b` is no larger than either
  operand (`◦(a+b)` is the closest float to `a+b`, and the float `a` is at distance
  `|b|`). So each residual `hᵢ = err(Q, eᵢ)` has `|hᵢ| ≤ |eᵢ|`.
* **Magnitude-monotonicity of nonoverlapping** — shrinking the smaller operand keeps
  it nonoverlapping with the larger. Since `|hᵢ| ≤ |eᵢ|` and `eᵢ` is
  nonoverlapping-below the later (larger) components, `hᵢ` is too — so it cannot
  overlap any later output. -/

include hp in
/-- **Lemma 1 (Shewchuk), left form:** `|◦(a+b) − (a+b)| ≤ |b|` (the float `a` is a
witness no farther than the nearest). -/
theorem roundN_add_err_le_left {a b : ℝ}
    (Fa : generic_format beta (FLX_exp prec) a) :
    |round beta (FLX_exp prec) (Znearest choice) (a + b) - (a + b)| ≤ |b| := by
  have h := (round_N_pt beta (FLX_exp prec) (FLX_exp_valid prec hp) choice (a + b)).2 a Fa
  rwa [show a - (a + b) = -b from by ring, abs_neg] at h

include hp in
/-- **Lemma 1, right form:** `|◦(a+b) − (a+b)| ≤ |a|`. -/
theorem roundN_add_err_le_right {a b : ℝ}
    (Fb : generic_format beta (FLX_exp prec) b) :
    |round beta (FLX_exp prec) (Znearest choice) (a + b) - (a + b)| ≤ |a| := by
  have h := (round_N_pt beta (FLX_exp prec) (FLX_exp_valid prec hp) choice (a + b)).2 b Fb
  rwa [show b - (a + b) = -a from by ring, abs_neg] at h

include hp in
/-- The `TwoSum` residual is no larger than the second operand (Lemma 1 applied to
`twoSumLo`). -/
theorem twoSumLo_abs_le {a b : ℝ} (Fa : generic_format beta (FLX_exp prec) a) :
    |twoSumLo beta prec choice a b| ≤ |b| := by
  unfold twoSumLo twoSumHi
  rw [show (a + b) - round beta (FLX_exp prec) (Znearest choice) (a + b)
      = -(round beta (FLX_exp prec) (Znearest choice) (a + b) - (a + b)) from by ring, abs_neg]
  exact roundN_add_err_le_left beta prec hp choice Fa

/-- Shrinking the dominated operand preserves nonoverlapping: if `w` is a multiple of
`β^s` strictly above `u`, then any `z` with `|z| ≤ |u|` is nonoverlapping with `w`. -/
theorem nonoverlapping_of_witness_le {w u z : ℝ} {s : ℤ}
    (hw : MultipleOfPow beta s w) (hu : |u| < bpow beta s) (hz : |z| ≤ |u|) :
    Nonoverlapping beta z w :=
  Or.inr (Or.inr (Or.inr ⟨s, hw, lt_of_le_of_lt hz hu⟩))

/-- From `Nonoverlapping x y` with `y` the larger (`|x| ≤ |y|`) and `x ≠ 0`, recover
the witness in which `y` is the multiple: `∃ s, MultipleOfPow s y ∧ |x| < β^s`. -/
theorem nonoverlapping_extract {x y : ℝ}
    (h : Nonoverlapping beta x y) (hx : x ≠ 0) (hxy : |x| ≤ |y|) :
    ∃ s : ℤ, MultipleOfPow beta s y ∧ |x| < bpow beta s := by
  rcases h with h | h | ⟨s, hmx, hy⟩ | ⟨s, hmy, hx'⟩
  · exact absurd h hx
  · rw [h, abs_zero] at hxy
    exact absurd (abs_eq_zero.mp (le_antisymm hxy (abs_nonneg x))) hx
  · exact absurd (multipleOfPow_le_abs beta hx hmx) (by
      have := lt_of_le_of_lt hxy hy; linarith)
  · exact ⟨s, hmy, hx'⟩

/-- **Magnitude-monotonicity:** if `x` (nonzero) is nonoverlapping with the larger `y`
and `z` is no larger than `x`, then `z` is nonoverlapping with `y`. This is the step
that carries each `TwoSum` residual's nonoverlapping past the larger components. -/
theorem nonoverlapping_shrink_left {x y z : ℝ}
    (h : Nonoverlapping beta x y) (hx : x ≠ 0) (hxy : |x| ≤ |y|) (hz : |z| ≤ |x|) :
    Nonoverlapping beta z y := by
  obtain ⟨s, hmy, hx'⟩ := nonoverlapping_extract beta h hx hxy
  exact nonoverlapping_of_witness_le beta hmy hx' hz

end

end LeanFlocq
