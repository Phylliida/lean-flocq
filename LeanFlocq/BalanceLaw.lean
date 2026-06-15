/-
Balance Law — the substantive infinite⟹finite lemma of the monotile
arena-2 programme, in abstract face-field form.

Group one rotation orbit's surface heights by face direction: `fx c,
gx c` are the +x and −x face-orbit-sums of cell c, likewise y,z. For a
complementary-matching tiling:
  • per-tile: the six face-sums add to the (rotation-invariant) orbit
    total σ, at every cell;
  • matching: `fx c + gx (c+eₓ) = 0`, and similarly y,z.
Summing the per-tile identity over an n³ box gives n³σ; every interior
face cancels by matching, leaving only the O(n²) boundary, so
n³|σ| ≤ 6Mn² and hence σ = 0.

`balance_of_faces` is the theorem; `balance_core` its arithmetic heart;
`pair_bound` the single-axis telescoping engine.
-/
import Mathlib

namespace MonotileBalance

open Finset

/-- Arithmetic heart: an integer `k` with `n³·|k| ≤ C·n²` for every `n`
(and `0 ≤ C`) is zero. -/
theorem balance_core (k C : ℤ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (n : ℤ) ^ 3 * |k| ≤ C * (n : ℤ) ^ 2) : k = 0 := by
  by_contra hk
  have hk1 : (1 : ℤ) ≤ |k| := by have := abs_pos.mpr hk; omega
  have key : ∀ n : ℕ, 1 ≤ n → (n : ℤ) ≤ C := by
    intro n hn
    have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
    have hcube : (n : ℤ) ^ 3 ≤ C * (n : ℤ) ^ 2 :=
      calc (n : ℤ) ^ 3 = (n : ℤ) ^ 3 * 1 := by ring
        _ ≤ (n : ℤ) ^ 3 * |k| := by nlinarith [pow_pos hn0 3]
        _ ≤ C * (n : ℤ) ^ 2 := h n
    have step2 : (n : ℤ) * (n : ℤ) ^ 2 ≤ C * (n : ℤ) ^ 2 := by
      have e : (n : ℤ) * (n : ℤ) ^ 2 = (n : ℤ) ^ 3 := by ring
      rw [e]; exact hcube
    exact le_of_mul_le_mul_right step2 (by positivity)
  have hbig := key (C.toNat + 1) (by omega)
  have hCnat : ((C.toNat : ℤ)) = C := Int.toNat_of_nonneg hC
  push_cast at hbig
  omega

/-- Box sum of a cell field over the n³ window. -/
def S3 (n : ℕ) (g : ℤ → ℤ → ℤ → ℤ) : ℤ :=
  ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n,
    g (i : ℤ) (j : ℤ) (k : ℤ)

/-- Reindex: swapping the first two summation axes. -/
theorem S3_swap12 (n : ℕ) (F : ℤ → ℤ → ℤ → ℤ) :
    S3 n F = S3 n (fun a b c => F b a c) := by
  unfold S3
  rw [Finset.sum_comm]

/-- Reindex: cycling axes so the third becomes first. -/
theorem S3_cyc (n : ℕ) (F : ℤ → ℤ → ℤ → ℤ) :
    S3 n F = S3 n (fun a b c => F c a b) := by
  unfold S3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- Reindex with the other 3-cycle (first axis ← third position), which
is what the z-face matching needs. -/
theorem S3_cyc2 (n : ℕ) (F : ℤ → ℤ → ℤ → ℤ) :
    S3 n F = S3 n (fun a b c => F b c a) := by
  rw [S3_cyc n F, S3_cyc n (fun a b c => F c a b)]

section
variable (M : ℤ)

/-- **Single-axis telescoping engine.** If `f a b c + g (a+1) b c = 0`
(matching across the first axis) and `|g| ≤ M`, the box sum of the
first-axis face pair is bounded by the O(n²) boundary. -/
theorem pair_bound (f g : ℤ → ℤ → ℤ → ℤ) (n : ℕ)
    (hmatch : ∀ a b c : ℤ, f a b c + g (a + 1) b c = 0)
    (hbound : ∀ a b c : ℤ, |g a b c| ≤ M) :
    |S3 n f + S3 n g| ≤ 2 * M * (n : ℤ) ^ 2 := by
  set H : ℕ → ℤ :=
    fun m => ∑ j ∈ range n, ∑ k ∈ range n, g (m : ℤ) (j : ℤ) (k : ℤ)
    with hHdef
  have step : S3 n f + S3 n g = ∑ i ∈ range n, (H i - H (i + 1)) := by
    unfold S3
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hHi : H i =
        ∑ j ∈ range n, ∑ k ∈ range n, g (i : ℤ) (j : ℤ) (k : ℤ) := rfl
    have hHi1 : H (i + 1) =
        ∑ j ∈ range n, ∑ k ∈ range n, g ((i : ℤ) + 1) (j : ℤ) (k : ℤ) := by
      simp only [hHdef, Nat.cast_add, Nat.cast_one]
    rw [hHi, hHi1, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have := hmatch (i : ℤ) (j : ℤ) (k : ℤ)
    omega
  rw [step, Finset.sum_range_sub' H n]
  have hHbound : ∀ m : ℕ, |H m| ≤ M * (n : ℤ) ^ 2 := by
    intro m
    calc |H m| ≤ ∑ j ∈ range n, |∑ k ∈ range n, g (m:ℤ) (j:ℤ) (k:ℤ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range n, ∑ k ∈ range n, |g (m:ℤ) (j:ℤ) (k:ℤ)| := by
          apply Finset.sum_le_sum; intro j _
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range n, ∑ k ∈ range n, M := by
          apply Finset.sum_le_sum; intro j _
          apply Finset.sum_le_sum; intro k _; exact hbound _ _ _
      _ = M * (n : ℤ) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  obtain ⟨l0, r0⟩ := abs_le.mp (hHbound 0)
  obtain ⟨ln, rn⟩ := abs_le.mp (hHbound n)
  rw [abs_le]; constructor <;> linarith

end

section
variable (σ M : ℤ)
variable (fx gx fy gy fz gz : ℤ → ℤ → ℤ → ℤ)

structure FaceData : Prop where
  cell : ∀ a b c : ℤ,
    fx a b c + gx a b c + fy a b c + gy a b c + fz a b c + gz a b c = σ
  matchx : ∀ a b c : ℤ, fx a b c + gx (a + 1) b c = 0
  matchy : ∀ a b c : ℤ, fy a b c + gy a (b + 1) c = 0
  matchz : ∀ a b c : ℤ, fz a b c + gz a b (c + 1) = 0
  bx : ∀ a b c : ℤ, |gx a b c| ≤ M
  by' : ∀ a b c : ℤ, |gy a b c| ≤ M
  bz : ∀ a b c : ℤ, |gz a b c| ≤ M

variable {σ M fx gx fy gy fz gz}

theorem balance_of_faces (hd : FaceData σ M fx gx fy gy fz gz) :
    σ = 0 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hd.bx 0 0 0)
  apply balance_core σ (6 * M) (by positivity)
  intro n
  -- the box sum of the constant cell field is n³σ
  have hconst : S3 n (fun _ _ _ => σ) = (n : ℤ) ^ 3 * σ := by
    unfold S3
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hfield : (fun a b c => fx a b c + gx a b c + fy a b c +
      gy a b c + fz a b c + gz a b c) = (fun _ _ _ => σ) := by
    funext a b c; exact hd.cell a b c
  -- split the field's box sum into the six face box sums
  have hsplit : S3 n (fun a b c => fx a b c + gx a b c + fy a b c +
      gy a b c + fz a b c + gz a b c)
      = S3 n fx + S3 n gx + S3 n fy + S3 n gy + S3 n fz + S3 n gz := by
    simp only [S3, Finset.sum_add_distrib]
  have hsum : (n : ℤ) ^ 3 * σ =
      (S3 n fx + S3 n gx) + (S3 n fy + S3 n gy) + (S3 n fz + S3 n gz) := by
    have h1 : S3 n (fun _ _ _ => σ) =
        S3 n fx + S3 n gx + S3 n fy + S3 n gy + S3 n fz + S3 n gz := by
      rw [← hfield]; exact hsplit
    rw [← hconst, h1]; ring
  -- bound each axis pair via the telescoping engine
  have tx : |S3 n fx + S3 n gx| ≤ 2 * M * (n : ℤ) ^ 2 :=
    pair_bound M fx gx n hd.matchx hd.bx
  have ty : |S3 n fy + S3 n gy| ≤ 2 * M * (n : ℤ) ^ 2 := by
    rw [S3_swap12 n fy, S3_swap12 n gy]
    exact pair_bound M _ _ n (fun a b c => hd.matchy b a c)
      (fun a b c => hd.by' b a c)
  have tz : |S3 n fz + S3 n gz| ≤ 2 * M * (n : ℤ) ^ 2 := by
    rw [S3_cyc2 n fz, S3_cyc2 n gz]
    exact pair_bound M _ _ n (fun a b c => hd.matchz b c a)
      (fun a b c => hd.bz b c a)
  obtain ⟨lx, rx⟩ := abs_le.mp tx
  obtain ⟨ly, ry⟩ := abs_le.mp ty
  obtain ⟨lz, rz⟩ := abs_le.mp tz
  have habs : (n : ℤ) ^ 3 * |σ| = |(n : ℤ) ^ 3 * σ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (n:ℤ) ^ 3)]
  rw [habs, hsum, abs_le]
  constructor <;> linarith

end

end MonotileBalance

#print axioms MonotileBalance.balance_of_faces
