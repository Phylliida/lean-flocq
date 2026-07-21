/-
# M4-C3: the empty-certificate CNF layer

The encoding for the 3,405 maximal-empty frontier masks' emptiness
certificates (DESIGN-anyk3d-endgame.md §C3): one-hot orientation vars per
box cell + per-axis binary compat clauses, plus the phase-bit extension
(aux vars encoding the 5 low bits of each cell's orientation) used by the
34 cube-and-conquer stragglers. Variable numbering matches the Python
(`monotile/arena2.py` `box_solver_cnf` + `cube_strag34.py`):

    xVar ci o      = ci*24 + o              (DIMACS: +1)
    bVar nc ci k   = nc*24 + ci*5 + k       (DIMACS: +1)

`encode_complete` (a Box3OK box tiling's assignment satisfies the CNF) is
ported from the SatReflect probe proofs — one-hot + binary-compat only,
the easy instance; `empty_sound` chains it with `box3OK_of_tiling`: CNF
UNSAT ⟹ no space tiling. The UNSAT facts themselves come from the cert
campaign (in-Lean verifyCert for the 3,371 cheap masks, cake_lpr
streaming for the 34).
-/
import Mathlib
import Std.Sat.CNF.Basic
import LeanFlocq.AnyK3DCerts

open Std.Sat Std.Sat.CNF

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## Variables and clauses -/

/-- One-hot var: orientation `o` at cell `ci` (0-based; DIMACS +1). -/
def xVar (ci o : ℕ) : ℕ := ci * 24 + o

/-- Phase-bit var: bit `k` of cell `ci`'s orientation code. -/
def bVar (nc ci k : ℕ) : ℕ := nc * 24 + ci * 5 + k

/-- Cell `ci` gets at least one orientation. -/
def atLeastOne3 (ci : ℕ) : Clause Nat :=
  (List.range 24).map fun o => (xVar ci o, true)

/-- Cell `ci` gets at most one orientation. -/
def atMostOne3 (ci : ℕ) : CNF Nat :=
  (List.range 24).flatMap fun o1 =>
    (List.range 24).filterMap fun o2 =>
      if o1 < o2 then some [(xVar ci o1, false), (xVar ci o2, false)]
      else none

/-- Forbid disallowed orientation pairs on the edge (ci, axF, nci). -/
def compatCls3 (m ci nci : ℕ) (axF : Fin 3) : CNF Nat :=
  (List.finRange 24).flatMap fun o1 =>
    (List.finRange 24).filterMap fun o2 =>
      if relOfMask m axF o1 o2 then none
      else some [(xVar ci o1.val, false), (xVar nci o2.val, false)]

/-- Phase-bit definitions: the one-hot var forces the bits of the
orientation code (matches cube_strag34's aux extension). -/
def phaseCls3 (nc ci : ℕ) : CNF Nat :=
  (List.finRange 24).flatMap fun o =>
    (List.range 5).map fun k =>
      [(xVar ci o.val, false), (bVar nc ci k, o.val.testBit k)]

/-- Neighbor of cell `ci` in the +ax direction, as a cell index
(x-major: ci = x*(h*d) + y*d + z). -/
def neighborOf (w h d ci ax : ℕ) : Option ℕ :=
  let x := ci / (h * d)
  let y := ci / d % h
  let z := ci % d
  match ax with
  | 0 => if x + 1 < w then some ((x + 1) * (h * d) + y * d + z) else none
  | 1 => if y + 1 < h then some (x * (h * d) + (y + 1) * d + z) else none
  | _ => if z + 1 < d then some (x * (h * d) + y * d + (z + 1)) else none

/-- The empty-certificate CNF: one-hot everywhere + compat on interior
edges. -/
def emptyCNF (m w h d : ℕ) : CNF Nat :=
  ((List.range (w * h * d)).map atLeastOne3) ++
  ((List.range (w * h * d)).flatMap atMostOne3) ++
  ((List.range (w * h * d)).flatMap fun ci =>
    (List.finRange 3).flatMap fun axF =>
      match neighborOf w h d ci axF.val with
      | none => []
      | some nci => compatCls3 m ci nci axF)

/-- The phase-bit extension (the 34 stragglers' cube-and-conquer). -/
def emptyCNFX (m w h d : ℕ) : CNF Nat :=
  emptyCNF m w h d ++ (List.range (w * h * d)).flatMap (phaseCls3 (w * h * d))

/-! ## The assignment -/

/-- The assignment decoding a box tiling. -/
def assign3 {w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (v : ℕ) : Bool :=
  if h1 : v < w * h * d * 24 then
    have h2 : v / 24 / (h * d) < w := by
      have hd' : 0 < h * d := Nat.mul_pos hh hd
      have hci : v / 24 < w * h * d := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 24)]
        exact h1
      rw [Nat.div_lt_iff_lt_mul hd']
      calc v / 24 < w * h * d := hci
        _ = w * (h * d) := by ring
    f ⟨v / 24 / (h * d), h2⟩ ⟨v / 24 / d % h, Nat.mod_lt _ hh⟩
      ⟨v / 24 % d, Nat.mod_lt _ hd⟩ == ⟨v % 24, Nat.mod_lt _ (by norm_num)⟩
  else if h1 : v < w * h * d * 24 + w * h * d * 5 then
    have h2 : (v - w * h * d * 24) / 5 / (h * d) < w := by
      have hd' : 0 < h * d := Nat.mul_pos hh hd
      have hci : (v - w * h * d * 24) / 5 < w * h * d := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 5)]
        omega
      rw [Nat.div_lt_iff_lt_mul hd']
      calc (v - w * h * d * 24) / 5 < w * h * d := hci
        _ = w * (h * d) := by ring
    (f ⟨(v - w * h * d * 24) / 5 / (h * d), h2⟩
       ⟨(v - w * h * d * 24) / 5 / d % h, Nat.mod_lt _ hh⟩
       ⟨(v - w * h * d * 24) / 5 % d, Nat.mod_lt _ hd⟩).val.testBit
      ((v - w * h * d * 24) % 5)
  else false

/-- The div bound a cell index always satisfies (factored out: every
statement that names the cell Fin's needs it). -/
theorem cell_div_lt {w h d : ℕ} (hh : 0 < h) (hd : 0 < d) {ci : ℕ}
    (hci : ci < w * h * d) : ci / (h * d) < w := by
  have hd' : 0 < h * d := Nat.mul_pos hh hd
  rw [Nat.div_lt_iff_lt_mul hd']
  calc ci < w * h * d := hci
    _ = w * (h * d) := by ring

/-- X round-trip: `assign3` at `xVar ci o` says "the box tiling puts o at
cell ci". -/
theorem assign3_xVar {w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (ci o : ℕ)
    (hci : ci < w * h * d) (ho : o < 24) :
    assign3 hh hd f (xVar ci o) =
      (f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
        ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩ == ⟨o, ho⟩) := by
  unfold assign3 xVar
  have h1 : ci * 24 + o < w * h * d * 24 := by omega
  rw [dif_pos h1]
  simp only [show (ci * 24 + o) / 24 = ci by omega,
    show (ci * 24 + o) % 24 = o by omega]

/-- B round-trip: `assign3` at `bVar` is the orientation's bit. -/
theorem assign3_bVar {w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (ci k : ℕ)
    (hci : ci < w * h * d) (hk : k < 5) :
    assign3 hh hd f (bVar (w * h * d) ci k) =
      (f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
        ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩).val.testBit k := by
  unfold assign3 bVar
  have h1 : ¬ (w * h * d * 24 + ci * 5 + k < w * h * d * 24) := by omega
  have h2 : w * h * d * 24 + ci * 5 + k < w * h * d * 24 + w * h * d * 5 := by
    omega
  rw [dif_neg h1, dif_pos h2]
  simp only [show (w * h * d * 24 + ci * 5 + k - w * h * d * 24) / 5 = ci by omega,
    show (w * h * d * 24 + ci * 5 + k - w * h * d * 24) % 5 = k by omega]

/-! ## Neighbor coordinates -/

/-- The neighbor's coordinates and bounds, per axis. -/
theorem neighborOf_coords {w h d : ℕ} (hh : 0 < h) (hd : 0 < d) (ci nci : ℕ)
    (hci : ci < w * h * d) (ax : ℕ) (hax : ax < 3)
    (hn : neighborOf w h d ci ax = some nci) :
    nci < w * h * d ∧
    ((ax = 0 ∧ nci / (h * d) = ci / (h * d) + 1 ∧ nci / d % h = ci / d % h ∧
        nci % d = ci % d ∧ ci / (h * d) + 1 < w) ∨
     (ax = 1 ∧ nci / (h * d) = ci / (h * d) ∧ nci / d % h = ci / d % h + 1 ∧
        nci % d = ci % d ∧ ci / d % h + 1 < h) ∨
     (ax = 2 ∧ nci / (h * d) = ci / (h * d) ∧ nci / d % h = ci / d % h ∧
        nci % d = ci % d + 1 ∧ ci % d + 1 < d)) := by
  have hd' : 0 < h * d := Nat.mul_pos hh hd
  have hx : ci / (h * d) < w := cell_div_lt hh hd hci
  have hy : ci / d % h < h := Nat.mod_lt _ hh
  have hz : ci % d < d := Nat.mod_lt _ hd
  have hyd : (ci / d % h + 1) * d ≤ h * d :=
    Nat.mul_le_mul (Nat.succ_le_of_lt hy) (le_refl d)
  have hyz : ci / d % h * d + ci % d < h * d := by
    have h1 : ci / d % h * d + d ≤ h * d := by
      calc ci / d % h * d + d = (ci / d % h + 1) * d := by ring
        _ ≤ h * d := hyd
    omega
  rcases ax with _ | _ | _ | _
  · unfold neighborOf at hn
    simp only [] at hn
    split at hn
    · rename_i hxw
      simp only [Option.some.injEq] at hn
      subst hn
      have heq1 : (ci / (h * d) + 1) * (h * d) + ci / d % h * d + ci % d
          = ci / d % h * d + ci % d + (h * d) * (ci / (h * d) + 1) := by ring
      have hrw := Nat.add_mul_div_left (ci / d % h * d + ci % d)
        (ci / (h * d) + 1) hd'
      rw [Nat.div_eq_of_lt hyz, Nat.zero_add] at hrw
      have heq2 : (ci / (h * d) + 1) * (h * d) + ci / d % h * d + ci % d
          = ci % d + d * ((ci / (h * d) + 1) * h + ci / d % h) := by ring
      have hrd := Nat.add_mul_div_left (ci % d)
        ((ci / (h * d) + 1) * h + ci / d % h) hd
      rw [Nat.div_eq_of_lt hz, Nat.zero_add] at hrd
      have heq3 : (ci / (h * d) + 1) * h + ci / d % h
          = ci / d % h + h * (ci / (h * d) + 1) := by ring
      refine ⟨?_, Or.inl ⟨rfl, ?_, ?_, ?_, hxw⟩⟩
      · have hb : (ci / (h * d) + 2) * (h * d) ≤ w * (h * d) :=
          Nat.mul_le_mul (Nat.succ_le_of_lt hxw) (le_refl _)
        calc (ci / (h * d) + 1) * (h * d) + ci / d % h * d + ci % d
            < (ci / (h * d) + 1) * (h * d) + (h * d) := by omega
          _ = (ci / (h * d) + 2) * (h * d) := by ring
          _ ≤ w * (h * d) := hb
          _ = w * h * d := by ring
      · rw [heq1, hrw]
      · rw [heq2, hrd, heq3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
      · rw [heq2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz]
    · simp at hn
  · unfold neighborOf at hn
    simp only [] at hn
    split at hn
    · rename_i hyh
      simp only [Option.some.injEq] at hn
      subst hn
      have hyz' : (ci / d % h + 1) * d + ci % d < h * d := by
        have h1 : (ci / d % h + 2) * d ≤ h * d :=
          Nat.mul_le_mul (Nat.succ_le_of_lt hyh) (le_refl d)
        have h2 : (ci / d % h + 1) * d + d ≤ h * d := by
          calc (ci / d % h + 1) * d + d = (ci / d % h + 2) * d := by ring
            _ ≤ h * d := h1
        omega
      have heq1 : ci / (h * d) * (h * d) + (ci / d % h + 1) * d + ci % d
          = (ci / d % h + 1) * d + ci % d + (h * d) * (ci / (h * d)) := by ring
      have hrw := Nat.add_mul_div_left ((ci / d % h + 1) * d + ci % d)
        (ci / (h * d)) hd'
      rw [Nat.div_eq_of_lt hyz', Nat.zero_add] at hrw
      have heq2 : ci / (h * d) * (h * d) + (ci / d % h + 1) * d + ci % d
          = ci % d + d * (ci / (h * d) * h + (ci / d % h + 1)) := by ring
      have hrd := Nat.add_mul_div_left (ci % d)
        (ci / (h * d) * h + (ci / d % h + 1)) hd
      rw [Nat.div_eq_of_lt hz, Nat.zero_add] at hrd
      have heq3 : ci / (h * d) * h + (ci / d % h + 1)
          = (ci / d % h + 1) + h * (ci / (h * d)) := by ring
      refine ⟨?_, Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_, hyh⟩)⟩
      · have hb : (ci / (h * d) + 1) * (h * d) ≤ w * (h * d) :=
          Nat.mul_le_mul (Nat.succ_le_of_lt hx) (le_refl _)
        calc ci / (h * d) * (h * d) + (ci / d % h + 1) * d + ci % d
            < ci / (h * d) * (h * d) + (h * d) := by omega
          _ = (ci / (h * d) + 1) * (h * d) := by ring
          _ ≤ w * (h * d) := hb
          _ = w * h * d := by ring
      · rw [heq1, hrw]
      · rw [heq2, hrd, heq3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hyh]
      · rw [heq2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz]
    · simp at hn
  · unfold neighborOf at hn
    simp only [] at hn
    split at hn
    · rename_i hzd
      simp only [Option.some.injEq] at hn
      subst hn
      have hyz'' : ci / d % h * d + (ci % d + 1) < h * d := by
        have h1 : ci / d % h * d + d ≤ h * d := by
          calc ci / d % h * d + d = (ci / d % h + 1) * d := by ring
            _ ≤ h * d := hyd
        omega
      have heq1 : ci / (h * d) * (h * d) + ci / d % h * d + (ci % d + 1)
          = ci / d % h * d + (ci % d + 1) + (h * d) * (ci / (h * d)) := by ring
      have hrw := Nat.add_mul_div_left (ci / d % h * d + (ci % d + 1))
        (ci / (h * d)) hd'
      rw [Nat.div_eq_of_lt hyz'', Nat.zero_add] at hrw
      have heq2 : ci / (h * d) * (h * d) + ci / d % h * d + (ci % d + 1)
          = (ci % d + 1) + d * (ci / (h * d) * h + ci / d % h) := by ring
      have hrd := Nat.add_mul_div_left (ci % d + 1)
        (ci / (h * d) * h + ci / d % h) hd
      rw [Nat.div_eq_of_lt hzd, Nat.zero_add] at hrd
      have heq3 : ci / (h * d) * h + ci / d % h
          = ci / d % h + h * (ci / (h * d)) := by ring
      refine ⟨?_, Or.inr (Or.inr ⟨rfl, ?_, ?_, ?_, hzd⟩)⟩
      · have hb : (ci / (h * d) + 1) * (h * d) ≤ w * (h * d) :=
          Nat.mul_le_mul (Nat.succ_le_of_lt hx) (le_refl _)
        calc ci / (h * d) * (h * d) + ci / d % h * d + (ci % d + 1)
            < ci / (h * d) * (h * d) + (h * d) := by omega
          _ = (ci / (h * d) + 1) * (h * d) := by ring
          _ ≤ w * (h * d) := hb
          _ = w * h * d := by ring
      · rw [heq1, hrw]
      · rw [heq2, hrd, heq3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
      · rw [heq2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzd]
    · simp at hn
  · omega

/-! ## Per-family satisfaction -/

theorem atLeastOne3_sat {w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (ci : ℕ) (hci : ci < w * h * d) :
    Clause.eval (assign3 hh hd f) (atLeastOne3 ci) = true := by
  unfold atLeastOne3 Clause.eval
  rw [List.any_eq_true]
  refine ⟨(xVar ci (f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
        ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩).val, true),
    List.mem_map.mpr ⟨_, List.mem_range.mpr (f _ _ _).isLt, rfl⟩, ?_⟩
  show (assign3 hh hd f (xVar ci (f _ _ _).val) == true) = true
  simp only [assign3_xVar hh hd f ci _ hci (f _ _ _).isLt, Fin.eta,
    beq_self_eq_true']

theorem atMostOne3_sat {w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (ci : ℕ) (hci : ci < w * h * d) :
    (atMostOne3 ci).all (Clause.eval (assign3 hh hd f)) = true := by
  rw [List.all_eq_true]
  intro c hc
  unfold atMostOne3 at hc
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap] at hc
  obtain ⟨o1, ho1, o2, ho2, hc⟩ := hc
  split at hc
  · rename_i hlt
    simp only [Option.some.injEq] at hc
    subst hc
    unfold Clause.eval
    rw [List.any_eq_true]
    have hne : f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
          ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩
        ≠ (⟨o1, ho1⟩ : Fin 24) ∨
        f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
          ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩
        ≠ ⟨o2, ho2⟩ := by
      by_contra hcon
      push_neg at hcon
      have he : (⟨o1, ho1⟩ : Fin 24) = ⟨o2, ho2⟩ := hcon.1 ▸ hcon.2
      have hv := congrArg Fin.val he
      simp only [] at hv
      omega
    rcases hne with hne | hne
    · refine ⟨(xVar ci o1, false), by simp, ?_⟩
      show (assign3 hh hd f (xVar ci o1) == false) = true
      rw [assign3_xVar hh hd f ci o1 hci ho1, beq_eq_false_iff_ne.mpr hne]
      rfl
    · refine ⟨(xVar ci o2, false), by simp, ?_⟩
      show (assign3 hh hd f (xVar ci o2) == false) = true
      rw [assign3_xVar hh hd f ci o2 hci ho2, beq_eq_false_iff_ne.mpr hne]
      rfl
  · simp at hc

theorem compatCls3_sat {m w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (hbox : Box3OK (relOfMask m) f)
    (ci nci : ℕ) (hci : ci < w * h * d) (axF : Fin 3)
    (hn : neighborOf w h d ci axF.val = some nci) :
    (compatCls3 m ci nci axF).all (Clause.eval (assign3 hh hd f)) = true := by
  obtain ⟨hnci, hspec⟩ := neighborOf_coords hh hd ci nci hci axF.val axF.isLt hn
  rw [List.all_eq_true]
  intro c hc
  unfold compatCls3 at hc
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_filterMap,
    true_and] at hc
  obtain ⟨o1, o2, hc⟩ := hc
  split at hc
  · simp at hc
  · rename_i hrel
    simp only [Option.some.injEq] at hc
    subst hc
    -- the relation holds across the edge, by Box3OK + the coordinate bridge
    have key : relOfMask m axF
        (f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
          ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩)
        (f ⟨nci / (h * d), cell_div_lt hh hd hnci⟩
          ⟨nci / d % h, Nat.mod_lt _ hh⟩ ⟨nci % d, Nat.mod_lt _ hd⟩) = true := by
      rcases hspec with ⟨h0, e1, e2, e3, hw⟩ | ⟨h1, e1, e2, e3, hw⟩ |
        ⟨h2, e1, e2, e3, hw⟩
      · have hax : axF = (0 : Fin 3) := Fin.ext h0
        subst hax
        have hR := hbox.1 ⟨ci / (h * d), cell_div_lt hh hd hci⟩
          ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩ hw
        rw [show (⟨nci / (h * d), cell_div_lt hh hd hnci⟩ : Fin w) =
              ⟨ci / (h * d) + 1, hw⟩ from Fin.ext e1,
          show (⟨nci / d % h, Nat.mod_lt _ hh⟩ : Fin h) =
            ⟨ci / d % h, Nat.mod_lt _ hh⟩ from Fin.ext e2,
          show (⟨nci % d, Nat.mod_lt _ hd⟩ : Fin d) =
            ⟨ci % d, Nat.mod_lt _ hd⟩ from Fin.ext e3]
        exact hR
      · have hax : axF = (1 : Fin 3) := Fin.ext h1
        subst hax
        have hR := hbox.2.1 ⟨ci / (h * d), cell_div_lt hh hd hci⟩
          ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩ hw
        rw [show (⟨nci / (h * d), cell_div_lt hh hd hnci⟩ : Fin w) =
              ⟨ci / (h * d), cell_div_lt hh hd hci⟩ from Fin.ext e1,
          show (⟨nci / d % h, Nat.mod_lt _ hh⟩ : Fin h) =
            ⟨ci / d % h + 1, hw⟩ from Fin.ext e2,
          show (⟨nci % d, Nat.mod_lt _ hd⟩ : Fin d) =
            ⟨ci % d, Nat.mod_lt _ hd⟩ from Fin.ext e3]
        exact hR
      · have hax : axF = (2 : Fin 3) := Fin.ext h2
        subst hax
        have hR := hbox.2.2 ⟨ci / (h * d), cell_div_lt hh hd hci⟩
          ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩ hw
        rw [show (⟨nci / (h * d), cell_div_lt hh hd hnci⟩ : Fin w) =
              ⟨ci / (h * d), cell_div_lt hh hd hci⟩ from Fin.ext e1,
          show (⟨nci / d % h, Nat.mod_lt _ hh⟩ : Fin h) =
            ⟨ci / d % h, Nat.mod_lt _ hh⟩ from Fin.ext e2,
          show (⟨nci % d, Nat.mod_lt _ hd⟩ : Fin d) =
            ⟨ci % d + 1, hw⟩ from Fin.ext e3]
        exact hR
    unfold Clause.eval
    rw [List.any_eq_true]
    by_cases ho1 : f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
        ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩ = o1
    · by_cases ho2 : f ⟨nci / (h * d), cell_div_lt hh hd hnci⟩
        ⟨nci / d % h, Nat.mod_lt _ hh⟩ ⟨nci % d, Nat.mod_lt _ hd⟩ = o2
      · rw [ho1, ho2] at key
        exact (hrel key).elim
      · refine ⟨(xVar nci o2.val, false), by simp, ?_⟩
        show (assign3 hh hd f (xVar nci o2.val) == false) = true
        rw [assign3_xVar hh hd f nci o2.val hnci o2.isLt, Fin.eta,
          beq_eq_false_iff_ne.mpr ho2]
        rfl
    · refine ⟨(xVar ci o1.val, false), by simp, ?_⟩
      show (assign3 hh hd f (xVar ci o1.val) == false) = true
      rw [assign3_xVar hh hd f ci o1.val hci o1.isLt, Fin.eta,
        beq_eq_false_iff_ne.mpr ho1]
      rfl

theorem phaseCls3_sat {w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (ci : ℕ) (hci : ci < w * h * d) :
    (phaseCls3 (w * h * d) ci).all (Clause.eval (assign3 hh hd f)) = true := by
  rw [List.all_eq_true]
  intro c hc
  unfold phaseCls3 at hc
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, List.mem_range,
    true_and] at hc
  obtain ⟨o, k, hk, rfl⟩ := hc
  unfold Clause.eval
  rw [List.any_eq_true]
  by_cases ho : f ⟨ci / (h * d), cell_div_lt hh hd hci⟩
      ⟨ci / d % h, Nat.mod_lt _ hh⟩ ⟨ci % d, Nat.mod_lt _ hd⟩ = o
  · refine ⟨(bVar (w * h * d) ci k, o.val.testBit k), by simp, ?_⟩
    show (assign3 hh hd f (bVar (w * h * d) ci k) == o.val.testBit k) = true
    rw [assign3_bVar hh hd f ci k hci hk, ho]
    exact beq_self_eq_true' (o.val.testBit k)
  · refine ⟨(xVar ci o.val, false), by simp, ?_⟩
    show (assign3 hh hd f (xVar ci o.val) == false) = true
    rw [assign3_xVar hh hd f ci o.val hci o.isLt, Fin.eta,
      beq_eq_false_iff_ne.mpr ho]
    rfl

/-! ## encode_complete and soundness -/

/-- **encode_complete**: a box tiling's assignment satisfies the
empty-certificate CNF. -/
theorem emptyCNF_complete {m w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (hbox : Box3OK (relOfMask m) f) :
    CNF.eval (assign3 hh hd f) (emptyCNF m w h d) = true := by
  rw [CNF.eval, List.all_eq_true]
  intro c hc
  simp only [emptyCNF, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_range, List.mem_finRange, true_and] at hc
  rcases hc with (⟨ci, hci, rfl⟩ | ⟨ci, hci, hc⟩) | ⟨ci, hci, axF, hc⟩
  · exact atLeastOne3_sat hh hd f ci hci
  · exact (List.all_eq_true.mp (atMostOne3_sat hh hd f ci hci)) c hc
  · cases hn : neighborOf w h d ci axF.val with
    | none =>
      simp only [hn] at hc
      simp at hc
    | some nci =>
      simp only [hn] at hc
      exact (List.all_eq_true.mp
        (compatCls3_sat hh hd f hbox ci nci hci axF hn)) c hc

/-- **encode_complete, phase-extended.** -/
theorem emptyCNFX_complete {m w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (f : Fin w → Fin h → Fin d → Fin 24) (hbox : Box3OK (relOfMask m) f) :
    CNF.eval (assign3 hh hd f) (emptyCNFX m w h d) = true := by
  rw [emptyCNFX, CNF.eval_append, emptyCNF_complete hh hd f hbox,
    Bool.true_and]
  rw [CNF.eval, List.all_eq_true]
  intro c hc
  simp only [List.mem_flatMap, List.mem_range] at hc
  obtain ⟨ci, hci, hc⟩ := hc
  exact (List.all_eq_true.mp (phaseCls3_sat hh hd f ci hci)) c hc

/-- **Empty soundness**: CNF UNSAT rules out a space tiling. -/
theorem empty_sound {m w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hunsat : CNF.Unsat (emptyCNF m w h d)) :
    ¬ ∃ ω, IsTiling (relOfMask m) ω := by
  rintro ⟨ω, hω⟩
  have hbox := box3OK_of_tiling hω w h d
  have hsat := emptyCNF_complete hh hd _ hbox
  rw [hunsat] at hsat
  exact absurd hsat (by decide)

/-- **Empty soundness, phase-extended.** -/
theorem emptyX_sound {m w h d : ℕ} (hh : 0 < h) (hd : 0 < d)
    (hunsat : CNF.Unsat (emptyCNFX m w h d)) :
    ¬ ∃ ω, IsTiling (relOfMask m) ω := by
  rintro ⟨ω, hω⟩
  have hbox := box3OK_of_tiling hω w h d
  have hsat := emptyCNFX_complete hh hd _ hbox
  rw [hunsat] at hsat
  exact absurd hsat (by decide)

end AnyK3D
