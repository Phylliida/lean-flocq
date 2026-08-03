/-
# Color M3 (fast lane): the equal-color census enumeration

The equal-color analogue of `AnyK3DCensusFast.lean`. Same enumeration
shape, with the 8-element gain group (grid isometries only, signs +1):
gains coded 0..7 (the `Fin 8` value itself) with multiplication/inverse
TABLES computed in Lean from the color M2 definitions (`gmulT8`/`ginvT8`
— nothing imported); subgroups as 8-bit masks (ALL of them — every
subgroup of the color gain group is exact-stabilizer feasible, verified
by brute-force witnesses on K = 2,3,4 grids:
`monotile/check_color_subgroups.py`, missing = 0); gain tuples as base-8
digit extraction from a counter; the shared `relEqs`/`partitionsN`/
`dedupSorted` machinery.

The held-bit formula is the bump/dent `classMask` with the sign stripped:
equation (i, ja, jb, t) is held iff
`gmul8 (ginv8 (gainAt8 idx ja)) (gmul8 t (gainAt8 idx jb)) ∈ H`
— the twist code `t` used directly (no `negTau`).

The cross-checks: `subMasksC_count` (10 subgroups — matches the Python
feasibility probe) and `census_count_fastC`, which must independently
reproduce the Python color census count 9,341,248
(`monotile/color_census.py` → `color3d_profiles.json`).
-/
import Mathlib
import LeanFlocq.AnyK3DColorGain
import LeanFlocq.AnyK3DCensusFast

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## Encoded gain arithmetic (tables computed from color M2) -/

/-- Code of a color gain: the `Fin 8` value itself. -/
def encG8 (w : Fin 8) : ℕ := w.val

def decG8 (n : ℕ) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by norm_num)⟩

def gmulT8 : Array ℕ :=
  ((List.range 64).map fun n =>
    encG8 (cmul (decG8 (n / 8)) (decG8 (n % 8)))).toArray

def ginvT8 : Array ℕ :=
  ((List.range 8).map fun n => encG8 (cinv (decG8 n))).toArray

def gmul8 (a b : ℕ) : ℕ := gmulT8.getD (a * 8 + b) 0

def ginv8 (a : ℕ) : ℕ := ginvT8.getD a 0

/-! ## Subgroups as 8-bit masks -/

def maskHasAll8 (H : ℕ) (f : ℕ → ℕ → Bool) : Bool :=
  (List.range 8).all fun a =>
    !H.testBit a || (List.range 8).all fun b => !H.testBit b || f a b

def isSubgroupM8 (H : ℕ) : Bool :=
  H.testBit 0 &&
  maskHasAll8 H (fun a b => H.testBit (gmul8 a b)) &&
  (List.range 8).all fun a => !H.testBit a || H.testBit (ginv8 a)

/-- All 10 subgroups of the color gain group (no feasibility filter —
every subgroup is exact-stabilizer realizable). -/
def subMasksC : Array ℕ :=
  ((List.range 256).filter fun H => isSubgroupM8 H).toArray

/-! ## Per-class profile enumeration -/

/-- Gain of member position j under tuple counter `idx` (position 0 =
root, gain code 0). -/
def gainAt8 (idx j : ℕ) : ℕ := if j = 0 then 0 else idx / 8 ^ (j - 1) % 8

/-- Profile mask of one class: bit i of equation (i, ja, jb, t) set iff
the combined gain lands in H — the color coset formula. -/
def classMaskC (re : Array (ℕ × ℕ × ℕ × ℕ)) (idx H : ℕ) : ℕ :=
  re.foldl
    (fun acc e =>
      let (i, ja, jb, t) := e
      if H.testBit (gmul8 (ginv8 (gainAt8 idx ja))
          (gmul8 t (gainAt8 idx jb))) then
        acc ||| (1 <<< i)
      else acc) 0

/-- All profile masks a single class (member set) can induce. -/
def classOptionsFastC (members : List ℕ) : Array ℕ :=
  let re := relEqs members
  let n := 8 ^ (members.length - 1)
  dedupSorted <| subMasksC.foldl (fun acc H =>
    (List.range n).foldl (fun acc idx => acc.push (classMaskC re idx H)) acc)
    #[]

/-! ## The union-combination census -/

def censusFastC : Array ℕ :=
  let parts := partitionsN [0, 1, 2, 3, 4, 5]
  dedupSorted <| parts.foldl (fun acc part =>
    let combos := part.foldl
      (fun accList cls =>
        let opts := classOptionsFastC cls
        accList.flatMap fun m => (opts.map fun o => m ||| o).toList)
      [0]
    combos.foldl (fun a m => a.push m) acc) #[]

/-! ## Cross-checks

The count cross-checks live in `AnyK3DColorCensusCount.lean` (a separate
module so downstream proof modules don't rebuild behind the heavy
`native_decide`s). -/

end AnyK3D
