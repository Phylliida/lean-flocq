/-
# M3 (fast lane): the census enumeration, machine-friendly encoding

Same enumeration as `AnyK3DCensus.lean`, restructured for native speed:
gains coded 0..15 (code = τ*2 + sign) with multiplication/inverse TABLES
computed in Lean from the M2 definitions (`gmulT`/`ginvT` — nothing
imported); subgroups as 16-bit masks; gain tuples as base-16 digit
extraction from a counter (no per-tuple allocation); per-class relevant
equations precomputed; Array.qsort + fold dedup.

The cross-check is the same: `census_count_fast` must independently
produce 1,445,865. The encode/decode bridge lemmas (`gmulT_correct` etc.)
connect this file to the M2 algebra for the M3b membership proofs.
-/
import Mathlib
import LeanFlocq.AnyK3DGain

set_option maxRecDepth 100000

namespace AnyK3D

/-! ## Encoded gain arithmetic (tables computed from M2's definitions) -/

def encG (w : Gain) : ℕ := w.1.val * 2 + (if w.2 then 1 else 0)

def decG (n : ℕ) : Gain := (⟨n / 2 % 8, Nat.mod_lt _ (by norm_num)⟩,
                            n % 2 = 1)

def gmulT : Array ℕ :=
  ((List.range 256).map fun n =>
    encG (gmul (decG (n / 16)) (decG (n % 16)))).toArray

def ginvT : Array ℕ :=
  ((List.range 16).map fun n => encG (ginv (decG n))).toArray

def gmul16 (a b : ℕ) : ℕ := gmulT.getD (a * 16 + b) 0

def ginv16 (a : ℕ) : ℕ := ginvT.getD a 0

/-- Encoded negative gain of twist code t: (τ_t, true) = t*2+1. -/
def negTau (t : ℕ) : ℕ := t * 2 + 1

/-! ## Subgroups as 16-bit masks -/

def maskHasAll (H : ℕ) (f : ℕ → ℕ → Bool) : Bool :=
  (List.range 16).all fun a =>
    !H.testBit a || (List.range 16).all fun b => !H.testBit b || f a b

def isSubgroupM (H : ℕ) : Bool :=
  H.testBit 0 &&
  maskHasAll H (fun a b => H.testBit (gmul16 a b)) &&
  (List.range 16).all fun a => !H.testBit a || H.testBit (ginv16 a)

/-- Even-feasibility: no (id,−), (swap-diag,−) — codes 1, 9, 15. -/
def feasibleM (H : ℕ) : Bool :=
  !H.testBit 1 && !H.testBit 9 && !H.testBit 15

def subMasks : Array ℕ :=
  ((List.range 65536).filter fun H => isSubgroupM H && feasibleM H).toArray

/-! ## Per-class profile enumeration -/

/-- Relevant equations of a class: (bit index, member position of faceA,
member position of faceB, twist code). -/
def relEqs (members : List ℕ) : Array (ℕ × ℕ × ℕ × ℕ) :=
  (((List.range 84).filterMap fun i =>
    match members.idxOf? (eqFaceA.getD i 0), members.idxOf? (eqFaceB.getD i 0) with
    | some ja, some jb => some (i, ja, jb, eqTau.getD i 0)
    | _, _ => none)).toArray

/-- Gain of member position j under tuple counter `idx` (position 0 = root,
gain code 0). -/
def gainAt (idx j : ℕ) : ℕ := if j = 0 then 0 else idx / 16 ^ (j - 1) % 16

def classMask (re : Array (ℕ × ℕ × ℕ × ℕ)) (idx H : ℕ) : ℕ :=
  re.foldl
    (fun acc e =>
      let (i, ja, jb, t) := e
      if H.testBit (gmul16 (ginv16 (gainAt idx ja))
          (gmul16 (negTau t) (gainAt idx jb))) then
        acc ||| (1 <<< i)
      else acc) 0

/-- Sort + dedup. mergeSort (csimp-tail-recursive, has `mem_mergeSort`)
rather than qsort (no membership lemmas) — M3b's membership chain needs
`x ∈ a → x ∈ dedupSorted a`. -/
def dedupSorted (a : Array ℕ) : Array ℕ :=
  (a.toList.mergeSort (· ≤ ·)).foldl (fun acc x =>
    if acc.back? = some x then acc else acc.push x) #[]

def classOptionsFast (members : List ℕ) : Array ℕ :=
  let re := relEqs members
  let n := 16 ^ (members.length - 1)
  dedupSorted <| subMasks.foldl (fun acc H =>
    (List.range n).foldl (fun acc idx => acc.push (classMask re idx H)) acc)
    #[]

/-! ## Partitions and the union-combination -/

def partitionsN : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | x :: rest =>
    (partitionsN rest).flatMap fun part =>
      ([x] :: part) ::
        (List.range part.length).map fun i =>
          part.set i (x :: part.getD i [])

def censusFast : Array ℕ :=
  let parts := partitionsN [0, 1, 2, 3, 4, 5]
  dedupSorted <| parts.foldl (fun acc part =>
    let combos := part.foldl
      (fun accList cls =>
        let opts := classOptionsFast cls
        accList.flatMap fun m => (opts.map fun o => m ||| o).toList)
      [0]
    combos.foldl (fun a m => a.push m) acc) #[]

/-! ## Cross-checks -/

/-- Cross-check vs Python (countclosures: 35 subgroups, 18 feasible). -/
theorem subMasks_count : subMasks.size = 18 := by
  native_decide

theorem census_count_fast : censusFast.size = 1445865 := by
  native_decide

end AnyK3D
