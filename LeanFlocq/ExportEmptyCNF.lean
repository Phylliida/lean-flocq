/-
# DIMACS exporter for the M4-C3 empty certificates

Usage: lake env lean LeanFlocq/ExportEmptyCNF.lean -- <mask> <w> <h> <d> <x> <out>

  <mask>  decimal 84-bit relation mask
  <w><h><d> box dims
  <x>     0 = emptyCNF (the 3,371 cheap masks), 1 = emptyCNFX
          (phase-bit extension, the 34 stragglers)

Vars are 0-based in Lean (xVar ci o = ci*24+o, bVar nc ci k = nc*24+ci*5+k);
DIMACS is 1-based, so the export shifts every literal by +1 — matching
monotile/cube_strag34.py's phase-bit literals exactly.
-/
import LeanFlocq.AnyK3DEmptyEnc

open AnyK3D

def exportOne (m w h d x : ℕ) (out : String) : IO Unit := do
  let cnf := if x == 1 then emptyCNFX m w h d else emptyCNF m w h d
  let nvars := if x == 1 then w * h * d * 29 else w * h * d * 24
  let fh ← IO.FS.Handle.mk out IO.FS.Mode.write
  fh.putStrLn s!"p cnf {nvars} {cnf.length}"
  for c in cnf do
    let lits := c.map fun (v, pol) =>
      if pol then s!"{v + 1}" else s!"-{v + 1}"
    fh.putStrLn (String.intercalate " " lits ++ " 0")

def main (args : List String) : IO Unit := do
  match args with
  | ["batch", jobsFile] => do
    let contents ← IO.FS.readFile jobsFile
    for line in contents.splitOn "\n" do
      let ws := line.splitOn " " |>.filter (· != "")
      if ws.length == 6 then
        let [ms, ws', hs, ds, xs, out] := ws
          | throw (IO.userError s!"bad job line: {line}")
        let some m := ms.toNat? | throw (IO.userError "bad mask")
        let some w := ws'.toNat? | throw (IO.userError "bad w")
        let some h := hs.toNat? | throw (IO.userError "bad h")
        let some d := ds.toNat? | throw (IO.userError "bad d")
        let some x := xs.toNat? | throw (IO.userError "bad x")
        exportOne m w h d x out
  | [ms, ws, hs, ds, xs, out] => do
    let some m := ms.toNat? | throw (IO.userError "bad mask")
    let some w := ws.toNat? | throw (IO.userError "bad w")
    let some h := hs.toNat? | throw (IO.userError "bad h")
    let some d := ds.toNat? | throw (IO.userError "bad d")
    let some x := xs.toNat? | throw (IO.userError "bad x")
    exportOne m w h d x out
  | _ => throw (IO.userError "usage: mask w h d x out  |  batch jobs.txt")
