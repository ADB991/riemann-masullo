import Lean
open Lean

/-!
Prints one line per declaration of the given modules: its kind, its name, a hash of its type
and, for definitions, a hash of its body, followed by `SORRY` if that body contains `sorry`. Comparing the output for two versions of the project
shows whether a change altered the statement of anything that already existed.

    lake env lean --run scripts/Signatures.lean RiemannMasullo.AppA_AlgebraicNT.Sec1 ...

Use `scripts/signatures.sh`, which builds first and passes every module of the library.
-/

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules := args.toArray.map (·.toName)
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024)
  let wanted : Std.HashSet Name := Std.HashSet.ofArray modules
  let mut lines : Array String := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless wanted.contains env.header.moduleNames[idx.toNat]! do continue
    if name.isInternalDetail then continue
    -- A definition is marked when `sorry` occurs in its own body, including in a proof field.
    let body := match info with
      | .defnInfo d =>
        s!" {d.value.hash}" ++ (if d.value.getUsedConstants.contains ``sorryAx then " SORRY" else "")
      | _ => ""
    lines := lines.push s!"{kindOf info} {name} {info.type.hash}{body}"
  for line in lines.qsort (· < ·) do
    IO.println line
  return 0
