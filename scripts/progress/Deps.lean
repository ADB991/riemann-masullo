import Lean
open Lean

/-!
Prints one JSON object per line for every constant of the given modules: its kind, module,
source range, docstring, and the constants of those same modules that occur in its type and
in its body. `scripts/progress/build.py` turns this into the dependency graph of the progress
page; run that, not this file.

    lake env lean --run scripts/progress/Deps.lean RiemannMasullo.AppA_AlgebraicNT.Sec1 ...

`importModules` is called at its default level (`OLeanLevel.private`), which loads the
`.olean.private` parts as well, so the proof terms of theorems are available even though the
library uses the module system. Dependencies are therefore read from the elaborated terms,
not guessed from the source text.

Fields: `n` name, `k` kind, `m` module, `mi` position of the module in import order (a module
comes after everything it imports), `t` project constants in the type, `v` project
constants in the body (definitions and theorems), `s` whether the body mentions `sorryAx`
directly, `r` declaration range `[line, col, endLine, endCol]` (lines from 1, columns from 0,
in codepoints), `sel` start of the name `[line, col]`, `doc` docstring, `of` the inductive type
of a constructor or recursor.
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
  let moduleOf (name : Name) : Option (Name × Nat) := do
    let idx ← env.getModuleIdxFor? name
    let m := env.header.moduleNames[idx.toNat]!
    if wanted.contains m then some (m, idx.toNat) else none
  let project (e : Expr) : Array String :=
    (e.getUsedConstants.filter (moduleOf · |>.isSome)).map toString |>.qsort (· < ·)
  let out ← IO.getStdout
  for (name, info) in env.constants.toList do
    let some (m, mi) := moduleOf name | continue
    let value? : Option Expr := match info with
      | .defnInfo d => some d.value
      | .thmInfo t => some t.value
      | .opaqueInfo o => some o.value
      | _ => none
    let mut fields : List (String × Json) := [
      ("n", toJson (toString name)), ("k", toJson (kindOf info)), ("m", toJson (toString m)),
      ("mi", toJson mi),
      ("t", toJson (project info.type))]
    if let some v := value? then
      fields := fields ++ [("v", toJson (project v)),
        ("s", toJson (v.getUsedConstants.contains ``sorryAx))]
    match info with
    | .ctorInfo c => fields := fields ++ [("of", toJson (toString c.induct))]
    | .recInfo r => fields := fields ++ [("of", toJson (toString (r.all.headD .anonymous)))]
    | _ => pure ()
    let ranges? := declRangeExt.find? (level := .exported) env name <|>
      declRangeExt.find? (level := .server) env name
    if let some rs := ranges? then
      fields := fields ++ [
        ("r", toJson #[rs.range.pos.line, rs.range.pos.column,
          rs.range.endPos.line, rs.range.endPos.column]),
        ("sel", toJson #[rs.selectionRange.pos.line, rs.selectionRange.pos.column])]
    let doc? := docStringExt.find? (level := .exported) env name <|>
      docStringExt.find? (level := .server) env name
    if let some doc := doc? then
      fields := fields ++ [("doc", toJson doc)]
    out.putStrLn (Json.mkObj fields).compress
  return 0
