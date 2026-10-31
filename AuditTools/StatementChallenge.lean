module
import all Challenge
public import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isProject := fun n : Name =>
    match env.getModuleIdxFor? n with
    | some i =>
        let m := env.header.moduleNames[i]!.toString
        m.startsWith "AffineFK." || m == "Solution" || m == "Challenge"
    | none => n.toString.startsWith "AffineFK." || n.toString.startsWith "AffineFKProof."
  let target := ``AffineFK.affine_reverse_faber_krahn_principal_results
  let main ← getConstInfo target
  let mainRow := Json.mkObj [("name", toJson target.toString),
    ("level_params", toJson (main.levelParams.map Name.toString)),
    ("type_hash", toJson s!"{hash main.type}")]
  liftIO (IO.println ("COMPILED_MAIN_JSON: " ++ mainRow.compress))
  let mut pending := main.type.getUsedConstants.toList.filter
    (fun n => isProject n)
  let mut seen : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n then
      seen := seen.push n
      let c ← getConstInfo n
      let (kind, value) := match c with
        | .defnInfo v => ("definition", v.value)
        | .thmInfo v => ("theorem", v.value)
        | _ => ("unexpected", c.type)
      if kind == "unexpected" then
        throwError "Unexpected ordinary project dependency kind: {n}"
      let safety := match c with
        | .defnInfo v => reprStr v.safety
        | _ => "theorem"
      if c.isUnsafe || c.isPartial then
        throwError "Unsafe or partial project dependency: {n}"
      let refs := (c.type.getUsedConstants ++ value.getUsedConstants).toList.filter
        (fun name => isProject name)
      let row := Json.mkObj [("name", toJson n.toString), ("kind", toJson kind),
        ("level_params", toJson (c.levelParams.map Name.toString)),
        ("safety", toJson safety), ("is_unsafe", toJson c.isUnsafe),
        ("is_partial", toJson c.isPartial), ("type_hash", toJson s!"{hash c.type}"),
        ("value_hash", toJson s!"{hash value}"),
        ("project_constants", toJson (refs.map Name.toString))]
      liftIO (IO.println ("COMPILED_CONSTANT_JSON: " ++ row.compress))
      pending := refs ++ pending
  liftIO (IO.println s!"COMPILED_ORDINARY_COUNT: {seen.size}")

-- The selected Challenge theorem is an unproved specification.
