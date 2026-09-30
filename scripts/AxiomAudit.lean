import StringDiagrams
-- Modules built by the library glob but not imported by the root module.
import StringDiagrams.Examples.RenderDemo
import StringDiagrams.Render.Basic
import StringDiagrams.Tactic.Test
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Axiom audit for the whole library. Run from the package directory:

    lake env lean -DwarningAsError=true scripts/AxiomAudit.lean

Declarations are audited by owning module, not by namespace: this includes private declarations,
compiler-generated auxiliaries, and declarations placed in foreign namespaces (e.g. `CategoryTheory`).
The only allowed transitive axioms are `propext`, `Classical.choice` and `Quot.sound`; in particular
`sorryAx` and the `Lean.ofReduceBool` axiom used by `native_decide` are rejected. -/
set_option maxHeartbeats 80000000 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let modules := moduleNames.filter (fun n => n.getRoot == `StringDiagrams)
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  let mut foreignCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := moduleNames[idx.toNat]!
      if owner.getRoot == `StringDiagrams then
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name} (module {owner})"
        count := count + 1
        if name.getRoot == `_private then
          privateCount := privateCount + 1
        else if name.getRoot != `StringDiagrams then
          foreignCount := foreignCount + 1
  if count == 0 then
    throwError "No StringDiagrams declarations were imported"
  logInfo m!"Audited {count} declarations owned by {modules.size} StringDiagrams modules; {privateCount} private and {foreignCount} non-StringDiagrams-namespace declarations included. All transitive axioms are allowed."
