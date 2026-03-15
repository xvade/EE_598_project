import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.TryThis
import GrindExperiments.TacticExperimentation.InitAttrPrinter
import Lean.Meta.Tactic.Grind.Attr

open Lean.Elab.Command
open Lean.Elab
open Lean



@[command_elab printAttr]
def myElabGrindAttrLintCheckCore : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let `(#print_attr $[$attrs:ident]*) := stx | throwUnsupportedSyntax


  -- let attrNames := attrs.getElems.map Syntax.getId
  let attrNames : Array Name := attrs.map (·.getId)

  logInfo m!"Parsed {attrNames.size} attr arg(s):"
  for attrName in attrNames do
    match ← Lean.Meta.Grind.getExtension? attrName with
    | some _ => logInfo m!"  • {attrName} (known grind attr)"
    | none   => logInfo m!"  • {attrName} (unknown / not a registered grind attr)"
  -- let config ← mkConfig items
  -- let attrExts ← myResolveGrindAttrs attrs.getElems
  -- let params ← myMkParamsForAttrs config attrExts
  -- let prefixes? : Option (Array Name) := prefixes?.map (·.map (·.getId))
  -- let inModule := m? matches some (some _)

  -- let decls ← myGetTheoremsFromAttrs attrExts prefixes? inModule
  -- let decls := decls.toArray.qsort Name.lt

  -- let mut problematicTheorems := #[]
  -- for declName in decls do
  --   try
  --     if (← analyzeEMatchTheorem declName params) then
  --       problematicTheorems := problematicTheorems.push declName
  --   catch e =>
  --     logError m!"{declName} failed with {e.toMessageData}"

  -- if !problematicTheorems.isEmpty then
  --   logInfo m!"#grind_attr_lint check reported {problematicTheorems.size} potentially noisy theorem(s)."
  --   for declName in problematicTheorems do
  --     logInfo m!"  {declName}"
