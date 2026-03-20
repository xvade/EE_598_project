import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.TryThis
import GrindExperiments.TacticExperimentation.PrintAttr.InitAttrPrinter
import Lean.Meta.Tactic.Grind.Attr

open Lean.Elab.Command
open Lean.Elab
open Lean
open Lean.Meta


def resolveGrindAttrs (ids : Array (TSyntax `ident)) : TermElabM (Array Lean.Meta.Grind.Extension) := do
  let mut seen : NameSet := {}
  let mut exts : Array Grind.Extension := #[]
  for id in ids do
    let attrName := id.getId
    let some ext := (← Lean.Meta.Grind.getExtension? attrName) | throwError "unknown `grind` attribute `{attrName}`"
    unless seen.contains attrName do
      seen := seen.insert attrName
      exts := exts.push ext
  return exts


@[command_elab printAttr]
def printAttrCore : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let `(#print_attr $[$attrs:ident]*) := stx | throwUnsupportedSyntax
  let attrNames : Array Name := attrs.map (·.getId)

  logInfo m!"Parsed {attrNames.size} attr arg(s):"
  for attrName in attrNames do
    match ← Lean.Meta.Grind.getExtension? attrName with
    | some _ => logInfo m!"  • {attrName} (known grind attr)"
    | none   => logInfo m!"  • {attrName} (unknown / not a registered grind attr)"
