/-
This file is based on Lean.Elab.Tactic.Grind.Lint.
-/

import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.TryThis
import GrindExperiments.TacticExperimentation.GrindAttrLint.InitGrindAttrLint
import Lean.Meta.Tactic.Grind.Attr
import Lean.Elab.Tactic.Grind
import Lean.Elab.Tactic.Grind.Main


open Lean.Meta.Grind
open Lean.Elab.Tactic.Grind
open Lean.Elab.Command
open Lean.Elab
open Lean
open Lean.Meta

initialize skipExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

initialize skipSuffixExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

initialize muteExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

def nameEndsWithSuffix (name suff : Name) : Bool :=
  match name with
  | .str _ s => s.endsWith suff.toString
  | _ => false

def getAttrTheorems (attrExt : Extension) (prefixes? : Option (Array Name)) (inModule : Bool) : CoreM (List Name) := do
  let skip := skipExt.getState (← getEnv)
  let skipSuffixes := skipSuffixExt.getState (← getEnv)
  let origins := (← attrExt.getEMatchTheorems).getOrigins
  let env ← getEnv
  return origins.filterMap fun origin => Id.run do
    let .decl declName := origin | return none
    if skip.contains declName then return none
    if skipSuffixes.any fun suff => nameEndsWithSuffix declName suff then return none
    let some prefixes := prefixes? | return some declName
    if inModule then
      let some modIdx := env.getModuleIdxFor? declName | return none
      let modName := env.header.moduleNames[modIdx]!
      if prefixes.any fun pre => pre.isPrefixOf modName then
        return some declName
      else
        return none
    else
      let keep := prefixes.any fun pre =>
        if pre == `_root_ then
          declName.components.length == 1
        else
          pre.isPrefixOf declName
      unless keep do return none
      return some declName

def defaultConfig : Grind.Config := {
  splits       := 0
  lookahead    := false
  mbtc         := false
  ematch       := 20
  instances    := 100
  gen          := 10
  min          := 10
  detailed     := 50
}

def mkConfig (items : Array (TSyntax `Lean.Parser.Tactic.configItem)) : TermElabM Grind.Config := do
  elabConfigItems defaultConfig items

def mkAttrParams (config : Grind.Config) (attrExt : Extension) : MetaM Params := do
  let env ← getEnv
  let params ← Meta.Grind.mkParams config #[attrExt.getState env]
  let mut ematch := params.extensions[0]!.ematch
  for declName in muteExt.getState (← getEnv) do
    try
      ematch ← ematch.eraseDecl declName
    catch _ =>
      pure () -- Ignore failures here.
  return { params with extensions[0].ematch := ematch }

def sum (cs : PHashMap Grind.Origin Nat) : Nat := Id.run do
  let mut r := 0
  for (_, c) in cs do
    r := r + c
  return r

def thmsToMessageData (thms : PHashMap Grind.Origin Nat) : MetaM MessageData := do
  let data := thms.toArray.filterMap fun (origin, c) =>
    match origin with
    | .decl declName => some (declName, c)
    | _ => none
  let data := data.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then Name.lt d₁ d₂ else c₁ > c₂
  let data ← data.mapM fun (declName, counter) =>
    return .trace { cls := `thm } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
  return .trace { cls := `thm } "instances" data

def analyzeEMatchTheorem (declName : Name) (params : Params) : MetaM Bool := do
  let info ← getConstInfo declName
  let mvarId ← forallTelescope info.type fun _ type => do
    withLocalDeclD `h type fun _ => do
      return (← mkFreshExprMVar (mkConst ``False)).mvarId!
  let result ← Grind.main mvarId params
  let thms := result.counters.thm
  let s := sum thms
  if s > params.config.min then
    if s >= params.config.instances then
      logInfo m!"instantiating `{declName}` triggers more than {s} additional `grind` theorem instantiations"
    else
      logInfo m!"instantiating `{declName}` triggers {s} additional `grind` theorem instantiations"
  if s > params.config.detailed then
    logInfo m!"{declName}\n{← thmsToMessageData thms}"
  return s > params.config.min


@[command_elab grindAttrLintInspect]
def elabGrindAttrLintInspectCore : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let `(#grind_attr_lint inspect $[$items:configItem]* $ids:ident* under $attr:ident) := stx | throwUnsupportedSyntax
  let config ← mkConfig items
  match (← Lean.Meta.Grind.getExtension? attr.getId) with
    | some attrExt =>
      let params ← mkAttrParams config attrExt
      let mut addCodeAction := false
      for id in ids do
        let declName ← realizeGlobalConstNoOverloadWithInfo id
        if (← analyzeEMatchTheorem declName params) then
          addCodeAction := true
      if addCodeAction then
        unless (← getOptions).getBool `trace.grind.ematch.instance do
          let s ← `(command|
            set_option trace.grind.ematch.instance true in
            $(⟨stx⟩):command)
          Tactic.TryThis.addSuggestion (header := "Try this to display the actual theorem instances:") stx { suggestion := .tsyntax s }
    | none   => throwError "unknown grind attribute {attr.getId}"


@[command_elab grindAttrLintCheck]
def elabGrindAttrLintCheckCore : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let `(#grind_attr_lint check $[$items:configItem]* $attr:ident $[in $[module%$m?]? $ids?:ident*]?) := stx | throwUnsupportedSyntax
  let config ← mkConfig items
  match (← Lean.Meta.Grind.getExtension? attr.getId) with
    | some attrExt =>
      let params ← mkAttrParams config attrExt
      let prefixes? := ids?.map (·.map (·.getId))
      let inModule := m? matches some (some _)
      let decls ← getAttrTheorems attrExt prefixes? inModule
      let decls := decls.toArray.qsort Name.lt
      let mut problematicTheorems := #[]
      for declName in decls do
        try
          if (← analyzeEMatchTheorem declName params) then
            problematicTheorems := problematicTheorems.push declName
        catch e =>
          logError m!"{declName} failed with {e.toMessageData}"
      if !problematicTheorems.isEmpty then
        -- Build the "Try this:" suggestion
        let checkCmd ← PrettyPrinter.ppCategory `command stx
        let mut suggestion := Format.pretty checkCmd
        suggestion := suggestion ++ "\n"
        for declName in problematicTheorems do
          suggestion := suggestion ++ s!"#grind_lint inspect {declName}\n"
        Tactic.TryThis.addSuggestion stx { suggestion := .string suggestion }
    | none => throwError "unknown grind attribute {attr.getId}"
