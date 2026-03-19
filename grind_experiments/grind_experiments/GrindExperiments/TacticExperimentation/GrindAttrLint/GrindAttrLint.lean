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


-- def myResolveGrindAttrs (attrNames : Array Name) : TermElabM (Array Lean.Meta.Grind.Extension) := do
--   let mut seen : NameSet := {}
--   let mut exts : Array Grind.Extension := #[]
--   for attrName in attrNames do
--     let some ext := (← Lean.Meta.Grind.getExtension? attrName) | throwError "unknown `grind` attribute `{attrName}`"
--     unless seen.contains attrName do
--       seen := seen.insert attrName
--       exts := exts.push ext
--   return exts


initialize skipExt : SimplePersistentEnvExtension Name NameSet ←
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

initialize skipSuffixExt : SimplePersistentEnvExtension Name NameSet ←
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

initialize muteExt : SimplePersistentEnvExtension Name NameSet ←
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

def nameEndsWithSuffix (name suff : Name) : Bool :=
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  match name with
  | .str _ s => s.endsWith suff.toString
  | _ => false

def getTheorems (prefixes? : Option (Array Name)) (inModule : Bool) : CoreM (List Name) := do
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  let skip := skipExt.getState (← getEnv)
  let skipSuffixes := skipSuffixExt.getState (← getEnv)
  let origins := (← Grind.grindExt.getEMatchTheorems).getOrigins
  let env ← getEnv
  return origins.filterMap fun origin => Id.run do
    let .decl declName := origin | return none
    if skip.contains declName then return none
    -- Check if declName's last component ends with any of the skip suffixes
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
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  elabConfigItems defaultConfig items

def mkAttrParams (config : Grind.Config) (attrExt : Extension) : MetaM Params := do
  -- Coppied with modification from mkParams in Lean.Elab.Tactic.Grind.Lint
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
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  let mut r := 0
  for (_, c) in cs do
    r := r + c
  return r

def thmsToMessageData (thms : PHashMap Grind.Origin Nat) : MetaM MessageData := do
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
  let data := thms.toArray.filterMap fun (origin, c) =>
    match origin with
    | .decl declName => some (declName, c)
    | _ => none
  let data := data.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then Name.lt d₁ d₂ else c₁ > c₂
  let data ← data.mapM fun (declName, counter) =>
    return .trace { cls := `thm } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
  return .trace { cls := `thm } "instances" data

def analyzeEMatchTheorem (declName : Name) (params : Params) : MetaM Bool := do
  -- Coppied from Lean.Elab.Tactic.Grind.Lint
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
  -- Coppied with modification from Lean.Elab.Tactic.Grind.Lint
  let `(#grind_attr_lint inspect $[$items:configItem]* $ids:ident* under $attr:ident) := stx | throwUnsupportedSyntax
  let config ← mkConfig items
  match (← Lean.Meta.Grind.getExtension? attr.getId) with
    | some ext =>
      let attrExt := ext
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
  let `(#grind_attr_lint check $[$attrs:ident]*) := stx | throwUnsupportedSyntax
  -- let attrNames := attrs.getElems.map Syntax.getId
  let attrNames : Array Name := attrs.map (·.getId)
  -- let mut thms : Array
  let thmNames := #[]
  -- logInfo m!"{resolved[0]!}"
  logInfo m!"Parsing {attrNames.size} attr arg(s):"
  for attrName in attrNames do
    match ← Lean.Meta.Grind.getExtension? attrName with
    | some ext =>
      logInfo m!"  • {attrName} (known grind attr)"
      let origins := (← ext.getEMatchTheorems).getOrigins
      for origin in origins do
        match origin with
        | .decl declName => logInfo m!"Found a .decl associated with {attrName}: {declName}"
        | .local _ => throwError "Not ready for origin originating from {attrName} to be made with .local"
        | .stx _ _ => throwError "Not ready for origin originating from {attrName} to be made with .stx"
        | .fvar _ => throwError "Not ready for origin originating from {attrName} to be made with .fvar"

    | none   => throwError "unknown grind attribute {attrName}"

  logInfo m!"Parsing {thmNames.size} theorem(s):"
  for thmName in thmNames do
    logInfo m!"{thmName}"
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
