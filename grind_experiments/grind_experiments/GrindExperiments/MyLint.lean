-- module
-- prelude
-- public import Lean.Elab.Command
import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.TryThis
import GrindExperiments.MyInitGrindLint
namespace Lean.Elab.Tactic.Grind

initialize mySkipExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

initialize mySkipSuffixExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

initialize myMuteExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

open Command Meta Grind

def checkEMatchTheorem (declName : Name) : CoreM Unit := do
  unless (← Grind.grindExt.isEMatchTheorem declName) do
    throwError "`{declName}` is not marked with the `@[grind]` attribute for theorem instantiation"


/--
Default configuration for `#grind_lint`.
-/
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

def mkParams (config : Grind.Config) : MetaM Params := do
  let params ← Meta.Grind.mkDefaultParams config
  let mut ematch := params.extensions[0]!.ematch
  for declName in myMuteExt.getState (← getEnv) do
    try
      ematch ← ematch.eraseDecl declName
    catch _ =>
      pure () -- Ignore failures here.
  return { params with extensions[0].ematch := ematch }

/-- Returns the total number of generated instances.  -/
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

/--
Analyzes theorem `declName`. That is, creates the artificial goal based on `declName` type,
and invokes `grind` on it.
Returns `true` if the number of instances is above the minimal threshold.
-/
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

/-- Check if the last component of `name` ends with the string form of `suff`. -/
def nameEndsWithSuffix (name suff : Name) : Bool :=
  match name with
  | .str _ s => s.endsWith suff.toString
  | _ => false

def getTheorems (prefixes? : Option (Array Name)) (inModule : Bool) : CoreM (List Name) := do
  let skip := mySkipExt.getState (← getEnv)
  let skipSuffixes := mySkipSuffixExt.getState (← getEnv)
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

@[command_elab Lean.Grind.grindAttrLintCheck]
def myElabGrindLintCheck : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  Tactic.TryThis.addSuggestion stx { suggestion := .string "hello" }
  let `(#grind_attr_lint check $[$items:configItem]* $[in $[module%$m?]? $ids?:ident*]?) := stx | throwUnsupportedSyntax
  let config ← mkConfig items
  let params ← mkParams config
  let prefixes? := ids?.map (·.map (·.getId))
  let inModule := m? matches some (some _)
  let decls ← getTheorems prefixes? inModule
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

end Lean.Elab.Tactic.Grind
