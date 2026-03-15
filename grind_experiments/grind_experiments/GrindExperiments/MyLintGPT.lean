import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.TryThis
import GrindExperiments.MyInitGrindLint

namespace Lean.Elab.Tactic.Grind
open Command Meta Grind
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












def myResolveGrindAttrs (ids : Array (TSyntax `ident)) : TermElabM (Array Lean.Meta.Grind.Extension) := do
  let mut seen : NameSet := {}
  let mut exts : Array Lean.Meta.Grind.Extension := #[]
  for id in ids do
    let attrName := id.getId
    let some ext := (← Grind.getExtension? attrName) | throwError "unknown `grind` attribute `{attrName}`"
    unless seen.contains attrName do
      seen := seen.insert attrName
      exts := exts.push ext
  return exts

def myMkParamsForAttrs (config : Grind.Config) (exts : Array Lean.Meta.Grind.Extension) : MetaM Params := do
  let norm ← Grind.getSimpContext config
  let normProcs ← Grind.getSimprocs
  let symPrios ← Grind.getGlobalSymbolPriorities
  let muted := myMuteExt.getState (← getEnv)
  let mut extensions : Array Grind.ExtensionState := #[]
  for ext in exts do
    let mut s := ext.getState (← getEnv)
    let mut ematch := s.ematch
    for declName in muted do
      try
        ematch ← ematch.eraseDecl declName
      catch _ =>
        pure ()
    extensions := extensions.push { s with ematch := ematch }
  return { config, extensions, norm, normProcs, symPrios }

def myFilterByPrefixInModule
    (declName : Name) (prefixes? : Option (Array Name)) (inModule : Bool) : CoreM Bool := do
  let some prefixes := prefixes? | return true
  let env ← getEnv
  if inModule then
    let some modIdx := env.getModuleIdxFor? declName | return false
    let modName := env.header.moduleNames[modIdx]!
    return prefixes.any (fun pre => pre.isPrefixOf modName)
  else
    return prefixes.any fun pre =>
      if pre == `_root_ then
        declName.components.length == 1
      else
        pre.isPrefixOf declName

def myGetTheoremsFromAttrs
    (exts : Array Lean.Meta.Grind.Extension)
    (prefixes? : Option (Array Name))
    (inModule : Bool) : CoreM (Array Name) := do
  let skip := mySkipExt.getState (← getEnv)
  let skipSuffixes := mySkipSuffixExt.getState (← getEnv)
  let mut seen : NameSet := {}
  let mut names : Array Name := #[]
  for ext in exts do
    let origins := (← ext.getEMatchTheorems).getOrigins
    for origin in origins do
      match origin with
      | .decl declName =>
        unless seen.contains declName do
          unless skip.contains declName || skipSuffixes.any (fun suff => nameEndsWithSuffix declName suff) do
            if ← myFilterByPrefixInModule declName prefixes? inModule then
              seen := seen.insert declName
              names := names.push declName
      | _ => pure ()
  return names

-- NOTE: your existing file already has #[command_elab Lean.Grind.grindAttrLintCheck] below this name.
-- If you want this to be the active elaborator, replace that elaborator definition with this one.
@[command_elab Lean.Grind.grindAttrLintCheck]
def myElabGrindAttrLintCheckCore : CommandElab := fun stx => liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
  let `(#grind_attr_lint check $[$items:configItem]* $[$attrs:ident]* $[in $[module%$m?]? $prefixes?:ident*]?) := stx | throwUnsupportedSyntax
  let config ← mkConfig items
  let attrExts ← myResolveGrindAttrs attrs.getElems
  let params ← myMkParamsForAttrs config attrExts
  let prefixes? : Option (Array Name) := prefixes?.map (·.map (·.getId))
  let inModule := m? matches some (some _)

  let decls ← myGetTheoremsFromAttrs attrExts prefixes? inModule
  let decls := decls.toArray.qsort Name.lt

  let mut problematicTheorems := #[]
  for declName in decls do
    try
      if (← analyzeEMatchTheorem declName params) then
        problematicTheorems := problematicTheorems.push declName
    catch e =>
      logError m!"{declName} failed with {e.toMessageData}"

  if !problematicTheorems.isEmpty then
    logInfo m!"#grind_attr_lint check reported {problematicTheorems.size} potentially noisy theorem(s)."
    for declName in problematicTheorems do
      logInfo m!"  {declName}"
end Lean.Elab.Tactic.Grind
