import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Elab.Tactic.Grind.Config
import Lean.Meta.Tactic.TryThis
import GrindExperiments.TacticExperimentation.GrindAttrLint.InitGrindAttrLint
import Lean.Meta.Tactic.Grind.Attr
import Lean.Elab.Tactic.Grind

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
