-- Based on InitGrindLint.lean
import Lean.Parser.Tactic

open Lean.Parser.Tactic

syntax (name := grindAttrLintCheck) "#grind_attr_lint" ppSpace "check" configItem* ident (ppSpace "in" (ppSpace &"module")? ident+)? : command
syntax (name := grindAttrLintInspect) "#grind_attr_lint" ppSpace "inspect" configItem* ident+ ppSpace "under" ppSpace ident: command
