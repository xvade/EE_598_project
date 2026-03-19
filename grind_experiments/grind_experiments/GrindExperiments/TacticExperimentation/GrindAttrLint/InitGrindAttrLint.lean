-- Based on InitGrindLint.lean
import Lean.Parser.Tactic

open Lean.Parser.Tactic

syntax (name := grindAttrLintCheck) "#grind_attr_lint" ppSpace "check" (ppSpace ident)+ : command
syntax (name := grindAttrLintInspect) "#grind_attr_lint" ppSpace "inspect" configItem* ident+ ppSpace "under" ppSpace ident: command
