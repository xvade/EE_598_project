/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
-- module
-- prelude
-- public import Init.Grind.Interactive
-- public import Init.Grind.Config
import Init.Grind.Interactive
import Init.Grind.Config
-- public import GrindExperiments.MyLint
-- public section
namespace Lean.Grind
open Parser Tactic Grind


-- syntax (name := grindAttrLintCheck) "#grind_attr_lint" ppSpace &"check" (ppSpace configItem)* ppSpace grindAttrName : command
syntax (name := grindAttrLintCheck) "#grind_attr_lint" ppSpace &"check" (ppSpace configItem)* (ppSpace ident)+ (ppSpace "in" (ppSpace &"module")? ident+)? : command


end Lean.Grind
