import GrindExperiments.TacticExperimentation.PrintAttr.PrintAttr
import GrindExperiments.TacticExperimentation.GrindAttrLint.GrindAttrLint
import Mathlib.Init
import Mathlib.Tactic.Common
import GrindExperiments.Init
import GrindExperiments.People


#print_attr my_grind_attr a
#grind_attr_lint check my_grind_attr
#grind_attr_lint inspect (detailed:=0) mod.steve_is_the_one under my_grind_attr
#grind_lint inspect (detailed:=0) mod.steve_is_the_one
-- #grind_lint check

example (x : Person) (hx : mod.on_right Person.mary x) : Person.steve = x := by
  grind[my_grind_attr]
  -- grind[a]
