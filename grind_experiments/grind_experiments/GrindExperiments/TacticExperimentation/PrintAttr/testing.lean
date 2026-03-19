import GrindExperiments.TacticExperimentation.PrintAttr
import Mathlib.Init
import Mathlib.Tactic.Common
import GrindExperiments.Init

#print_attr my_grind_attr

example : 1 = 1 := by
  grind[my_grind_attr]
  -- grind[a]
