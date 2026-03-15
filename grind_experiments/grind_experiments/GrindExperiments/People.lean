import GrindExperiments.Init

inductive Person where | mary | steve | ed | jolin

open Person

namespace mod
def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

@[grind .]
theorem steve_is_the_one (x : Person) (hx : on_right mary x) : x = steve := by sorry


@[my_grind_attr .]
theorem steve_is_the_one' (x : Person) (hx : on_right mary x) : x = steve := by sorry

@[my_grind_attr .]
theorem the_one_is_steve (x : Person) (hx : on_right mary x) : steve = x := by sorry


end mod
