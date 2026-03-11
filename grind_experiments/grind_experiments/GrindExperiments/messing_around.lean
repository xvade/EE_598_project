import GrindExperiments.Init
import GrindExperiments.People

set_option linter.hashCommand false

theorem my_steve_is_the_one (x : Person) (hx : mod.on_right Person.mary x) : x = Person.steve := by
  grind[my_grind_attr]

#grind_lint check (detailed:=0) in mod
#grind_attr_lint check (detailed:=0) in mod



-- #grind_lint check_attr my_grind_attr
