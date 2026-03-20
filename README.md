# EE_598_project

# Project Goal
As I mentioned during the presentation, the goal of this project shifted partway through. The original goal was to resolve [CSLib issue #308](https://github.com/leanprover/cslib/issues/308). You can see my pull request for that [here](https://github.com/leanprover/cslib/pull/385). I made a good start toward this goal, but unfortunately because CSLib uses `#grind_lint` to check the quality of their grind annotations, and `#grind_lint` is not yet compatible with grind attributes (which was the main focus of my efforts), I was forced to pivot. Inspired by this issue, I decided that I would make the new goal of my project to implement `#grind_attr_lint`, a version of `#grind_lint` that works for grind attributes (rather than just for theorems annotated directly with `@[grind]`).

