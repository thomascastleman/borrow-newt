# To do

- [ ] Optimizations for efficiency

- [ ] Splitting everything into multiple .frg files based on the comments dividing functionality

- [ ] Try very large instances (20 Statement, etc)

- [ ] More constraints to eliminate insignificant differences between instances, so that
      each instance really represents a different program.

  - [x] E.g. adding `mut` to a variable that isn't mutated
  - [x] Curly braces that don't have a `next`

- [ ] Testing

  - [ ] More tests for program structure now with the new fields (Thomas)

- [ ] Visualization: Try removing indentation + explicit braces from scope of `let` statements

# Efficiency

## (**OLD**) Valid + Borrow Checks

exactly 7 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 43 seconds translation, 5 seconds solving

exactly 8 Statement, exactly 3 Variable, exactly 3 Value, 5 Type, 5 Int: 40 seconds translation, 995 ms solving

8 Statement, 5 Variable, 5 Value, 5 Type: 8 min translation, 311ms solving

9 Statement, 5 Variable, 5 Value, 5 Type: 23 min translation, 2 seconds solving

- With Tim's optimizer, down to 15 min translation, 560ms solving

## Valid **with new end of lifetime constraints**

exactly 7 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 3.5 min translation, 5 seconds solving

exactly 8 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 3.5 min translation, 12 seconds solving

# Bugs

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
