# To do

- [ ] Testing

  - [ ] Property tests for lifetimes
  - [ ] Property tests for borrow checking

- [ ] Optimizations for efficiency

- [ ] Splitting everything into multiple .frg files based on the comments dividing functionality

- [ ] More constraints to eliminate insignificant differences between instances, so that
      each instance really represents a different program.
  - E.g. adding `mut` to a variable that isn't mutated
  - Curly braces that don't have a `next`

# Efficiency

## Valid + Borrow Checks

8 Statement, 5 Variable, 5 Value, 5 Type: 8 min translation, 311ms solving

9 Statement, 5 Variable, 5 Value, 5 Type: 23 min translation, 2 seconds solving

# Bugs

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
