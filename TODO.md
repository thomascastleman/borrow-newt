# To do

- [ ] We don't model the "copy" behavior of shared references, which shouldn't be "movable"

  - Should we just have an UpdateVariable statement instead of Move, which
    behaves like a move if the thing is movable, and behaves like a copy otherwise

- [ ] Visualize lifetimes

  - Use some kind of bounding box around the relevant statements, color-coded by value?

- [ ] Changes to visualization so that programs can be pasted and run

  - Don't use Value0, etc, for owned, use Box or other type

- [ ] Testing

  - [ ] Property tests for lifetimes
  - [ ] Property tests for borrow checking

- [ ] Optimizations for efficiency

- [ ] Splitting everything into multiple .frg files based on the comments dividing functionality

# Bugs

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
