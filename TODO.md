# To do

- [ ] Visualization updates

  - [x] Visualize types on declarations

  - [ ] Visualize lifetimes

    - [x] Use some kind of bounding box around the relevant statements, color-coded by value?
    - [x] Visualize the bounding boxes first, then the text ON TOP of it, so that
          you can see the text better

    - [x] Vary the width of the boxes so that overlap is easier to see
          Ideally, this would depend on how "nested" a lifetime is within other lifetimes

    - [ ] Actually calculate what the max width of the program text is, so we can
          choose a base width for the bounding boxes appropriately (and also an
          offset for the statement labels)

  - [x] Changes to visualization so that programs can be pasted and run

    - Don't use Value0, etc, for owned, use Box or other type

- [ ] Testing

  - [ ] Property tests for lifetimes
  - [ ] Property tests for borrow checking

- [ ] Optimizations for efficiency

- [ ] Splitting everything into multiple .frg files based on the comments dividing functionality

- [ ] More constraints to eliminate insignificant differences between instances, so that
      each instance really represents a different program.
  - E.g. adding `mut` to a variable that isn't mutated
  - Curly braces that don't have a `next`

# Bugs

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
