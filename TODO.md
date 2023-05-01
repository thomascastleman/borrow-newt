# To do

- [ ] Constrain lifetimes
- [ ] Borrow checking rules
- [ ] predicate to prevent variable from borrowing itself
- [ ] We don't model the "copy" behavior of shared references, which shouldn't be "movable"
  - Should we just have an UpdateVariable statement instead of Move, which
    behaves like a move if the thing is movable, and behaves like a copy otherwise

# Bugs

- We allow a variable to borrow itself, which isn't legal in actual Rust because
  the types &T (or &mut T) and T will never be equal, but we're not modeling types.

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
