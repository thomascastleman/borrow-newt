# To do

- [ ] Optimizations for efficiency

- [ ] Splitting everything into multiple .frg files based on the comments dividing functionality

- [ ] More constraints to eliminate insignificant differences between instances, so that
      each instance really represents a different program.
  - [x] E.g. adding `mut` to a variable that isn't mutated
  - [x] Curly braces that don't have a `next`

# Efficiency

## Valid + Borrow Checks

exactly 7 Statement, exactly 3 Variable, exactly 3 Value, 5 Type: 43 seconds translation, 5 seconds solving

exactly 8 Statement, exactly 3 Variable, exactly 3 Value, 5 Type, 5 Int: 40 seconds translation, 995 ms solving

8 Statement, 5 Variable, 5 Value, 5 Type: 8 min translation, 311ms solving

9 Statement, 5 Variable, 5 Value, 5 Type: 23 min translation, 2 seconds solving

- With Tim's optimizer, down to 15 min translation, 560ms solving

# Bugs

- [ ] Are we calculating end of lifetime for &mut and & correctly in the case of
      nested borrows? See example program below, which happens to work but only
      because the end of lifetime statement is a move

  ```
  let v0: &mut &mut Box<i32>;
  {
    let mut v1: &mut Box<i32>;
    {
      {
        let mut v2: Box<i32>;
        {
          v2 = Box::new(0);
          v1 = &mut v2;         // <-- Value1 start lifetime
          drop(v2);
        }
      }
      v0 = &mut v1;
      drop(v0);                 // <-- Value1 end lifetime
    }
  }
  ```

# Questions

- Is there a way to parameterize over the bounds (exactly 5 Statement, etc)
  in tests? That way we can easily change the bounds on all our tests instead
  of manually rewriting for each test.
