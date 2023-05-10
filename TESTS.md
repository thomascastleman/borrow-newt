## Lifetime Tests

- valid program with correct lifetimes is satisfiable
- start of a lifetime must be before the end
- every variable has at most one value at a given statement
- end of lifetime is not always reachable from the beginning (nested initialization case)
- value held by some variable after end of lifetime is unsat
- owned value held by variable after its lifetime is unsat

- [ ] some test to make sure the lifetimes are constrained to be as small as possible for borrows
- [ ] check that lifetimes are not too small, make sure it counts when a value is passed from one variable to another

## Borrow Check Tests

- valid program with borrow checking is satisfiable
- possible for an otherwise valid program to fail borrow checking
- multiple borrows (&) of a given variable can exist at the same time
- invalid to have any other kind of borrow of some variable while there is a mutable borrow (&mut) to it that is alive
- use of variable after moving it is possible without borrow checking, and prevented with borrow checking
- borrow that outlives the value is possible without borrow checking and prevented with borrow checking
- can mutable a variable while it is borrowed without borrow checking, prevented with borrow checking
- use of value after the end of its lifetime is unsat
