#lang forge "final" "jWRoVmMudTkyxClS"

one sig Program {
    program_start: lone Statement
}

// A lifetime describes a region of the program for which a value is "live" (in use).
sig Lifetime {
    // TODO: Decide what these bounds mean (inclusive/exclusive)
    begin: one Statement,
    end: one Statement
}

one sig Mutable {}

// A variable represents a 'place' where a value can be stored.
sig Variable {
    // Whether this variable is being declared as mutable or not.
    mutable: lone Mutable
}

// ============================== Values ==============================

abstract sig Value {
    value_lifetime: one Lifetime
}

sig Owned extends Value {}
sig Borrow extends Value {
    borrow_referent: one Variable 
}
sig BorrowMut extends Value {
    borrow_mut_referent: one Variable 
}

// ============================== Statements ==============================

abstract sig Statement {
    // Each Statement has a link to the Statement that follows it. Statements
    // appearing at the end of scopes will have no `next`.
    next: lone Statement,
    
    // Only used for DeclareVariable and Scope statements
    inner_scope: lone Statement
}

// A variable declaration. E.g., `let a;`
sig DeclareVariable extends Statement {
    // The variable being declared
    declared_variable: one Variable
}

// A variable initialization to some value. E.g. `a = &b;`
sig InitializeVariable extends Statement {
    initialized_variable: one Variable,
    initial_value: one Value
}

// Setting a mutable variable to some new value. E.g. `a = Box::new(());` where 
// a has previously been initialized.
// NOTE: Only valid for variables declared mut
sig UpdateVariable extends Statement {
    updated_variable: one Variable,
    new_value: one Value
}

sig MoveOrCopy extends Statement {
    // The value being moved
    moved_value: one Value,
    // The variable that is being moved out of.
    source: one Variable,
    // The destination is the variable to which ownership of this value is
    // begin transferred. If there is no destination, this indicates the value
    // is being moved to another function.
    destination: lone Variable
}

// A block statement, which creates a new scope.
sig CurlyBraces extends Statement {}


// Determines if there is a path through the program from the start statement
// to the target statement, by following either the sequence of statements or 
// stepping into inner scopes.
pred statementReachable[target: Statement, start: Statement] {
    // The target is reachable by following either next (for sequential statements),
    // variable_scope_start (for inner scopes of variable declarations), or
    // curly_braces_start (for other inner scopes).
    reachable[target, start, next, inner_scope]
}

pred statementReachableOnlyNext[target: Statement, start: Statement] {
    reachable[target, start, next]
}

// Checks if the `before` statement occurs strictly earlier in the program than the `after` statement.
pred isBefore[earlier: Statement, later: Statement] {
    // Statement cannot be before itself
    earlier != later

    // EITHER: You can directly reach `later` by traversing down the tree from `earlier`
    (statementReachable[later, earlier] or 

    // OR: You can "back up" the tree to some "common ancestor" statement whose 
    // scope contains the `earlier` statement, and occurs before the `later`.
    (some commonAncestor: Statement | {
        // The common ancestor is a containing scope for `earlier`
        some commonAncestor.inner_scope
        (statementReachable[earlier, commonAncestor.inner_scope] or 
        earlier = commonAncestor.inner_scope)

        // The common ancestor happens strictly before the `later`, and
        // `later` is not part of the common ancestor's inner scope.
        some commonAncestor.next and statementReachable[later, commonAncestor.next]
    }))
}

// Determines if a given statement is between a start and end statement, exclusive.
pred isBetween[middle: Statement, start: Statement, end: Statement] {
    // The middle is not at the endpoints (this is exclusive)
    middle != start
    middle != end

    // The middle is contained between the start/end, by being after the start and before the end.
    isBefore[start, middle]
    isBefore[middle, end]
}

// Determines if a given statement is between a start and end, inclusive of the bounds.
pred isBetweenInclusive[middle: Statement, start: Statement, end: Statement] {
    middle = start or 
    middle = end or
    isBetween[middle, start, end]
}


// ============================== Program Structure ==============================

// All statements in the program (including nested scopes) follow a linear structure.
pred sequentialStatements {
    // There are no cycles in the chain of statements (no statement is reachable from itself)
    no s: Statement | statementReachable[s, s]

    // Statements are the `next` of at MOST one other statement
    all s: Statement | {
        lone prev: Statement | prev.next = s
    }

    // All statements are part of the program (reachable from the program start)
    all s: Statement | (s != Program.program_start => statementReachable[s, Program.program_start])
}

// Determines if the given variable is being "used" in the given statement.
// NOTE: Excludes declaration and initialization, because if initializing 
// is considered use, and use before initialization is illegal, then 
// you can never initialize.
pred variableUse[variable: Variable, statement: Statement] {
    statement.updated_variable = variable or    // Being reassigned to
    statement.source = variable or              // Being moved out of
    statement.destination = variable or         // Being moved into

    // Account for uses of variables that are embedded in values, e.g. &mut a
    (some value: Value | {
        // This value is part of this statement
        (statement.initial_value = value) or (statement.new_value = value) or (statement.moved_value = value)

        // The value uses the variable
        (value.borrow_referent = variable) or (value.borrow_mut_referent = variable)
    })
}

// Checks that variable use is preceded by initialization and declaration.
pred variableDeclThenInitThenUsed {
    all v: Variable | {
        some decl: DeclareVariable, init: InitializeVariable | {
            decl.declared_variable = v      // v is declared
            init.initialized_variable = v   // v is initialized

            // The initialization is in the scope of this variable.
            // NOTE: This is necessary in addition to the above constraint, 
            // because initializations are not considered uses.
            statementReachable[init, decl]

            all use: Statement | variableUse[v, use] implies {
                // Use is preceded by initialization
                isBetween[init, decl, use]

                // All uses of the variable are within the scope of that variable
                // NOTE: We use NoExit here, because we do not want to exit scopes 
                // when finding a path from declaration to use.
                statementReachable[use, decl]
            }
        }
    }
}

// Variables that are mutated must be declared mutable.
pred onlyMutateMutableVars {
    //for all variables such that there is some update of it implies it was mutable 
    all v: Variable | {
        (some update: UpdateVariable | update.updated_variable = v) => some v.mutable
        (some move: MoveOrCopy | move.destination = v) => some v.mutable
    }
}

// Ensures that all objects in the instance are actually being used in the program.
// It prevents "floating" objects from cluttering up our instances.
pred allObjectsParticipating {
    // All lifetimes correspond to exactly one value. This eliminates lifetimes
    // that are not tied to any value, and ensures that each value gets its own lifetime.
    all lifetime: Lifetime | {
        one value: Value | value.value_lifetime = lifetime
    }
    // All variables in the instance are declared in the program exactly once.
    // This eliminates variables that do not participate in the program, and 
    // ensures that the same variable isn't declared more than once.
    all variable: Variable | {
        one decl: DeclareVariable | decl.declared_variable = variable
    }
    // All values are used in some statement. This eliminates values that 
    // aren't actually part of the program.
    all value: Value | {
        // There is exactly one place where this value is introduced to the program.
        (one s: Statement | {
            (s.initial_value = value) or (s.new_value = value)
        })
    }

    //Optional TODO: constrain curly braces to be useful-> having at least one statement in it 
}

// For every variable, there should be at most one InitializeVariable statement 
// for that variable, though it is not required to be initialized.
// Everthing else should be considered an update
pred uniqueInitialization {
    all v: Variable | {
        lone initialize: InitializeVariable | initialize.initialized_variable = v
    }
}

// Constrains the inner_scope field to only be valid for declarations and curly brace statements.
pred innerScopeValid {
    // Variable declarations cannot have a "next" statement, as all statements that
    // occur afterwards are subsumed in their scope (accessible via inner_scope).
    all d: DeclareVariable | no d.next

    // Only declarations and curly brace statements can create nested scopes
    all i: InitializeVariable   | no i.inner_scope
    all m: MoveOrCopy                 | no m.inner_scope
    all u: UpdateVariable       | no u.inner_scope

    // Every statement is the first statement of at most one scope
    all s, outer: Statement | {
        (outer.inner_scope = s) => {
            // No statement at all has this one as its `next` 
            no s.~next

            // No *other* statement has this as its inner scope
            no other: Statement | (other != outer and other.inner_scope = s)
        }
    }
}

// Constrains the move_value field of MoveOrCopy statements to refer to the value
// of the source variable involved in the move, at the time of move.
pred correctMoveValue {
    all move: MoveOrCopy | {
        some assignment: Statement | {
            // Assigns to this variable
            (assignment.initialized_variable = move.source or
            assignment.updated_variable = move.source or 
            assignment.destination = move.source)

            // The assignment happens before the move
            isBefore[assignment, move]

            // No other assignment to this variable is more recent
            no moreRecentAssignment: Statement | {
                (moreRecentAssignment.initialized_variable = move.source or
                moreRecentAssignment.updated_variable = move.source or 
                moreRecentAssignment.destination = move.source)

                isBetween[moreRecentAssignment, assignment, move]
            }    

            // The move gets the value from this most recent assignment
            (move.moved_value = assignment.initial_value or 
            move.moved_value = assignment.new_value or
            move.moved_value = assignment.moved_value)
        }
    }
}

pred validProgramStructure {
    innerScopeValid
    sequentialStatements
    variableDeclThenInitThenUsed
    onlyMutateMutableVars
    allObjectsParticipating
    uniqueInitialization
    correctMoveValue
}

// ============================== Lifetimes ==============================

// Determines if the given statement is the one that creates the given value.
pred valueCreated[statement: Statement, value: Value] {
    // Only initialize/update statements can create values
    statement.initial_value = value or 
    statement.new_value = value
}

// Determines if the given statement is the last use of the given variable.
pred lastUse[statement: Statement, variable: Variable] {
    // The statement is a use of the variable
    variableUse[variable, statement]

    // There is no later use
    no laterUse: Statement | {
        isBefore[statement, laterUse]
        variableUse[variable, laterUse]
    }
}

pred reachableViaMove[target: Variable, start: Variable] {
    // TODO: Ria
    //some statmeent1 where start is source 
    //all in between ones dest1 = source2
    //some statement2 where target is dest
    //FIXME: this shouldn't be an implies it would need to be an and but then im not sure how to keep the startStatement and endStatement variables 
    some startStatement, endStatement: MoveOrCopy | (startStatement.source = start and endStatement.destination = target) => {
        all middleStatement: MoveOrCopy | isBetween[middleStatement, startStatement, endStatement] => {
            (middleStatement = startStatement or 
            middleStatement = endStatement or 
            (reachableViaMove[target, middleStatement.source] and 
            reachableViaMove[middleStatement.source, start]))
        }
    }
    
}

// Determines if the given variable is the *first* variable that holds the value.
pred initialVariable[variable: Variable, value: Value] {
    some s: Statement | {
        valueCreated[s, value]
        (s.initialized_variable = variable or s.updated_variable = variable)
    }
}

// Determines if the given variable is the *last* variable that holds the value.
pred lastVariable[variable: Variable, value: Value] {
    some initialVar: Variable | {
        initialVariable[initialVar, value]
        reachableViaMove[variable, initialVar]

        //no moves out of initialVar
        no otherVar: Variable | {
            some m: MoveOrCopy | {
                m.source = variable
                m.destination = otherVar
                m.moved_value = value
            }
        }
    }
}

pred ownedEndOfLifetime[owned: Owned, end: Statement] {
    some lastHoldingVar: Variable | {
        lastVariable[lastHoldingVar, owned]

        //   - The value is moved in a function call (destinationless move)
        (end.source = lastHoldingVar and no end.destination) or
        //   - The holding variable is assigned to again (holding variable is overwritten)
        (end.updated_variable = lastHoldingVar) or
        //   - The holding variable goes out of scope
        {
            // The end is indeed a statement at the end of a scope
            no end.next

            some decl: DeclareVariable | {
                // The end is within the scope of the last holding variable
                decl.declared_variable = lastHoldingVar
                statementReachable[end, decl.inner_scope]

                // It is the *very last* statement of the inner scope of the last holding variable
                no earlierEnd: Statement | {
                    statementReachable[earlierEnd, decl.inner_scope]
                    isBefore[earlierEnd, end]
                }
            }
        }
    }
}

// For owned values, the lifetime extends from the point of creation until either:
//   - The value is moved in a function call (destinationless move)
//   - The holding variable is assigned to again (holding variable is overwritten)
//   - The holding variable goes out of scope
pred ownedLifetime[owned: Owned] {
    // The start of lifetime is the point of creation
    valueCreated[owned.value_lifetime.begin, owned]

    // The end of the lifetime is a valid end for owned values
    ownedEndOfLifetime[owned, owned.value_lifetime.end]

    // The end is the earliest statement that meets such ending conditions
    no earlierEnd: Statement | {
        ownedEndOfLifetime[owned, earlierEnd]
        isBefore[earlierEnd, owned.value_lifetime.end]
    }
}

// For borrows, the lifetime extends from the point of creation until last use.
pred borrowLifetime[borrow: Borrow] {
    // The start of lifetime is the point of creation
    valueCreated[borrow.value_lifetime.begin, borrow]

    // TODO:
}

// For mutable borrows, the lifetime extends from the point of creation until last use.
pred borrowMutLifetime[borrowMut: BorrowMut] {
    // The start of lifetime is the point of creation
    valueCreated[borrowMut.value_lifetime.begin, borrowMut]

    // TODO: Idea for how we might implement this:
    some initVar: Variable, lastVar: Variable | {
        lastVariable[lastVar, borrowMut]
        lastUse[borrowMut.value_lifetime.end, lastVar]
    }
}

// Enforces that all lifetimes have been determined following the rules.
// NOTE: This does NOT check that the program borrow checks, but only ensures
// that the lifetimes are correct so that they may be used in analysis.
pred lifetimesCorrect {
    // Each kind of value has the corresponding kind of lifetime
    all borrow: Borrow | borrowLifetime[borrow]
    all borrowMut: BorrowMut | borrowMutLifetime[borrowMut]
    all owned: Owned | ownedLifetime[owned]
}


// ============================== Borrow Checking ==============================

// TODO: Add predicates for these rules
// Borrow checking rules:
// - When there is an exclusive reference (&mut) to a variable, there can be 
//   no other references (& or &mut) alive at the same time.
// - As many shared references (&) as you want can coexist at the same time.
// - You cannot move out of a variable that is borrowed (either & or &mut)
// - You cannot mutate a variable that is borrowed (either & or &mut)
// - Once you move out of a variable, you cannot use it (it becomes uninitialized)
// - You can only construct an exclusive reference (&mut) to a variable that is declared mut
// - The lifetime of a borrow of a value must be contained within the lifetime of the value

run {
    validProgramStructure
    lifetimesCorrect

    some value: Value, variable: Variable | value.borrow_referent = variable
    some value: Value, variable: Variable | value.borrow_mut_referent = variable
} for 7 Statement, 5 Variable, 5 Value