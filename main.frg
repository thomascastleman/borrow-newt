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
    // For owned values, the lifetime extends from 
    // initialization until either:
    //   - The value is moved
    //   - The holding variable is assigned to again
    //   - The holding variable goes out of scope
    // 
    // For borrows, the lifetime extends from the point of 
    // creation until the last use of the reference.
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

sig Move extends Statement {
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

pred isBefore[s1: Statement, s2: Statement] {
    // Statement cannot be before itself
    s1 != s2

    // EITHER: You can directly reach s2 by traversing down the tree from s1
    (statementReachable[s2, s1] or 

    // OR: There is a "common ancestor" statement, from which s1 can be reached
    // by entering inner scopes, and s2 can be reached at the same scope level (only via next)
    (some commonAncestor: Statement | {
        not statementReachableOnlyNext[s1, commonAncestor]
        statementReachable[s1, commonAncestor]
        statementReachableOnlyNext[s2, commonAncestor]
    }))
}

// Determines if a given statement is between a start and end statement, exclusive.
pred isBetween[middle: Statement, start: Statement, end: Statement] {
    // The middle is not at the endpoints (this is exclusive)
    middle != start
    middle != end

    isBefore[start, middle]
    isBefore[middle, end]

    // FIXME: Remove this if the above works
    // // The middle should be reachable from the start (it occurs after the start)
    // statementReachable[middle, start] 

    // // The middle should NOT be reachable from the end. If this is the case,
    // // the end is necessarily after the middle.
    // // NOTE: The end is not necessarily reachable from the end, given the
    // // tree structure of our programs.
    // not statementReachable[middle, end]

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
pred enterScopeValid {
    // Variable declarations cannot have a "next" statement, as all statements that
    // occur afterwards are subsumed in their scope (accessible via inner_scope).
    all d: DeclareVariable | no d.next

    // Only declarations and curly brace statements can create nested scopes
    all i: InitializeVariable   | no i.inner_scope
    all m: Move                 | no m.inner_scope
    all u: UpdateVariable       | no u.inner_scope

    // No statement is both the `next` and `inner_scope` of some other statements.
    // This is because:
    //  - The only way to enter a new scope is via inner_scope, so a statement
    //    cannot be accessible via next if it is the first in a new scope
    //  - If a statement is accessible by next, then it is not the first in a 
    //    new scope and thus shouldn't be accessible by inner_scope
    no s: Statement | {
        some prev, containing: Statement | {
            prev.next = s
            containing.inner_scope = s
        }
    }
}

// Constrains the move_value field of Move statements to refer to the value
// of the source variable involved in the move, at the time of move.
pred correctMoveValue {
    all move: Move | {
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
    enterScopeValid
    sequentialStatements
    variableDeclThenInitThenUsed
    onlyMutateMutableVars
    allObjectsParticipating
    uniqueInitialization
    correctMoveValue
}

// ============================== Lifetimes ==============================

// Enforces that all lifetimes have been determined following the rules.
// NOTE: This does NOT check that the program borrow checks, but only ensures
// that the lifetimes are correct so that they may be used in analysis.
pred lifetimesCorrect {
    // TODO: 
    // - Go through all values to check values lifetimes (Owned, Borrow, Borrow Mut)
    // - Lifetimes should be unique (not shared between multiple values)
}

// For owned values, the lifetime extends from initialization until either:
//   - The value is moved
//   - The holding variable is assigned to again
//   - The holding variable goes out of scope
pred ownedLifetimes[o: Owned] {
    // TODO:
}

pred borrowLifetimes[b: Borrow] {
    // TODO:
}

pred borrowMutLifetimes[bm: BorrowMut] {
    // TODO:
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

run {
    validProgramStructure
    all move: Move | {
        move.source != move.destination
        some move.destination
    }
} for exactly 6 Statement, exactly 1 Move