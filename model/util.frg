#lang forge "final" "jWRoVmMudTkyxClS"

// Predicates that are used by several modules and implement common functionality.

open "sigs.frg"

// Determines if there is a path through the program from the start statement
// to the target statement, by following either the sequence of statements or 
// stepping into inner scopes.
pred statementReachable[target: Statement, start: Statement] {
    // The target is reachable by following either next (for sequential statements),
    // variable_scope_start (for inner scopes of variable declarations), or
    // curly_braces_start (for other inner scopes).
    reachable[target, start, next, inner_scope]
}

// Variant of statementReachable that only allows reachability via the `next` field.
// This outrules any entering of inner scopes in order to reach the target.
pred statementReachableOnlyNext[target: Statement, start: Statement] {
    reachable[target, start, next]
}

// Variant of statementReachable that allows for the target and start begin the same.
pred statementReachableInclusive[target: Statement, start: Statement] {
    statementReachable[target, start] or target = start
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
        statementReachableInclusive[earlier, commonAncestor.inner_scope]

        // The common ancestor happens strictly before the `later`, and
        // `later` is not part of the common ancestor's inner scope.
        some commonAncestor.next and statementReachableInclusive[later, commonAncestor.next]
    }))
}

// A variant of isBefore that allows for the statements to be the same.
pred isBeforeOrEqual[earlier: Statement, later: Statement] {
    isBefore[earlier, later] or 
    earlier = later
}

// A variant of isBefore that enforces that the earlier statement be immediately 
// before the later statement, i.e. there are no intervening statements.
pred isDirectlyBefore[earlier: Statement, later: Statement] {
    isBefore[earlier, later]
    no middle: Statement | isBetween[middle, earlier, later]
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

// Determines if a given value is an owned value.
pred isOwned[value: Value] {
    no value.borrow_referent
    no value.borrow_mut_referent
}

// Determines if a given type is an owned type.
pred isOwnedType[type: Type] {
    no type.borrow_referent_type
    no type.borrow_mut_referent_type
}

// Determines if a given value is a borrow (&).
pred isBorrow[value: Value] {
    some value.borrow_referent
}

// Determines if a given type is a borrow type.
pred isBorrowType[type: Type] {
    some type.borrow_referent_type
}

// Determines if a given value is a mutable borrow.
pred isBorrowMut[value: Value] {
    some value.borrow_mut_referent
}

// Determines if a given type is a borrow mut type.
pred isBorrowMutType[type: Type] {
    some type.borrow_mut_referent_type
}

// Extract the referent variable of a given value, or none if the value is an Owned.
fun referent(borrow: Value): Variable {
    some borrow.borrow_referent => borrow.borrow_referent else borrow.borrow_mut_referent
}

// Extract the referent value from a given borrow (or none, if Owned)
fun referentValue(value: Value): Value {
    some value.borrow_referent_value => value.borrow_referent_value else value.borrow_mut_referent_value
}

// Determines if the given variable is being modified either by reassigning to a new value or moving into or out of the variable
pred variableModification[variable: Variable, statement: Statement] {
    statement.updated_variable = variable or    // Being reassigned to
    statement.source = variable or              // Being moved out of
    statement.destination = variable            // Being moved into
}

// Determines if the statement creates a value that references the given variable.
pred variableUseInValue[variable: Variable, statement: Statement] {
    // Account for uses of variables that are embedded in values, e.g. &mut a
    (some value: Value | {
        // This value is part of this statement
        (statement.initial_value = value) or (statement.new_value = value) or (statement.moved_value = value)

        // The value uses the variable
        (value.borrow_referent = variable) or (value.borrow_mut_referent = variable)
    })
}

// Determines if the given variable is being "used" in the given statement.
// NOTE: Excludes declaration and initialization, because if initializing 
// is considered use, and use before initialization is illegal, then 
// you can never initialize.
pred variableUse[variable: Variable, statement: Statement] {
    variableModification[variable, statement] or
    variableUseInValue[variable, statement]
}

// Version of variableUse that includes initialization statements as uses.
pred variableUseOrInit[variable: Variable, statement: Statement] {
    variableUse[variable, statement] or statement.initialized_variable = variable
}

// Determines if the statement creates a borrow of the variable or moves out of it.
pred readUseOfVariable[variable: Variable, statement: Statement] {
    variableUseInValue[variable, statement] or 
    statement.source = variable
}

// Determines if the given statement is the one that creates the given value.
pred valueCreated[statement: Statement, value: Value] {
    // Only initialize/update statements can create values
    statement.initial_value = value or 
    statement.new_value = value
}

// Determines if the given statement assigns to the variable (either by initializing,
// updating, or doing a move).
pred assignsToVar[assignment: Statement, variable: Variable] {
    assignment.initialized_variable = variable or
    assignment.updated_variable = variable or 
    assignment.destination = variable
}

// Determines if the given value matches the one from the given assignment statement.
pred valueFromAssignment[assignment: Statement, value: Value] {
    value = assignment.initial_value or 
    value = assignment.new_value or
    value = assignment.moved_value
}

// Determine if the given statement is within the scope of the variable.
pred inScopeOfVariable[statement: Statement, variable: Variable] {
    some decl: DeclareVariable | {
        decl.declared_variable = variable
        statementReachableInclusive[statement, decl.inner_scope]
    }
}

// Determines if the given variable holds the given value right before the 
// execution of the given statement (not including effects of the statement itself).
pred variableHasValueBeforeStmt[statement: Statement, variable: Variable, value: Value] {
    // In order for the variable to have a value at all, it must be in scope
    inScopeOfVariable[statement, variable]

    // Look at the most recent assignment to determine the value
    some assignment: Statement | {
        assignsToVar[assignment, variable]

        // The assignment happens before the statement
        isBefore[assignment, statement]

        // No other assignment to this variable is more recent
        no moreRecentAssignment: Statement | {
            assignsToVar[moreRecentAssignment, variable]
            isBetween[moreRecentAssignment, assignment, statement]
        }
        // The variable hasn't been moved out of since this assignment, because 
        // that would leave it uninitialized.
        (!isBorrow[value]) => (no moveOut: MoveOrCopy | {
            moveOut.source = variable
            moveOut.moved_value = value
            isBetween[moveOut, assignment, statement]
        })

        // The value comes from this most recent assignment
        valueFromAssignment[assignment, value]
    }
}

// Determines if the given variable holds the given value at the point in the 
// program when this statement occurs.
// NOTE: This *includes* the effect of `statement` itself, so if it is is an 
// assignment, this will use the assignment's new value.
pred variableHasValueAtStmt[statement: Statement, variable: Variable, value: Value] {
    assignsToVar[statement, variable] => {
        // If the statement itself assigns to the variable, get the value there
        valueFromAssignment[statement, value]
    } else {
        // Otherwise, look for the value it had before this statement
        variableHasValueBeforeStmt[statement, variable, value]
    }
}

// Determines if the target value is reachable via a chain of borrows from the start.
// I.e., You could dereference the start value some number of times to get to the target.
pred borrowReachable[target: Value, start: Value] {
    reachable[target, start, borrow_referent_value, borrow_mut_referent_value]
}