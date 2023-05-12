#lang forge "final" "jWRoVmMudTkyxClS"

// Predicates that constrain the lifetimes of values, ensuring that they indicate the proper 
// range of statements given the value's type.

open "sigs.frg"
open "util.frg"

// Determines if this statement is the last usage of the given variable, while 
// it is holding the given value. I.e., if there are later uses of the variable,
// they occur while it is holding different values.
pred lastUseOfVarWithValue[statement: Statement, variable: Variable, value: Value] {
    variableUseOrInit[variable, statement]
    variableHasValueAtStmt[statement, variable, value]

    no laterUse: Statement | {
        variableUseOrInit[variable, laterUse]
        variableHasValueAtStmt[laterUse, variable, value]
        isBefore[statement, laterUse]
    }
}

// Determines if the value from the start variable is eventually moved 
// into the target variable (potentially by a long chain of other moves).
pred reachableViaMove[target: Variable, start: Variable, value: Value] {
    some startStatement, endStatement: MoveOrCopy | {
        // The start moves OUT OF the starting variable
        startStatement.source = start

        // The end moves INTO the target variable
        endStatement.destination = target

        // If the moved value is the same between these two statements, and equal to the current value 
        // there must be a chain of moves that gets the value from start to target.
        endStatement.moved_value = value
        startStatement.moved_value = value
    }
}

// Determines if the given variable is the *first* variable that holds the value.
pred initialVariable[variable: Variable, value: Value] {
    some s: Statement | {
        valueCreated[s, value]
        (s.initialized_variable = variable or s.updated_variable = variable)
    }
}

// Determines if this variable eventually holds this value.
pred holdingVariable[variable: Variable, value: Value] {
    some initialVar: Variable | {
        initialVariable[initialVar, value]
        reachableViaMove[variable, initialVar, value] or variable = initialVar
    }
}

// Determines if the given variable is the *last* variable that holds the value.
pred lastVariable[variable: Variable, value: Value] {
    // This variable holds the value
    holdingVariable[variable, value]

    // This variable is never moved out of into some other variable
    // (It can be moved in a destination-less move though)
    no otherVar: Variable | {
        otherVar != variable

        some m: MoveOrCopy | {
            m.source = variable
            m.destination = otherVar
            m.moved_value = value
        }
    }
}

// Determines if the given `end` statement is a valid end of lifetime for the given owned value.
pred ownedEndOfLifetime[owned: Owned, end: Statement] {
    some lastHoldingVar: Variable | {
        lastVariable[lastHoldingVar, owned]

        // Case 1) The end statement is a destinationless move of the last holding variable of the value
        {
            end.source = lastHoldingVar 
            no end.destination
            variableHasValueBeforeStmt[end, lastHoldingVar, owned]
        } or

        // Case 2) The end statement is the last statement before the last holding variable 
        // is overwritten to a different value, either by an update or a move into the variable.
        {
            // There is a statement following the end of lifetime
            some stmtAfterEnd: Statement | {
                isDirectlyBefore[end, stmtAfterEnd]

                // It modifies the last holding variable for this value
                (stmtAfterEnd.updated_variable = lastHoldingVar or
                (stmtAfterEnd.destination = lastHoldingVar and stmtAfterEnd.moved_value != owned))

                // It does so while the last holding variable was actually holding this value
                variableHasValueBeforeStmt[stmtAfterEnd, lastHoldingVar, owned]
            }
        } or

        // Case 3) The end statement is the last statement before the last holding variable goes out of scope
        {
            // The end is indeed a statement at the end of a scope
            no end.next
            no end.inner_scope

            some decl: DeclareVariable | {
                // The end is within the scope of the last holding variable
                decl.declared_variable = lastHoldingVar
                statementReachable[end, decl.inner_scope]

                // It is the last statement in that scope.
                // (All other statements in that scope are *before* the end)
                all stmtInSameScope: Statement | {
                    (statementReachableInclusive[stmtInSameScope, decl.inner_scope] and stmtInSameScope != end) => {
                        isBefore[stmtInSameScope, end]
                    }
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
    
    // The beginning of the lifetime cannot be after the end 
    isBeforeOrEqual[owned.value_lifetime.begin, owned.value_lifetime.end]
}

// Determine if the given outer borrow contains the borrow nested within it, and 
// the given statement is the last use of the outer borrow
pred outerBorrowUse[borrow: Value, outerBorrow: Value, useOfOuterBorrow: Statement] {
    // The borrow is reachable from the outer borrow
    borrowReachable[borrow, outerBorrow] or outerBorrow = borrow 

    // The outer borrow is either created at this statement, or read
    (valueCreated[useOfOuterBorrow, outerBorrow] or 
    (some outerBorrowHoldingVar: Variable | {
        readUseOfVariable[outerBorrowHoldingVar, useOfOuterBorrow]
        variableHasValueAtStmt[useOfOuterBorrow, outerBorrowHoldingVar, outerBorrow]
    }))

    // The use needs to be in the scope of the variable from which the outer borrow was created
    inScopeOfVariable[useOfOuterBorrow, referent[outerBorrow]]
}

// Constrain the end of lifetime for a given borrow (either & or &mut).
// The end of lifetime of a borrow should be the last use of any value 
// from which this borrow is reachable by following a chain of borrows.
// E.g. &a can be reached through &mut &a and &&mut &a.
pred borrowEndOfLifetime[borrow: Value] {
    some outerBorrow: Value, lastUseOfOuterBorrow: Statement | {
        // This statement is a last use of an outer borrow for this borrow
        outerBorrowUse[borrow, outerBorrow, lastUseOfOuterBorrow]
        
        // This is the absolute last possible candidate for the end of lifetime
        // NOTE: otherOuterBorrow could equal outerBorrow here, this constraint just ensures
        // that the use of the outer borrow we're looking at is the last possible one.
        no otherOuterBorrow: Value, otherUse: Statement | {
            outerBorrowUse[borrow, otherOuterBorrow, otherUse]
            isBefore[lastUseOfOuterBorrow, otherUse]
        }

        // The lifetime ends at this use
        borrow.value_lifetime.end = lastUseOfOuterBorrow
    }
}

// Constrain the lifetime begin and end for a borrow value.
pred borrowLifetime[borrow: Value] {
    // The start of lifetime is the point of creation
    valueCreated[borrow.value_lifetime.begin, borrow]

    // The end of lifetime is the last use of any value through which the borrow 
    // is reachable by a chain of nested borrows.
    borrowEndOfLifetime[borrow]

    // The beginning of the lifetime cannot be after the end
    isBeforeOrEqual[borrow.value_lifetime.begin, borrow.value_lifetime.end]
}

// Enforces that all lifetimes have been determined following the rules.
// NOTE: This does NOT check that the program borrow checks, but only ensures
// that the lifetimes are correct so that they may be used in analysis.
pred lifetimesCorrect {
    // Each kind of value has the corresponding kind of lifetime
    all value: Value | {
        (isBorrow[value] or isBorrowMut[value]) => borrowLifetime[value]
        isOwned[value] => ownedLifetime[value]
    }
}