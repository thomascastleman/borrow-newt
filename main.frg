#lang forge "final" "jWRoVmMudTkyxClS"

one sig Program {
    program_start: lone Statement
}

// A lifetime describes a region of the program for which a value is "live" (in use).
sig Lifetime {
    begin: one Statement,
    end: one Statement
}

abstract sig Type {}

sig OwnedType extends Type {}
sig BorrowType extends Type {
    borrow_referent_type: one Type
}
sig BorrowMutType extends Type {
    borrow_mut_referent_type: one Type
}

one sig Mutable {}

// A variable represents a 'place' where a value can be stored.
sig Variable {
    // Whether this variable is being declared as mutable or not.
    mutable: lone Mutable,

    // The type of values this variable can hold.
    variable_type: one Type
}

// ============================== Values ==============================

abstract sig Value {
    value_lifetime: one Lifetime
}

sig Owned extends Value {}
sig Borrow extends Value {
    borrow_referent: one Variable,
    borrow_referent_value: lone Value
}
sig BorrowMut extends Value {
    borrow_mut_referent: one Variable,
    borrow_mut_referent_value: lone Value
}

// ============================== Statements ==============================

abstract sig Statement {
    // Each Statement has a link to the Statement that follows it. Statements
    // appearing at the end of scopes will have no `next`.
    next: lone Statement,
    
    // Only used for DeclareVariable and CurlyBraces statements
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
    all s: Statement | statementReachableInclusive[s, Program.program_start]
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

// Checks that variable use is preceded by initialization and declaration.
pred variableDeclThenInitThenUsed {
    all v: Variable | {
        some decl: DeclareVariable, init: InitializeVariable | {
            decl.declared_variable = v      // v is declared
            init.initialized_variable = v   // v is initialized

            // The initialization is in the scope of this variable.
            // NOTE: This is necessary in addition to the below constraint, 
            // because initializations are not considered uses.
            statementReachable[init, decl]

            all use: Statement | variableUse[v, use] implies {
                // Use is preceded by initialization
                isBetween[init, decl, use]

                // All uses of the variable are within the scope of that variable
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

// You can only construct an exclusive reference (&mut) to a variable that is declared mut
// referent of a borrowMut is mutable
pred onlyBorrowMutMutableVars {
    all borrowMut: BorrowMut | {
       some borrowMut.borrow_mut_referent.mutable
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
    // Also, do not pointlessly mark variables as mutable if they don't need to be.
    all variable: Variable | {
        one decl: DeclareVariable | decl.declared_variable = variable

        some variable.mutable => {
            (some mutation: Statement | {
                mutation.updated_variable = variable or mutation.destination = variable
            }) or 
            (some borrowMut: BorrowMut | borrowMut.borrow_mut_referent = variable)
        }
    }
    // All values are used in some statement. This eliminates values that 
    // aren't actually part of the program.
    all value: Value | {
        // There is exactly one place where this value is introduced to the program.
        (one s: Statement | {
            (s.initial_value = value) or (s.new_value = value)
        })
    }
    // Every set of braces that introduces a new scope must serve the purposes of limiting 
    // the scope of some variable declaration (the declaration appears inside the braces).
    // Any other use of braces does not impact the meaning of the program.
    all curly: CurlyBraces | {
        some curly.inner_scope
        some curly.next
        some decl: DeclareVariable | {
            statementReachableOnlyNext[decl, curly.inner_scope] or decl = curly.inner_scope
        }
    }
    // Every type can be reached from some variable type annotation. 
    // No types just floating around.
    all type: Type | {
        some variable: Variable | {
            reachable[type, variable.variable_type, borrow_referent_type, borrow_mut_referent_type] or 
            type = variable.variable_type
        }
    }
    // Do not allow moves from the same variable to itself, as they do nothing.
    no move: MoveOrCopy | move.source = move.destination
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
    all m: MoveOrCopy           | no m.inner_scope
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

// Constrains the move_value field of MoveOrCopy statements to refer to the value
// of the source variable involved in the move, at the time of move.
pred correctMoveValue {
    all move: MoveOrCopy | {
       variableHasValueBeforeStmt[move, move.source, move.moved_value] 
    }
}

// Determines if the given types match at the outermost level, without checking equivalence of nested types.
pred surfaceTypeMatches[t1: Type, t2: Type] {
    (isOwnedType[t1] and isOwnedType[t2]) or
    (isBorrowType[t1] and isBorrowType[t2]) or
    (isBorrowMutType[t1] and isBorrowMutType[t2])
}

// Determines if the given types are equal.
pred sameType[t1: Type, t2: Type] {
    // At the outermost level, the types must match
    surfaceTypeMatches[t1, t2]

    // Construct a relation that represents reachability from an outer type to the types 
    // nested inside it, by taking the transitive closure of the union of the referent fields.
    let reachableNestedTypes = ^(borrow_referent_type + borrow_mut_referent_type) | {
        // The nesting depth of both types is the same
        // NOTE: This is necessary since we quantify over all nested types in t1 below and match
        // them to types in t2, which could still be satisfied if t2 was a superset of t1.
        #(t1.reachableNestedTypes) = #(t2.reachableNestedTypes)

        // For every nested type within t1
        all nestedType1: Type | (nestedType1 in t1.reachableNestedTypes) => {
            // There is some corresponding nested type within t2, such that
            some nestedType2: Type | {
                nestedType2 in t2.reachableNestedTypes

                // The nested types match on the surface (same kind of borrow, or both owned)
                surfaceTypeMatches[nestedType1, nestedType2]

                // The nesting depth is the same (they are at the same "position" in the type)
                #(nestedType1.reachableNestedTypes) = #(nestedType2.reachableNestedTypes)
            }
        }
    }
}

// Determines if the given value has the given type.
pred valueHasType[value: Value, type: Type] {
    // Owned values: Only need to match at the surface level
    (isOwned[value] and isOwnedType[type]) or
    // Borrows: The value should be a borrow and the variable it was constructed from 
    // must have a type that matches the referent part of the given type.
    {
        isBorrow[value] 
        isBorrowType[type] 
        sameType[(value.borrow_referent).variable_type, type.borrow_referent_type]
    } or
    // Mutable borrows: Same as borrows
    {
        isBorrowMut[value] 
        isBorrowMutType[type] 
        sameType[(value.borrow_mut_referent).variable_type, type.borrow_mut_referent_type]
    }
}

// Checks the program for type errors.
pred passesTypeCheck {
    // No cycles: No type can reach itself
    no type: Type | reachable[type, type, borrow_referent_type, borrow_mut_referent_type]

    // All initializations / updates / moves into a variable must use a value 
    // that matches the annotated type of the variable.
    all variable: Variable, value: Value, assignment: Statement | {
        (assignsToVar[assignment, variable] and valueFromAssignment[assignment, value]) => {
            valueHasType[value, variable.variable_type]
        }
    }
}

// Ensures that the chain of values connected by the `borrow_referent_value` and 
// `borrow_mut_referent_value` fields is properly constrained.
pred validBorrowChain {
    // For all borrows, consider the statement that creates the borrow
    all borrow: Value, pointOfCreation: Statement | (!isOwned[borrow] and valueCreated[pointOfCreation, borrow]) => {
        let ref = referent[borrow] | {
            let refValue = referentValue[borrow] | {
                // If the referent variable of this borrow has some value at the point when the
                // borrow is constructed, the borrow referent value field should take that value.
                // Otherwise, the field should be none.
                (some v: Value | variableHasValueAtStmt[pointOfCreation, ref, v]) => {
                    some refValue
                    variableHasValueAtStmt[pointOfCreation, ref, refValue]
                } else {
                    no refValue
                }
            }
        }
    }
}

// Determines if the target value is reachable via a chain of borrows from the start.
// I.e., You could dereference the start value some number of times to get to the target.
pred borrowReachable[target: Value, start: Value] {
    reachable[target, start, borrow_referent_value, borrow_mut_referent_value]
}

pred validProgramStructure {
    innerScopeValid
    sequentialStatements
    variableDeclThenInitThenUsed
    onlyMutateMutableVars
    onlyBorrowMutMutableVars
    allObjectsParticipating
    uniqueInitialization
    correctMoveValue
    passesTypeCheck
    validBorrowChain
}

// ============================== Lifetimes ==============================

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


// ============================== Borrow Checking ==============================

// Determines if the lifetimes of the given values have any overlap.
pred lifetimesOverlap[v1: Value, v2: Value] {
    isBetweenInclusive[v2.value_lifetime.begin, v1.value_lifetime.begin, v1.value_lifetime.end] or 
    isBetweenInclusive[v2.value_lifetime.end, v1.value_lifetime.begin, v1.value_lifetime.end] or 
    isBetweenInclusive[v1.value_lifetime.begin, v2.value_lifetime.begin, v2.value_lifetime.end] or 
    isBetweenInclusive[v1.value_lifetime.end, v2.value_lifetime.begin, v2.value_lifetime.end]
}

// Determines if the given statement happens during the lifetime of the value.
pred duringLifetime[statement: Statement, value: Value] {
    isBetweenInclusive[statement, value.value_lifetime.begin, value.value_lifetime.end]
}

// When there is an exclusive reference (&mut) to a variable, there can be 
// no other references (& or &mut) alive at the same time.
pred borrowMutsAreUnique {
    //if there is a borrow mut of a variable cannot have another borrow mut of that variable or a borrow of that variable
    all borrowMut: BorrowMut | {
        //this is during their lifetime 
        no otherBorrowMut: BorrowMut | {
            lifetimesOverlap[borrowMut, otherBorrowMut]
            borrowMut != otherBorrowMut
            borrowMut.borrow_mut_referent = otherBorrowMut.borrow_mut_referent
        }
        no borrow: Borrow |  {
            lifetimesOverlap[borrowMut, borrow]
            borrowMut.borrow_mut_referent = borrow.borrow_referent
        }
    }
}

// - You cannot move out of or into a variable that is borrowed (either & or &mut)
// - You cannot mutate a variable that is borrowed (either & or &mut)
// cannot do a move or update statement where the borrowed variable is the source within the lifetme of the borrow of that variable
pred cannotChangeBorrowedVariable {
    //for every mutable borrow, no move or update of the referent within the lifetime of that borrow 
    all borrowMut: BorrowMut | {
        no statement: Statement | {
            duringLifetime[statement, borrowMut]
            variableModification[borrowMut.borrow_mut_referent, statement]
        }
    }
    // Likewise for borrows
    all borrow: Borrow | {
        no statement: Statement | {
            duringLifetime[statement, borrow]
            variableModification[borrow.borrow_referent, statement]
        }
    }
}


// Once you move out of a variable, you cannot use it (it becomes uninitialized),
// until it is reinitialized (if it is).
// Note that with borrows (shared references), a copy is performed and 
// the variable can still be used afterwards
// E.g.
// Variable2 = Box::new(());
// Variable3 = Variable2;
// // Now, Variable2 cannot be used (was moved out of)
// E.g.
// Variable1 = Box::new(());
// Variable2 = &mut Variable1;
// Variable3 = Variable2;
// // Now, Variable2 cannot be used (was moved out of)
pred cannotUseWhileUninitialized {
    // All reads of variables occur only while the variable is in an initialized state
    all readOfVar: Statement, variable: Variable | {
        readUseOfVariable[variable, readOfVar] => {
            some value: Value | variableHasValueAtStmt[readOfVar, variable, value]
        }
    }
}

// The lifetime of a borrow of a value must be contained within the lifetime of the value
pred borrowAliveDuringValueLifetime {
    // For any kind of borrow (& and &mut)
    all borrow: Value | {
        let referentVariable = referent[borrow] {
            some referentVariable => {
                // Find the statement where the borrow was created, and the value of the 
                // variable being borrowed at that point in the program.
                some pointOfCreation: Statement, referentValue: Value | {
                    valueCreated[pointOfCreation, borrow]
                    variableHasValueAtStmt[pointOfCreation, referentVariable, referentValue]

                    // The borrow's lifetime is within the lifetime of the referent value
                    duringLifetime[borrow.value_lifetime.begin, referentValue]
                    duringLifetime[borrow.value_lifetime.end, referentValue]
                }
            }
        }
    }
}

// Does the program pass the borrow checker.
pred satisfiesBorrowChecking {
    borrowMutsAreUnique
    cannotChangeBorrowedVariable
    cannotUseWhileUninitialized
    borrowAliveDuringValueLifetime
}

inst optimizer_9statement {
    Program = `Program0
    Statement in `Statement0 + `Statement1 + `Statement2 + `Statement3 +
                 `Statement4 + `Statement5 + `Statement6 + `Statement7 + 
                 `Statement8
    -- Manually break the symmetry on which statement is first; if there is one,
    -- it is always `Statement0.
    program_start in `Program0 -> `Statement0 
    -- Manually break the symmetry on which statement follows another. 
    --   (I don't think it would be safe to have just a linear order as the
    --    upper bound? So this just forces the "next" statement to be later 
    --    in our enumeration.)
    next in `Statement0->(`Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8) +
            `Statement1->(`Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement2->(`Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement3->(`Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement4->(`Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement5->(`Statement6 + `Statement7 + `Statement8)+
            `Statement6->(`Statement7 + `Statement8)+
            `Statement7->`Statement8 + 
            `Statement8->none
    inner_scope in `Statement0->(`Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8) +
            `Statement1->(`Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement2->(`Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement3->(`Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement4->(`Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement5->(`Statement6 + `Statement7 + `Statement8)+
            `Statement6->(`Statement7 + `Statement8)+
            `Statement7->`Statement8 + 
            `Statement8->none
}

// Programs that do NOT borrow check
// run {
//     validProgramStructure
//     lifetimesCorrect
//     not satisfiesBorrowChecking
// } 
// for exactly 6 Statement, 3 Variable, 3 Value
// for optimizer_9statement 

run {
    validProgramStructure
    lifetimesCorrect

    borrowMutsAreUnique
    not cannotChangeBorrowedVariable
    cannotUseWhileUninitialized
    borrowAliveDuringValueLifetime
} 
for exactly 8 Statement, 5 Int //, 3 Variable, 3 Value
for optimizer_9statement 

