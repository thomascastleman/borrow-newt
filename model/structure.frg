#lang forge "final" "jWRoVmMudTkyxClS"

// Predicates that enforce the structure of valid Rust programs (modulo borrow checking).
// This includes constrains around how statements fit together, mutation, variable scope
// & initialization, and type checking.

open "sigs.frg"
open "util.frg"

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

// Does the instance satisfy valid structure?
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