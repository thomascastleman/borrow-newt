#lang forge "final" "jWRoVmMudTkyxClS"

open "../model/sigs.frg"
open "../model/optimizers.frg"
open "../model/util.frg"
open "../model/structure.frg"

test suite for isBefore {
    test expect {
        // No statement is before itself
        notBeforeSelf: {
            validProgramStructure => {
                no s: Statement | isBefore[s, s]
            }
        } 
        for 7 Statement
        for optimizer_7statement
        is theorem

        // It is impossible for s1 to be before s2 AND s2 also be before s1.
        notBothBefore: {
            validProgramStructure => {
                all s1, s2: Statement | {
                    isBefore[s1, s2] => not isBefore[s2, s1]
                }
            }
        } 
        for 7 Statement
        for optimizer_7statement
        is theorem

        // If s1 is before s2, and s2 is before s3, s1 must be before s3.
        beforeIsTransitive: {
            validProgramStructure => {
                all s1, s2, s3: Statement | {
                    (isBefore[s1, s2] and isBefore[s2, s3]) => isBefore[s1, s3]
                }
            }
        } 
        for 7 Statement
        for optimizer_7statement
        is theorem
    }
}

test suite for validProgramStructure {
    test expect {
        // Finding a valid program is satisfiable (vacuity check)
        validProgramVacuity: {
            validProgramStructure
        } 
        for 7 Statement
        for optimizer_7statement
        is sat

        // Cannot use a variable before it is initialized
        varUsedBeforeInit: {
            validProgramStructure

            some init: InitializeVariable, use: Statement | {
                variableUse[init.initialized_variable, use]
                isBefore[use, init]
            }
        } 
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Cannot use a variable outside its scope
        varUsedOutOfScope: {
            validProgramStructure

            // Find a use of some variable...
            some variable: Variable, use: Statement | {
                variableUse[variable, use]

                // ...that is out of scope
                no decl: DeclareVariable | {
                    decl.declared_variable = variable
                    statementReachable[use, decl]
                }
            }
        }
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Check that the structure of nested scopes is properly constrained
        scopingIsCorrect: {
            validProgramStructure

            some outer: Statement, inner: Statement {
                // The outer statement has some nested scope
                some outer.inner_scope

                // The inner statement is within that nested scope
                statementReachable[inner, outer.inner_scope]

                // BAD: You can get to inner even after you've passed outer
                // (which should contain inner and be the only way to get to it).
                some outer.next and statementReachable[inner, outer.next]
            }
        } 
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Cannot mutate a variable not marked as mutable
        mutateImmutable: {
            validProgramStructure

            some update: UpdateVariable | {
                no update.updated_variable.mutable
            }
        } 
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Cannot create a mutable borrow to a variable not marked mutable
        borrowMutImmutableVar: {
            validProgramStructure
            some v: BorrowMut | {
                no v.borrow_mut_referent.mutable
            }
        }
        for 7 Statement
        for optimizer_7statement
        is unsat

        // All nested types must bottom out with some Owned type eventually
        allTypesBottomOut: {
            validProgramStructure => (all t: Type | {
                !isOwnedType[t] => (some ownedType: Type | {
                    reachable[ownedType, t, borrow_referent_type, borrow_mut_referent_type]
                })
            })
        } 
        for 7 Statement
        for optimizer_7statement
        is theorem

        // It is okay for types to be shared between variables (whether shared fully or in a nested way)
        // This allows us to keep the bounds on Type low while still allowing many possible types.
        sharingTypesValid: {
            validProgramStructure
            some disj v1, v2: Variable | {
                some sharedType: Type | {
                    sharedType = v1.variable_type or reachable[sharedType, v1.variable_type, borrow_referent_type, borrow_mut_referent_type]
                    sharedType = v2.variable_type or reachable[sharedType, v2.variable_type, borrow_referent_type, borrow_mut_referent_type]
                }
            }
        }
        for 7 Statement
        for optimizer_7statement
        is sat

        // Nested borrows must be created *after* the values they borrow.
        borrowReferentCreatedEarlier: {
            validProgramStructure => (all v1, v2: Value, v1Created, v2Created: Statement | {
                (borrowReachable[v1, v2] and valueCreated[v1Created, v1] and valueCreated[v2Created, v2]) => {
                    isBefore[v1Created, v2Created]
                }
            })
        }
        for 7 Statement
        for optimizer_7statement
        is theorem
    }
}
