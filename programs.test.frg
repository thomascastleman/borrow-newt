#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"

test suite for isBefore {
    test expect {
        // No statement is before itself
        notBeforeSelf: {
            validProgramStructure => {
                no s: Statement | isBefore[s, s]
            }
        } 
        for 7 Statement
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
        is unsat

        // Cannot mutate a variable not marked as mutable
        mutateImmutable: {
            validProgramStructure

            some update: UpdateVariable | {
                no update.updated_variable.mutable
            }
        } 
        for 7 Statement
        is unsat
    }
}