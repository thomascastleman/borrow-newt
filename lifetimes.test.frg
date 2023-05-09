#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"

test suite for lifetimesCorrect {
    test expect {
        //Finding a valid program with correct lifetimes is satisfiable (vacuity check)
        lifetimesCorrectVacuity: {
            validProgramStructure
            lifetimesCorrect
        } 
        for 7 Statement
        is sat

        // The start of a lifetime must be before (or equal to) the end
        lifetimeStartBeforeEnd: {
            (validProgramStructure and lifetimesCorrect) => {
                all lifetime: Lifetime | {
                    isBefore[lifetime.begin, lifetime.end] or
                    lifetime.begin = lifetime.end
                }
            }
        } 
        for 7 Statement
        is theorem

        // Every variable has at most one value at a given statement
        variablesHaveOneValueAtATime: {
            (validProgramStructure and lifetimesCorrect) => {
                all statement: Statement, variable: Variable | {
                    lone value: Value | {
                        variableHasValueAtStmt[statement, variable, value]
                    }
                }
            }
        }
        for 7 Statement
        is theorem

        // end of lifetime not always reachable from the beginning (if there is some nesting)
        nestedValueAssignment: {
            validProgramStructure
            lifetimesCorrect
            some lifetime: Lifetime | {
                not statementReachable[lifetime.end, lifetime.begin]
            }
        }
        for 7 Statement
        is sat

        // owned value is held after itslifetime ended is unsat
        valueAliveAfterEndOfLife: {
            // validAndBorrowChecks
            validProgramStructure
            lifetimesCorrect

            some endStatement: Statement, owned: Owned, lastVar: Variable | {
                lastVariable[lastVar, owned]
                variableHasValueAtStmt[endStatement, lastVar, owned]
                isBefore[owned.value_lifetime.end, endStatement]
            }
        }
        for 7 Statement
        is unsat
    }
}