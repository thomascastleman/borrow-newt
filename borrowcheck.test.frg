#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"
open "optimizers.frg"

pred validAndBorrowChecks {
    validProgramStructure
    lifetimesCorrect
    satisfiesBorrowChecking
}

pred validAndFailsBorrowCheck {
    validProgramStructure
    lifetimesCorrect
    not satisfiesBorrowChecking
}

pred sameReferent[borrow1: Value, borrow2: Value] {
    let referent1 = referent[borrow1] | {
        let referent2 = referent[borrow2] | {
            some referent1
            referent1 = referent2
        }
    }
}

pred useWhileUninit {
    some statement: Statement, variable: Variable | {
        // The statement reads the variable
        readUseOfVariable[variable, statement]
        // The variable has no value at this statement
        no value: Value | variableHasValueAtStmt[statement, variable, value]
    }
}

pred borrowOutlivesValue {
    some borrow: Value, referentValue: Value | {
        isBorrow[borrow] or isBorrowMut[borrow]

        some borrowCreation: Statement | {
            valueCreated[borrowCreation, borrow]
            variableHasValueAtStmt[borrowCreation, referent[borrow], referentValue]
        }

        not {
            duringLifetime[borrow.value_lifetime.begin, referentValue]
            duringLifetime[borrow.value_lifetime.end, referentValue]
        }
    }
}

pred modificationWhileBorrowed {
    some modification: Statement, borrow: Value | {
        isBorrow[borrow] or isBorrowMut[borrow]
        variableModification[referent[borrow], modification]
        duringLifetime[modification, borrow]
    }
}

test suite for satisfiesBorrowChecking {
    test expect {
        // // Vacuity check for borrow checking - is it even satisfiable
        // borrowCheckVacuity: {
        //     validAndBorrowChecks
        // } 
        // for 7 Statement
        // for optimizer_7statement
        // is sat

        // // Important to also check that it is possible to *fail* borrow checking for otherwise valid programs.
        // borrowCheckFailVacuity: {
        //     validAndFailsBorrowCheck
        // }
        // for 7 Statement
        // for optimizer_7statement
        // is sat

        // FIXME: This has UNSAT result, but this should satisfy it:
        // let a;
        // a = Box::new(0)
        // let b; 
        // b = &a;
        // let c;
        // c = &a;
        // drop(b);

        // Multiple borrows (&) of a given variable can exist at the same time.
        // This checks that we didn't overconstrain borrow checking to prevent
        // multiple shared references.
        multipleBorrowsValid: {
            validAndBorrowChecks

            // At least two borrows of the same variable exist at the same time 
            some disj borrow1, borrow2: Borrow | {
                borrow1.borrow_referent = borrow2.borrow_referent
                lifetimesOverlap[borrow1, borrow2]
            }
        }
        for 7 Statement
        for optimizer_7statement
        is sat 

        // It is invalid to have any other kind of borrow of some variable while there is a 
        // mutable borrow (&mut) to it that is alive.
        otherBorrowAliveDuringBorrowMutInvalid: {
            validAndBorrowChecks

            some disj borrowMut: Value, otherBorrow: Value | {
                some borrowMut.borrow_mut_referent
                sameReferent[borrowMut, otherBorrow]
                lifetimesOverlap[borrowMut, otherBorrow]
            }
        }
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Without borrow checking, it is possible to use a variable after moving it
        useWhileUninitPossible: {
            validAndFailsBorrowCheck
            useWhileUninit 
        }
        for 7 Statement
        for optimizer_7statement
        is sat

        // Borrow checking prevents using a variable that has been moved out of
        useWhileUninitPrevented: {
            validAndBorrowChecks
            useWhileUninit
        }
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Without borrow checking, a borrow that outlives the value it references is possible
        borrowOutlivesValuePossible: {
            validAndFailsBorrowCheck
            borrowOutlivesValue
        }
        for 7 Statement
        for optimizer_7statement
        is sat

        // With borrow checking, a borrow cannot outlive its referent.
        borrowOutlivesValuePrevented: {
            validAndBorrowChecks
            borrowOutlivesValue
        }
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Without borrow checking, you can mutate a variable while it is borrowed
        mutateWhileBorrowedPossible: {
            validAndFailsBorrowCheck
            modificationWhileBorrowed
        }
        for 7 Statement
        for optimizer_7statement
        is sat

        // Borrow checking prevents mutation while borrowed
        mutateWhileBorrowedPrevented: {
            validAndBorrowChecks
            modificationWhileBorrowed
        }
        for 7 Statement
        for optimizer_7statement
        is unsat

        // Use of value after end of lifetime is unsat
        useOfValAfterEndOfLife: {
            validAndBorrowChecks
            some endStatement: Statement, value: Value, lastVar: Variable | {
                lastVariable[lastVar, value]
                lastUseOfVarWithValue[endStatement, lastVar, value]
                isBefore[value.value_lifetime.end, endStatement]
            }
        }
        for 7 Statement
        for optimizer_7statement
        is unsat
    }
}