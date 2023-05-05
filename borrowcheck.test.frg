#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"

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

test suite for satisfiesBorrowChecking {
    test expect {
        // Vacuity check for borrow checking - is it even satisfiable
        borrowCheckVacuity: {
            validAndBorrowChecks
        } 
        for 7 Statement
        is sat

        // Important to also check that it is possible to *fail* borrow checking for otherwise valid programs.
        borrowCheckFailVacuity: {
            validAndFailsBorrowCheck
        }
        for 7 Statement
        is sat

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
        is unsat 

        // TODO: Other property tests
    }
}