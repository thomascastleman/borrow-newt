#lang forge "final" "jWRoVmMudTkyxClS"

// Predicates that enforce compliance with the borrow checking rules. These 
// can be used to find both valid and invalid programs.

open "sigs.frg"
open "util.frg"

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