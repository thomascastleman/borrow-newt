#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"

test suite for satisfiesBorrowChecking {
    // Vacuity check for borrow checking - is it even satisfiable
    borrowCheckVacuity: {
        validProgramStructure
        lifetimesCorrect
        satisfiesBorrowChecking
    } 
    for 7 Statement
    is sat


    // TODO: Property test for:
    // As many shared references (&) as you want can coexist at the same time.

    // TODO: Other property tests
}