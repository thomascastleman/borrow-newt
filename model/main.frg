#lang forge "final" "jWRoVmMudTkyxClS"

open "sigs.frg"
open "optimizers.frg"
open "structure.frg"
open "lifetimes.frg"
open "borrowcheck.frg"

// Programs that DO borrow check
run {
    validProgramStructure
    lifetimesCorrect
    satisfiesBorrowChecking
} 
for exactly 6 Statement, 3 Variable, 3 Value
for optimizer_9statement 

// Programs that do NOT borrow check
// run {
//     validProgramStructure
//     lifetimesCorrect
//     not satisfiesBorrowChecking
// } 
// for exactly 6 Statement, 3 Variable, 3 Value
// for optimizer_9statement 
