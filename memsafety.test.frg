#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"
open "optimizers.frg"

// Determines if the instance contains a pointer that outlives the value it points to.
pred danglingPointer {
    some resource: Owned, pointer: Value | {
        isBorrow[pointer] or isBorrowMut[pointer]
        referentValue[pointer] = resource
        isBefore[resource.value_lifetime.end, pointer.value_lifetime.end]
    }
}

test expect {
    // It is not possible to create a dangling pointer under borrow checking.
    borrowCheckingPreventsDanglingPointers: {
        (validProgramStructure and lifetimesCorrect and satisfiesBorrowChecking) => {
            not danglingPointer
        }
    }
    for 7 Statement
    for optimizer_7statement
    is theorem
}