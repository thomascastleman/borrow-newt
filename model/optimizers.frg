#lang forge "final" "jWRoVmMudTkyxClS"

// Partial instances that break symmetry around the ordering of statements, in an effort to improve performance.

open "sigs.frg"

// Partial instance optimizer for 7 statements
inst optimizer_7statement {
    Program = `Program0
    Statement in `Statement0 + `Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6
    // Manually break the symmetry on which statement is first; if there is one, it is always `Statement0.
    program_start in `Program0 -> `Statement0
    // Manually break the symmetry on which statement follows another.
    next in
        `Statement0->(`Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6) +
        `Statement1->(`Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6) +
        `Statement2->(`Statement3 + `Statement4 + `Statement5 + `Statement6) +
        `Statement3->(`Statement4 + `Statement5 + `Statement6) +
        `Statement4->(`Statement5 + `Statement6) +
        `Statement5->(`Statement6) +
        `Statement6->(none)
    inner_scope in
        `Statement0->(`Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6) +
        `Statement1->(`Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6) +
        `Statement2->(`Statement3 + `Statement4 + `Statement5 + `Statement6) +
        `Statement3->(`Statement4 + `Statement5 + `Statement6) +
        `Statement4->(`Statement5 + `Statement6) +
        `Statement5->(`Statement6) +
        `Statement6->(none)
}

// Partial instance optimizer for 9 statements
inst optimizer_9statement {
    Program = `Program0
    Statement in `Statement0 + `Statement1 + `Statement2 + `Statement3 +
                 `Statement4 + `Statement5 + `Statement6 + `Statement7 + 
                 `Statement8
    // Manually break the symmetry on which statement is first; if there is one, it is always `Statement0.
    program_start in `Program0 -> `Statement0 
    // Manually break the symmetry on which statement follows another. 
    next in `Statement0->(`Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8) +
            `Statement1->(`Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement2->(`Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement3->(`Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement4->(`Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement5->(`Statement6 + `Statement7 + `Statement8)+
            `Statement6->(`Statement7 + `Statement8)+
            `Statement7->`Statement8 + 
            `Statement8->none
    inner_scope in `Statement0->(`Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8) +
            `Statement1->(`Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement2->(`Statement3 + `Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement3->(`Statement4 + `Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement4->(`Statement5 + `Statement6 + `Statement7 + `Statement8)+
            `Statement5->(`Statement6 + `Statement7 + `Statement8)+
            `Statement6->(`Statement7 + `Statement8)+
            `Statement7->`Statement8 + 
            `Statement8->none
}