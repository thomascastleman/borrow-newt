#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"

// Partial instance optimizer for 7 statements
inst optimizer_7statement {
    Program = `Program0
    Statement in `Statement0 + `Statement1 + `Statement2 + `Statement3 + `Statement4 + `Statement5 + `Statement6
    // Manually break the symmetry on which statement is first; if there is one,
    // it is always `Statement0.
    program_start in `Program0 -> `Statement0
    // Manually break the symmetry on which statement follows another.
    //   (I don't think it would be safe to have just a linear order as the
    //    upper bound? So this just forces the "next" statement to be later
    //    in our enumeration.)
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