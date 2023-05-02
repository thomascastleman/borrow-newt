#lang forge "final" "jWRoVmMudTkyxClS"

open "main.frg"

test suite for lifetimesCorrect {
    test expect {
        // Finding a valid program with correct lifetimes is satisfiable (vacuity check)
        lifetimesCorrectVacuity: {
            validProgramStructure
            lifetimesCorrect
        } is sat

        // The start of a lifetime must be before (or equal to) the end
        lifetimeStartBeforeEnd: {
            (validProgramStructure and lifetimesCorrect) => {
                all lifetime: Lifetime | {
                    isBefore[lifetime.begin, lifetime.end] or
                    lifetime.begin = lifetime.end
                }
            }
        } is theorem
    }

    // example trickyBorrowLifetime is {validProgramStructure lifetimesCorrect} for {
    //     // Tricky case for & borrow lifetimes (specifically end of lifetime)
    //     // let mut a = 0;
    //     // let b = &a;
    //     // let c = b;
    //     // a = 1;
    //     // println!("{}", c);  // &a is still alive because c made a copy    

    //     // Written in our subset of Rust:
    //     // let mut a;   Statement0
    //     // a = Value0   Statement1
    //     // let b;       Statement2
    //     // b = &a;      Statement3
    //     // let c;       Statement4
    //     // c = 0;
    //     // c = b;       Statement5
    //     // a = 1;       Statement6
    //     // move(c);     Statement7

    //     Statement = `Statement0 + `Statement1 + `Statement2 + `Statement3 + 
    //         `Statement4 + `Statement5 + `Statement6 + `Statement7;

    //     next = `Statement1 -> `Statement2 + 
    //         `Statement3 -> `Statement4 + 
    //         `Statement5 -> `Statement6 + 
    //         `Statement6 -> `Statement7

    //     inner_scope = `Statement0 -> `Statement1 +
    //         `Statement2 -> `Statement3 +
    //         `Statement4 -> `Statement5    

    //     Value = `Value0 + `Value1 + `Value2;

    //     Lifetime = `Lifetime0 + `Lifetime1 + `Lifetime2

    //     value_lifetime = `Value0 -> `Lifetime0 + 
    //         `Value1 -> `Lifetime1 + 
    //         `Value2 -> `Lifetime2    

    //     Mutable = `Mutable0

    //     Variable = `Variable0 + `Variable1 + `Variable2 

    //     declared_variable = `Statement0 -> `Variable0 +
    //         `Statement2 -> `Variable1 +
    //         `Statement4 -> `Variable2

    //     initialized_variable = `Statement1 -> `Variable0 +
    //         `Statement3 -> `Variable1
    // }
}