#lang forge "final" "jWRoVmMudTkyxClS"

one sig Program {
    first_statement: lone Statement
}

// A lifetime describes a region of the program for which a value is "live" (in use).
sig Lifetime {
    begin: one Statement,
    end: one Statement
}

// A variable represents a 'place' where a value can be stored.
sig Variable {
    // Whether this variable is being declared as mutable or not.
    mutable: lone Mutable,
    var_lifetime: one Lifetime
}

// ============================== Values ==============================

abstract sig Value {
    // For owned values, the lifetime extends from 
    // initialization until either:
    //   - The value is moved
    //   - The holding variable is assigned to again
    //   - The holding variable goes out of scope
    // 
    // For borrows, the lifetime extends from the point of 
    // creation until the last use of the reference.
    val_lifetime: one Lifetime
}

sig Owned extends Value {}
sig Borrow extends Value {
    borrow_referent: one Variable 
}
sig BorrowMut extends Value {
    borrow_mut_referent: one Variable 
}

// ============================== Statements ==============================

abstract sig Statement {
    // Each Statement has a link to the Statement that follows it. Statements
    // appearing at the end of scopes will have no `next`.
    next: lone Statement
}

one sig Mutable {}

// A variable declaration. E.g., `let a;`
sig DeclareVariable extends Statement {
    // The variable being declared
    declared_variable: one Variable,
    // The scope is the sequence of Statements for which the variable is valid.
    // NOTE: This is the first statement of that sequence, which links to the next, etc.
    variable_scope: lone Statement
}

// A variable initialization to some value. E.g. `a = &b;`
sig InitializeVariable extends Statement {
    initialized_variable: one Variable,
    initial_value: one Value
}

// Setting a mutable variable to some new value. E.g. `a = Box::new(());` where 
// a has previously been initialized.
// NOTE: Only valid for variables declared mut
sig UpdateVariable extends Statement {
    updated_variable: one Variable,
    new_value: one Value
}

sig Move extends Statement {
    // The value being moved
    moved_value: one Value,
    // The variable that is being moved out of.
    source: one Variable,
    // The destination is the variable to which ownership of this value is
    // begin transferred. If there is no destination, this indicates the value
    // is being moved to another function.
    destination: lone Variable
}

sig Scope extends Statement {
    statement: lone Statement
}


// Thomas
pred statementReachable[to: Statement, from: Statement] {
    // TODO:
}

// ============================== Program Structure ==============================

// All statements in the program (including nested scopes) follow a linear structure.
//Ria
pred sequentialStatements[p: Program] {
    // TODO:
}

// Checks that variable use is preceded by initialization and declaration.
// Thomas
pred varInitAndDecl[p: Program] {
    // TODO:
}

// Variables that are mutated must be declared mutable.
//Ria
pred onlyMutateMutableVars[p: Program] {
    // TODO:
}

pred validProgramStructure[p: Program] {
    sequentialStatements[p]
    varInitAndDecl[p]
    onlyMutateMutableVars[p]
}

// ============================== Borrow Checking ==============================


pred lifetimesCorrect[p: Program] {
    // TODO: 
}

// TODO: Add predicates for these rules
// Borrow checking rules:
// - When there is an exclusive reference (&mut) to a variable, there can be 
//   no other references (& or &mut) alive at the same time.
// - As many shared references (&) as you want can coexist at the same time.
// - You cannot move out of a variable that is borrowed (either & or &mut)
// - You cannot mutate a variable that is borrowed (either & or &mut)
// - Once you move out of a variable, you cannot use it (it becomes uninitialized)
// - You can only construct an exclusive reference (&mut) to a variable that is declared mut


run {
    validProgramStructure[Program]
} for exactly 1 Program, exactly 2 Statement
