#lang forge "final" "jWRoVmMudTkyxClS"

// Signatures for the model, representing what kinds of objects can exist in an instance.

// The program indicates the entry point.
one sig Program {
    program_start: lone Statement
}

// A lifetime describes a region of the program for which a value is "live" (in use).
sig Lifetime {
    begin: one Statement,
    end: one Statement
}

// ============================== Types ==============================

abstract sig Type {}

sig OwnedType extends Type {}
sig BorrowType extends Type {
    borrow_referent_type: one Type
}
sig BorrowMutType extends Type {
    borrow_mut_referent_type: one Type
}

// ============================== Variables ==============================

one sig Mutable {}

// A variable represents a 'place' where a value can be stored.
sig Variable {
    // Whether this variable is being declared as mutable or not.
    mutable: lone Mutable,

    // The type of values this variable can hold.
    variable_type: one Type
}

// ============================== Values ==============================

abstract sig Value {
    value_lifetime: one Lifetime
}

sig Owned extends Value {}
sig Borrow extends Value {
    borrow_referent: one Variable,
    borrow_referent_value: lone Value
}
sig BorrowMut extends Value {
    borrow_mut_referent: one Variable,
    borrow_mut_referent_value: lone Value
}

// ============================== Statements ==============================

abstract sig Statement {
    // Each Statement has a link to the Statement that follows it. Statements
    // appearing at the end of scopes will have no `next`.
    next: lone Statement,
    
    // Only used for DeclareVariable and CurlyBraces statements
    inner_scope: lone Statement
}

// A variable declaration. E.g., `let a;`
sig DeclareVariable extends Statement {
    // The variable being declared
    declared_variable: one Variable
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

sig MoveOrCopy extends Statement {
    // The value being moved
    moved_value: one Value,
    // The variable that is being moved out of.
    source: one Variable,
    // The destination is the variable to which ownership of this value is
    // begin transferred. If there is no destination, this indicates the value
    // is being moved to another function.
    destination: lone Variable
}

// A block statement, which creates a new scope.
sig CurlyBraces extends Statement {}
