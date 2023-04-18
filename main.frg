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
    // FIXME: I urge us to rename this field
    statement: lone Statement
}


// Determines if there is a path through the program from the start statement
// to the target statement, by following either the sequence of statements or 
// stepping into inner scopes.
pred statementReachable[target: Statement, start: Statement] {
    // The target is reachable by following either next (for sequential statements),
    // variable_scope (for inner scopes of variable declarations), or
    // statement (for other inner scopes).
    reachable[target, start, next, variable_scope, statement]
}

no cycles[s: Statement] {
    //no statement that is reachable from s and s is reachable from it (no cycles)
    no a: Statement | {
        reachable[s, a, next]
        reachable[a, s, next]
    }
}

// ============================== Program Structure ==============================

// All statements in the program (including nested scopes) follow a linear structure.
//Ria
pred sequentialStatements[p: Program] {
    // TODO: does it need to use is linear?
    no cycles[p.first_statement]
    all s: Statement | s in p.first_statement.next => {
        reachable[s, p.first_statement, next] //is this redundant idk @Thomas
        // //no statement that is reachable from s and s is reachable from it (no cycles)
        no cycles[s]
    }
    all scope_statement: Scope | scope_statement in p.first_statement.next => {
        no cycles[scope_statement.statement]
    }
    all var_dec: DeclareVariable | var_dec in p.first_statement.next => {
        no cycles[var_dec.variable_scope]
    }
}

// Enforces that all statements are part of the program (reachable from the program start).
pred allStatementsInProgram[p: Program] {
    all s: Statement | statementReachable[s, p.first_statement]
}

// Determines if the given variable is being "used" in the given statement.
// NOTE: Excludes declaration and initialization.
pred variableUse[variable: Variable, statement: Statement] {
    statement.updated_variable = variable or    // Being reassigned to
    statement.source = variable or              // Being moved out of
    statement.destination = variable            // Being moved into
}

// Checks that variable use is preceded by initialization and declaration.
pred variableDeclThenInitThenUsed[p: Program] {
    all v: Variable | {
        all use: Statement | variableUse[v, use] implies {
            some decl: DeclareVariable, init: InitializeVariable | {
                decl.declared_variable = v      // v is declared
                init.initialized_variable = v   // v is initialized
                statementReachable[init, decl]  // Initialization is preceded by declaration
                statementReachable[use, init]   // Use is preceded by initialization
            }
        }
    }
}

// Variables that are mutated must be declared mutable.
//Ria
pred onlyMutateMutableVars[p: Program] {
    // TODO:
    //for all variables such that there is some update of it implies it was mutable 
    //does this do what I think it does? @Thomas
    all v: Variable | {
        some update: UpdateVariable => some v.mutable
    }
}

pred validProgramStructure[p: Program] {
    allStatementsInProgram[p]
    sequentialStatements[p]
    variableDeclThenInitThenUsed[p]
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
    some v: Variable, s: Statement | variableUse[v, s]
} for exactly 1 Program