#lang forge "final" "jWRoVmMudTkyxClS"

one sig Program {
    program_start: lone Statement
}

// A lifetime describes a region of the program for which a value is "live" (in use).
sig Lifetime {
    // TODO: Decide what these bounds mean (inclusive/exclusive)
    begin: one Statement,
    end: one Statement
}

one sig Mutable {}

// A variable represents a 'place' where a value can be stored.
sig Variable {
    // Whether this variable is being declared as mutable or not.
    mutable: lone Mutable
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
    value_lifetime: one Lifetime
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
    next: lone Statement,
    
    //Only used for DeclareVariable and Scope statements
    enter_scope: lone Statement,

    // Only used for statements occurring at the end of a scope - this will point 
    // to the next statement outside the scope(s).
    exit_scope: lone Statement
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

// A block statement, which creates a new scope.
sig CurlyBraces extends Statement {}


// Determines if there is a path through the program from the start statement
// to the target statement, by following either the sequence of statements or 
// stepping into inner scopes.
pred statementReachable[target: Statement, start: Statement] {
    // The target is reachable by following either next (for sequential statements),
    // variable_scope_start (for inner scopes of variable declarations), or
    // curly_braces_start (for other inner scopes).
    reachable[target, start, next, enter_scope, exit_scope]
}

// Determines if target is reachable from start by only following next (sequential
// statements) and enter_scope (for going into nested scopes).
pred statementReachableNoExit[target: Statement, start: Statement] {
    reachable[target, start, next, enter_scope]
}


// ============================== Program Structure ==============================

// All statements in the program (including nested scopes) follow a linear structure.
pred sequentialStatements[p: Program] {
    // There are no cycles in the chain of statements (no statement is reachable from itself)
    no s: Statement | statementReachable[s, s]

    // All statements are part of the program (reachable from the program start)
    all s: Statement | (s != p.program_start => statementReachable[s, p.program_start])
}

// Determines if the given variable is being "used" in the given statement.
// NOTE: Excludes declaration and initialization, because if initializing 
// is considered use, and use before initialization is illegal, then 
// you can never initialize.
pred variableUse[variable: Variable, statement: Statement] {
    statement.updated_variable = variable or    // Being reassigned to
    statement.source = variable or              // Being moved out of
    statement.destination = variable            // Being moved into
}

// Checks that variable use is preceded by initialization and declaration.
pred variableDeclThenInitThenUsed[p: Program] {
    all v: Variable | {
        some decl: DeclareVariable, init: InitializeVariable | {
            decl.declared_variable = v      // v is declared
            init.initialized_variable = v   // v is initialized

            // The initialization is in the scope of this variable.
            // NOTE: This is necessary in addition to the above constraint, 
            // because initializations are not considered uses.
            statementReachableNoExit[init, decl]

            all use: Statement | variableUse[v, use] implies {
                // Use is preceded by initialization
                statementReachable[use, init]

                // All uses of the variable are within the scope of that variable
                // NOTE: We use NoExit here, because we do not want to exit scopes 
                // when finding a path from declaration to use.
                statementReachableNoExit[use, decl]
            }
        }
    }
}

// Variables that are mutated must be declared mutable.
pred onlyMutateMutableVars[p: Program] {
    //for all variables such that there is some update of it implies it was mutable 
    all v: Variable | {
        (some update: UpdateVariable | update.updated_variable = v) => some v.mutable
    }
}

// TODO: Variable declarations should be unique
// TODO: Initialization should be unique
// TODO: every variable should be declared 
// TODO: constrain enter and exit scope

pred validProgramStructure[p: Program] {
    sequentialStatements[p]
    variableDeclThenInitThenUsed[p]
    onlyMutateMutableVars[p]
}
// TODO: declare variable cannot have a next

// ============================== Lifetimes ==============================

// Enforces that all lifetimes have been determined following the rules.
// NOTE: This does NOT check that the program borrow checks, but only ensures
// that the lifetimes are correct so that they may be used in analysis.
pred lifetimesCorrect[p: Program] {
    // TODO: 
    // - Go through all values to check values lifetimes (Owned, Borrow, Borrow Mut)
    // - Lifetimes should be unique (not shared between multiple values)
}

// For owned values, the lifetime extends from initialization until either:
//   - The value is moved
//   - The holding variable is assigned to again
//   - The holding variable goes out of scope
pred ownedLifetimes[o: Owned] {
    // TODO:
}

pred borrowLifetimes[b: Borrow] {
    // TODO:
}

pred borrowMutLifetimes[bm: BorrowMut] {
    // TODO:
}

// ============================== Borrow Checking ==============================

// TODO: Add predicates for these rules
// Borrow checking rules:
// - When there is an exclusive reference (&mut) to a variable, there can be 
//   no other references (& or &mut) alive at the same time.
// - As many shared references (&) as you want can coexist at the same time.
// - You cannot move out of a variable that is borrowed (either & or &mut)
// - You cannot mutate a variable that is borrowed (either & or &mut)
// - Once you move out of a variable, you cannot use it (it becomes uninitialized)
// - You can only construct an exclusive reference (&mut) to a variable that is declared mut

// TODO: Maybe add some predicates to eliminate extraneous sigs from the instances,
// for instance, variable/lifetimes floating around that aren't part of the program.

run {
    validProgramStructure[Program]
} for exactly 1 Program