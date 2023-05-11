#!/bin/env python3
# Script for generating partial instances for optimization.

import sys

if len(sys.argv) != 2:
    print(f"Usage: {sys.argv[0]} NUM-STATEMENTS")
    sys.exit(1)

NUMBER_OF_STATEMENTS = int(sys.argv[1])
assert NUMBER_OF_STATEMENTS > 0

def generate_statements_bound(start_number, end_number) -> str:
    statements = []
    for i in range(start_number, end_number): 
        statements.append(f"`Statement{i}")
    
    return " + ".join(statements)

def generate_next_and_inner_scope_bound() -> str:
    bounds = []

    for i in range(NUMBER_OF_STATEMENTS):
        statements_bound = generate_statements_bound(i + 1, NUMBER_OF_STATEMENTS)
        if statements_bound == "":
            statements_bound = "none"

        bounds.append(f"\n        `Statement{i}->({statements_bound})")

    return " + ".join(bounds)

PARTIAL_INSTANCE_TEMPLATE = """
// Partial instance optimizer for {0} statements
inst optimizer_{0}statement {{
    Program = `Program0
    Statement in {1}
    // Manually break the symmetry on which statement is first; if there is one, it is always `Statement0.
    program_start in `Program0 -> `Statement0 
    // Manually break the symmetry on which statement follows another. 
    next in {2}
    inner_scope in {2}
}}
"""

def generate_partial_instance() -> str:
    return PARTIAL_INSTANCE_TEMPLATE.format(
        NUMBER_OF_STATEMENTS, 
        generate_statements_bound(0, NUMBER_OF_STATEMENTS), 
        generate_next_and_inner_scope_bound())

print(generate_partial_instance())