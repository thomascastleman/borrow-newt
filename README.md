# borrow-newt

![A Borrow Newt](/images/borrow-newt.png)

A Forge model of Rust borrow checking for CSCI1710: Logic for Systems.

By Ria Rajesh and Thomas Castleman.

## Overview

The [Rust programming language](https://www.rust-lang.org/) is a language aiming to target the
same space as C/C++, but with stronger guarantees around memory safety. It does so through a system
of rules (known as "borrow checking") which govern how resources are passed around and ultimately
destroyed. This project models these borrow checking rules to produce instances of Rust programs
(for a very small subset of the language) that follow or violate these rules.

## Tradeoffs

Our representation relies heavily on the sigs we defined to represent different parts of a program.
We represent core components of a program usings Sigs such as Values, Variables, and Statements.
One tradeoff we made was that we do not assign each variable a value, because their value can
change throughout the program. This affected the way we wrote our predicates, because we had to
find the value that a variable would have at a given point using predicates rather than a sig field.

Another tradeoff we made was how we modeled control flow and nested scopes. Each statement can have
a next or an inner scope (or both) which models the sequence of statements and nesting that occurs.
When we have statements within an inner scope their lifetime will end once we exit that scope. A
tradeoff we made was that we do not have a field "exit scope", which would be a field pointing to
the next statement outside of the scope that we were in, and this affected how we determined
reachability. The combination of using next and inner scope creates a tree-like structure rather
than a linear sequence of statements. To determine ordering and if one statement was reachable
from another we needed to find a common ancestor statement, and determine reachability from that statement.

We also made a design choice to represent making smaller scopes within the larger program as
a CurlyBrace statement. This allows us to model nested lifetimes, which are relevant to the
borrow checking rules that we model. We chose to make this a kind of statement rather than a
different sig in order to be able to make use of the next and inner scope fields defined as
part of a statement, which allowed us to better represent the program sequence.

## Scope & Limits

To limit the scope of the project, we chose to only model a small subset of Rust. The
types of statements represented in our model are variable declarations, assignment
(to a new value or to another variable's value), and explicit scopes created by braces.
Modeling the entirety of the language would be a significant undertaking that
would present a challenge given the timeframe of this project. We also limited the types
of values and kinds of statements seen in the program in order to maintain simplicity.
For example, we only have one type of owned value represented in our programs.

Due to efficiency limitations of Forge, the largest number of statements we have
been able to achieve in instances and test cases is 8. Despite this, there are a
significant number of non-trivial programs that can be represented with this many
statements.

## Goals

We were able to successfully complete our foundation and target goal outlined in our proposal. Our
foundation goal was to be able to model a Rust program that follows rules of valid program structure,
including: appropriate syntax, having variables declared, initialized, then used, curly braces forming
scopes, and enforcing type checking for variables and values assigned to them.

Our target goal was to model the borrow checking rules in Rust, and we were able to do this by
determining valid lifetimes for values, and expressing the rules in terms of these lifetimes.

Our reach goal was to model properties related to memory safety, such as uninitialized memory, dangling
pointers, or memory leaks, and to verify whether or not the borrow checking rules prevent such bugs. We
are able to express one of these scenarios under the current model: whether it is possible to create
a dangling pointer under borrow checking. Other, more complicated properties, however, might require
additional changes to the model.

## Understanding Instances

Each instance of our model represents a program in the Rust programming language. The custom
visualization script visualizes these instances as the text of the corresponding Rust program
being represented, with additional information about lifetimes annotated.

We use colored bounding boxes to visualize the lifetime of each value in the program, which
is the region of the program for which that value is considered to be valid or "alive."

The visualization can also display labels in a column alongside the program, which indicates
which statement/value objects correspond to each visualized line. This is useful for debugging,
as it allows you to reference specific statements/values in the evaluator.

### Example Instance 1

![](/images/owned-value-overwritten.png)

The lifetime of Value2 (an owned value) is illustrated in green, and the lifetime of Value1 (another
owned value) is in blue. Value1's lifetime ends due to its holding variable (v1) being overwritten at Statement6.

### Example Instance 2

![](/images/move-while-borrowed.png)

In this example, Value1 is borrowed by Value2. The usage of v1, the holding variable for Value2, at
Statement8 extends the lifetime of Value2 to this point. However, the lifetime of Value1 cannot
extend past the call to `drop(v2)` at Statement7.

Indeed, rustc rejects this program:

```
error[E0505]: cannot move out of `v2` because it is borrowed
 --> src/main.rs:8:18
  |
2 |     let mut v2: Box<i32>;
  |         ------ binding `v2` declared here
...
7 |             v1 = &mut v2;
  |                  ------- borrow of `v2` occurs here
8 |             drop(v2);
  |                  ^^ move out of `v2` occurs here
9 |             drop(v1);
  |                  -- borrow later used here
```
