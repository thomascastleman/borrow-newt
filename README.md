# borrow-newt

![A Borrow Newt](/borrow-newt.png)

A Forge model of Rust borrow checking for CSCI1710: Logic for Systems.

By Ria Rajesh and Thomas Castleman.

TODO: Describe model structure / what was proved.

The [Rust programming language](https://www.rust-lang.org/) is a language aiming to target the same space as C/C++, but with stronger guarantees around memory safety. It does so through a system of rules (known as "borrow checking") which govern how resources are passed around and ultimately destroyed. This project models these borrow checking rules to produce instances of Rust programs (for a very small subset of the language) that follow or violate these rules.

## Tradeoffs

- What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

Our representation relies heavily on the sigs we defined to represent different parts of a program. We represent core components of a program usings Sigs such as Values, Variables, and Statements. One tradeoff we made was that we do not assign each variable a value, because their value can change throughout the program. This affected the way we wrote our predicates, because we had to find the value that a variable would have at a given point using predicates rather than a sig field. Another tradeoff we made was how we modeled control flow and nested scopes. Each statement can have a next or an inner scope (or both) which models the sequence of statements and nesting that occurs. When we have statements within an inner scope their lifetime will end once we exit that scope. A tradeoff we made was that we do not have a field "exit scope" and this affected how we determined reachability. The combination of using next and inner scope creates a tree-like structure rather than a linear sequence of statements. To determine ordering and if one statement was reachable from another we needed to find a common ancestor statement

## Scope & Limits

- What assumptions did you make about scope? What are the limits of your model?

  - Discuss how we model only a subset of the kinds of operations you can do in Rust
  - Limitations around efficiency and number of statements

## Goals

- Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

## Understanding Instances

- How should we understand an instance of your model and what your custom visualization shows?

Each instance of our model represents a program in the Rust programming language. The custom
visualization script visualizes these instances as the text of the corresponding Rust program
being represented, with additional information about lifetimes annotated.

We use colored bounding boxes to visualize the lifetime of each value in the program, which
is the region of the program for which that value is considered to be valid or "alive."

TODO: Screenshots of visualization of some instances
