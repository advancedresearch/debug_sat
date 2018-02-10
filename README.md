# Debug-SAT

A debuggable automatic theorem prover for boolean satisfiability problems (SAT).

Brought to you by the [AdvancedResearch Community](https://advancedresearch.github.io/).

Designed for debugging and introspection rather than performance.

*NB! This library might contain bugs. Do not use in safety critical applications!*

This library can be used to:

- Learn basic logic theorem proving
- Design and verify boolean circuits
- Create machine checked proofs in propositional calculus for many variables
- Used as theorem prover assistant by using tactics step by step
- Optimize partial proofs by selecting from equivalent expressions

### How to use it

The `Graph::var` method adds a new variable.
Give it a unique id.

When creating a gate, you use the variables of previously created gates.

```rust
use debug_sat::Graph;

let ref mut graph = Graph::new();
let a = graph.var(0);
let b = graph.var(1);
let a_and_b = graph.and(a, b);
```

There is one method for the following 5 logical gates (selected for readability):

- AND
- OR
- NOT
- EQ
- IMPLY

Other gates are considered less readable, but can be created by combining these 5 gates.
For example, if you need XOR, use `not(eq(a, b))`.

By default, variables and expressions have no value, which are added by making assumptions.
An assumption is added to a history stack and can be undoed or inverted.

There are two kinds of assumptions: Equality and inequality.
Instead of saying that a variable `a` is `true`,
you say that `a` is equivalent to `true` or not equivalent to `false`.

The `Graph::are_eq` method is used to check the value of an variable or expression.

```rust
use debug_sat::Graph;

let ref mut graph = Graph::new();
let a = graph.var(0);
let tr = graph.true_();
let a_is_tr = graph.assume_eq(a, tr);
assert_eq!(graph.are_eq(a, tr), Some(true));
a_is_tr.undo(graph); // Alternative: `a_is_tr.invert(graph)`
```

When you add new stuff to the theorem prover, it does not automatically know the right answer.
This requires executing tactics or solving (runs all tactics).

```rust
use debug_sat::{Graph, Proof};

let ref mut graph = Graph::new();
let a = graph.var(0);
let b = graph.var(1);
let a_and_b = graph.and(a, b);
let a_is_b = graph.assume_eq(a, b);
// Does not know that `and(a, b) = a` when `a = b`.
assert_eq!(graph.are_eq(a_and_b, a), None);
// Run the tactic that checks input to AND is EQ.
// This is how the theorem prover learns, by checking stuff.
// Alternative: `graph.solve()` runs all tactics until nothing new is learned.
assert_eq!(graph.eq_and(a_and_b), Proof::True);
// Now the theorem prover knows the answer.
assert_eq!(graph.are_eq(a_and_b, a), Some(true));
```

For more information about tactics do, see the `Proof` enum.
