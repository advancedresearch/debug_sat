/*

Prove the following:

    A & B => A

This is proven by checking that `A` is true when `A & B` is true.

When `A & B` is false, the truth of the statement `A & B => A` is true,
so this case does not need to be checked.

*/

use debug_sat::*;

fn main() {
    let ref mut graph = Graph::new();
    let a = graph.var(0);
    let b = graph.var(1);
    let tr = graph.true_();
    let fa = graph.false_();

    let a_and_b = graph.and(a, b);
    let a_and_b_eq_tr = graph.assume_eq(a_and_b, tr);
    graph.solve();
    // Prints `Some(true)`
    println!("{:?}", graph.are_eq(a, tr));

    a_and_b_eq_tr.undo(graph);
    graph.solve();
    // Prints `None`
    println!("{:?}", graph.are_eq(a, tr));

    let a_and_b_eq_fa = graph.assume_neq(a_and_b, tr);
    graph.solve();
    println!("{:?}", graph.are_eq(a_and_b, fa));
    a_and_b_eq_fa.undo(graph);
}
