//! # Debug-SAT
//!
//! A debuggable automatic theorem prover for boolean satisfiability problems (SAT).
//!
//! Brought to you by the [AdvancedResearch Community](https://advancedresearch.github.io/).
//!
//! Designed for debugging and introspection rather than performance.
//!
//! *NB! This library might contain bugs. Do not use in safety critical applications!*
//!
//! This library can be used to:
//!
//! - Learn basic logic theorem proving
//! - Design and verify boolean circuits
//! - Create machine checked proofs in propositional calculus for many variables
//! - Used as theorem prover assistant by using tactics step by step
//! - Optimize partial proofs by selecting from equivalent expressions
//!
//! ### How to use it
//!
//! The `Graph::var` method adds a new variable.
//! Give it a unique id.
//!
//! When creating a gate, you use the variables of previously created gates.
//!
//! ```rust
//! use debug_sat::Graph;
//!
//! let ref mut graph = Graph::new();
//! let a = graph.var(0);
//! let b = graph.var(1);
//! let a_and_b = graph.and(a, b);
//! ```
//!
//! There is one method for the following 5 logical gates (selected for readability):
//!
//! - AND
//! - OR
//! - NOT
//! - EQ
//! - IMPLY
//!
//! Other gates are considered less readable, but can be created by combining these 5 gates.
//! For example, if you need XOR, use `not(eq(a, b))`.
//!
//! By default, variables and expressions have no value, which are added by making assumptions.
//! An assumption is added to a history stack and can be undoed or inverted.
//!
//! There are two kinds of assumptions: Equality and inequality.
//! Instead of saying that a variable `a` is `true`,
//! you say that `a` is equivalent to `true` or inequal to `false`.
//!
//! The `Graph::are_eq` method is used to check the value of an variable or expression.
//!
//! ```rust
//! use debug_sat::Graph;
//!
//! let ref mut graph = Graph::new();
//! let a = graph.var(0);
//! let tr = graph.true_();
//! let a_is_tr = graph.assume_eq(a, tr);
//! assert_eq!(graph.are_eq(a, tr), Some(true));
//! a_is_tr.undo(graph); // Alternative: `a_is_tr.invert(graph)`
//! ```
//!
//! When you add new stuff to the theorem prover, it does not automatically know the right answer.
//! This requires executing tactics or solving (runs all tactics).
//!
//! ```rust
//! use debug_sat::{Graph, Proof};
//!
//! let ref mut graph = Graph::new();
//! let a = graph.var(0);
//! let b = graph.var(1);
//! let a_and_b = graph.and(a, b);
//! let a_is_b = graph.assume_eq(a, b);
//! // Does not know that `and(a, b) = a` when `a = b`.
//! assert_eq!(graph.are_eq(a_and_b, a), None);
//! // Run the tactic that checks input to AND is EQ.
//! // This is how the theorem prover learns, by checking stuff.
//! // Alternative: `graph.solve()` runs all tactics until nothing new is learned.
//! assert_eq!(graph.eq_and(a_and_b), Proof::True);
//! // Now the theorem prover knows the answer.
//! assert_eq!(graph.are_eq(a_and_b, a), Some(true));
//! ```
//!
//! For more information about tactics do, see the `Proof` enum.
//!
//! ### Design
//!
//! Uses a graph that links expressions together.
//! Expressions that are grammatically identical has the same id.
//! Commutative operators are ordered on insertion of a new expression,
//! to make them trivial equivalent.
//! New expressions are never deleted from the graph, even after making new assumptions.
//! This does not affect soundness because expressions only have value by their constraints.
//!
//! Tactics are based on entangled functions under equality and inequality plus normal currying.
//! One nice mathematical property of entangled boolean functions of 2 arguments
//! is that every equality or inequality constraint reduces the function to 0 or 1 arguments.
//! This corresponds to natural deduction, so the tactics can be used for assisted theorem proving.
//! You can find more information about this in papers about entangled functions
//! in the research repository for [Path Semantics](https://github.com/advancedresearch/path_semantics).
//!
//! A first-order Havox diagram is used prove equality and inequality of expressions.
//! First order means it does not infer between edges.
//! Law of excluded middle is added as tactic to specialize inference on boolean logic.
//! Relations are stored on the current provable minimum ids in the moment of insertion.
//! This solves a soundness problem when searching for representatives for equivalence classes
//! (not sure why it works at this moment, but believe it got something to with ordering the relations).
//! It also accelerates proof of inequality since these relations are often looked up directly.
//! For more information about Havox diagrams, see papers about Havox diagrams
//! in the research repostiory for [Path Semantics](https://github.com/advancedresearch/path_semantics).

#![cfg_attr(test, feature(test))]
#![deny(missing_docs)]

use std::collections::HashMap;
use std::cell::RefCell;

/// Binds expressions together with constraints and acceleration data structures.
///
/// Exposes members to allow advanced introspection.
#[derive(Clone)]
pub struct Graph {
    /// Expression nodes.
    pub exprs: Vec<Expression>,
    /// Equality and inequality constraints.
    pub havox: HashMap<(usize, usize), bool>,
    /// Contains a map to look up index of expressions.
    pub map: HashMap<Expression, usize>,
    /// Used to keep track of assumptions.
    /// Changes to the havox diagram are recorded to roll back to moment
    /// right before assumption being made.
    pub history: Vec<(usize, usize)>,
    /// Caches minimum id for equivalence classes.
    pub cache: RefCell<Vec<Option<usize>>>,
}

impl Graph {
    /// Creates a new graph.
    pub fn new() -> Graph {
        let mut havox = HashMap::new();
        // `true` is not equal to `false`.
        havox.insert((0, 1), false);
        let mut map = HashMap::new();
        map.insert(Expression::False, 0);
        map.insert(Expression::True, 1);
        Graph {
            exprs: vec![Expression::False, Expression::True],
            havox,
            map,
            history: vec![],
            cache: RefCell::new(vec![]),
        }
    }

    /// Logical FALSE has a fixed location `0`.
    pub fn false_(&self) -> usize {0}
    /// Logical TRUE has a fixed location `1`.
    pub fn true_(&self) -> usize {1}

    /// Returns id of existing expression.
    pub fn contains(&self, expr: &Expression) -> Option<usize> {
        self.map.get(expr).map(|&a| a)
    }

    fn add_expr(&mut self, new_expr: Expression) -> usize {
        let id = self.exprs.len();
        self.exprs.push(new_expr.clone());
        self.map.insert(new_expr, id);
        id
    }

    /// Add variable.
    ///
    /// `name` - index of variable referenced externally.
    pub fn var(&mut self, name: usize) -> usize {
        let new_expr = Expression::Var(name);
        if let Some(id) = self.contains(&new_expr) {
            return id;
        }
        self.add_expr(new_expr)
    }

    /// Add logical NOT.
    pub fn not(&mut self, a: usize) -> usize {
        let new_expr = Expression::Not(a);
        if let Some(id) = self.contains(&new_expr) {
            return id;
        }
        self.add_expr(new_expr)
    }

    /// Add logical EQ.
    pub fn eq(&mut self, a: usize, b: usize) -> usize {
        let new_expr = Expression::Eq(a.min(b), a.max(b));
        if let Some(id) = self.contains(&new_expr) {
            return id;
        }
        self.add_expr(new_expr)
    }

    /// Add logical AND.
    pub fn and(&mut self, a: usize, b: usize) -> usize {
        let new_expr = Expression::And(a.min(b), a.max(b));
        if let Some(id) = self.contains(&new_expr) {
            return id;
        }
        self.add_expr(new_expr)
    }

    /// Add logical OR.
    pub fn or(&mut self, a: usize, b: usize) -> usize {
        let new_expr = Expression::Or(a.min(b), a.max(b));
        if let Some(id) = self.contains(&new_expr) {
            return id;
        }
        self.add_expr(new_expr)
    }

    /// Add logical material implication.
    pub fn imply(&mut self, a: usize, b: usize) -> usize {
        let new_expr = Expression::Imply(a, b);
        if let Some(id) = self.contains(&new_expr) {
            return id;
        }
        self.add_expr(new_expr)
    }

    /// Returns `Some(true)` if it is known that two things are equal.
    /// Returns `Some(false)` if it is known that two things are unequal.
    /// Returns `None` if it is unknown whether two things are equal.
    ///
    /// The `id` is an edge of the format `(min, max)`.
    pub fn havox(&self, id: (usize, usize)) -> Option<bool> {
        if id.0 == id.1 {Some(true)}
        else if self.havox.contains_key(&id) {Some(self.havox[&id])}
        else {
            // Find representative of equivalent objects.
            // The smallest index for equivalent objects should be the same.
            // This proves equivalence but not inequality.
            let ref mut cache = self.cache.borrow_mut();
            if cache.len() != self.exprs.len() {
                **cache = vec![None; self.exprs.len()];
            }
            let min_a = self.min_index(id.0, cache);
            let min_b = self.min_index(id.1, cache);
            if min_a == min_b {
                return Some(true)
            };

            // Check all inequivalences to see whether they match representatives.
            let (min_a, min_b) = (min_a.min(min_b), min_a.max(min_b));
            if self.havox.contains_key(&(min_a, min_b)) {return Some(self.havox[&(min_a, min_b)])};
            for (&(a, b), &val) in self.havox.iter() {
                if !val {
                    let ma = self.min_index(a, cache);
                    let mb = self.min_index(b, cache);
                    if ma.min(mb) == min_a && ma.max(mb) == min_b {
                        return Some(false);
                    }
                }
            }

            None
        }
    }

    fn min_index(&self, ind: usize, cache: &mut Vec<Option<usize>>) -> usize {
        // Check if this exists in the cache.
        if let Some(min_ind) = cache[ind] {
            return min_ind;
        }
        let mut min_ind: usize = ind;
        // Build a list of tracked indices to update them afterwards.
        // Use the cache after the end to not need to allocate a new list.
        let offset = cache.len();
        loop {
            let mut changed = false;
            for (&(a, b), &val) in self.havox.iter() {
                if val {
                    // Only necessary to check `b` because `a < b`.
                    if b == min_ind {
                        // If the cache contains the connected node,
                        // then all further along that path are also cached,
                        // so there is no point in continue the search.
                        if let Some(mi) = cache[a] {
                            // Update tracked indices.
                            for i in offset..cache.len() {
                                if let Some(id) = cache[i] {
                                    cache[id] = Some(mi);
                                }
                            }
                            cache[min_ind] = Some(mi);
                            cache.truncate(offset);
                            return mi;
                        }

                        cache.push(Some(min_ind));
                        min_ind = a;
                        changed = true;
                    }
                }
            }
            if !changed {break}
        }

        for i in offset..cache.len() {
            if let Some(id) = cache[i] {
                cache[id] = Some(min_ind);
            }
        }
        cache[min_ind] = Some(min_ind);
        cache.truncate(offset);

        min_ind
    }

    /// Returns whether it is known that two expressions are equivalent.
    pub fn are_eq(&self, a: usize, b: usize) -> Option<bool> {
        let id = (a.min(b), a.max(b));
        self.havox(id)
    }

    fn add_havox(&mut self, (a, b): (usize, usize), val: bool) {
        let ref mut cache = self.cache.borrow_mut();

        // Connect representatives such that equivalence relations are ordered on indices.
        // This is required to make the lookup algorithm sound.
        let a = self.min_index(a, cache);
        let b = self.min_index(b, cache);
        let id = (a.min(b), a.max(b));

        self.history.push(id);
        self.havox.insert(id, val);
        cache.clear();
    }

    fn proof_add_havox(&mut self, id: (usize, usize), val: bool) -> Proof {
        if let Some(v) = self.havox(id) {
            (val == v).into()
        } else {
            self.add_havox(id, val);
            Proof::True
        }
    }

    /// Checks whether it can be proven that one of the arguments are true.
    /// This means the return value depends on the other argument.
    pub fn true_and(&mut self, ind: usize) -> Proof {
        if let Expression::And(a, b) = self.exprs[ind] {
            let id = (self.true_(), a);
            if let Some(val) = self.havox(id) {
                if val {
                    return self.proof_add_havox((b.min(ind), b.max(ind)), true);
                }
            }
            let id = (self.true_(), b);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((a.min(ind), a.max(ind)), true)
                } else {
                    // The input was false, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `and` expression is false,
    /// by knowing that one of the arguments are false.
    pub fn false_and(&mut self, ind: usize) -> Proof {
        if let Expression::And(a, b) = self.exprs[ind] {
            let fa = self.false_();
            let id = (fa, a);
            if let Some(val) = self.havox(id) {
                if val {
                    return self.proof_add_havox((fa, ind), true);
                }
            }
            let id = (fa, b);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((fa, ind), true)
                } else {
                    // The input was false, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that one of the arguments are false.
    /// This means that the `or` expression is equal to the other argument.
    pub fn false_or(&mut self, ind: usize) -> Proof {
        if let Expression::Or(a, b) = self.exprs[ind] {
            let id = (self.false_(), a);
            if let Some(val) = self.havox(id) {
                if val {
                    return self.proof_add_havox((b.min(ind), b.max(ind)), true);
                };
            }
            let id = (self.false_(), b);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((a.min(ind), a.max(ind)), true)
                } else {
                    Proof::Unknown
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `or` expression is true,
    /// by knowing that one of the arguments are true.
    pub fn true_or(&mut self, ind: usize) -> Proof {
        if let Expression::Or(a, b) = self.exprs[ind] {
            let tr = self.true_();
            let id = (tr, a);
            if let Some(val) = self.havox(id) {
                if val {
                    return self.proof_add_havox((tr, ind), true);
                }
            }
            let id = (tr, b);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((tr, ind), true)
                } else {
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that input to `not` expression is true.
    /// This means that the output is false.
    pub fn true_not(&mut self, ind: usize) -> Proof {
        if let Expression::Not(a) = self.exprs[ind] {
            let id = (self.true_(), a);
            if let Some(val) = self.havox(id) {
                if val {
                    let fa = self.false_();
                    self.proof_add_havox((fa, ind), true)
                } else {
                    // The value was false, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that input to `not` expression is false.
    /// This means that the output is true.
    pub fn false_not(&mut self, ind: usize) -> Proof {
        if let Expression::Not(a) = self.exprs[ind] {
            let id = (self.false_(), a);
            if let Some(val) = self.havox(id) {
                if val {
                    let tr = self.true_();
                    self.proof_add_havox((tr, ind), true)
                } else {
                    // The value was true, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether assumption is proven to be false.
    pub fn false_imply(&mut self, ind: usize) -> Proof {
        if let Expression::Imply(a, _) = self.exprs[ind] {
            let id = (self.false_(), a);
            if let Some(val) = self.havox(id) {
                if val {
                    let tr = self.true_();
                    self.proof_add_havox((tr, ind), true)
                } else {
                    // The assumption is true, but this is not a contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether assumption is proven to be true.
    /// True assumption makes the `imply` expression is equal to the conclusion.
    pub fn true_imply(&mut self, ind: usize) -> Proof {
        if let Expression::Imply(a, b) = self.exprs[ind] {
            let id = (self.true_(), a);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((b.min(ind), b.max(ind)), true)
                } else {
                    // Assumption is false, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether arguments to `eq` expression are inequal.
    ///
    /// This means that the `eq` expression must be equal to false.
    pub fn false_eq(&mut self, ind: usize) -> Proof {
        if let Expression::Eq(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if !val {
                    let id = (self.false_(), ind);
                    self.proof_add_havox(id, true)
                } else {
                    // The arguments are equal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether arguments to `eq` expression are equal.
    ///
    /// This means that the `eq` expression must be equal to true.
    pub fn true_eq(&mut self, ind: usize) -> Proof {
        if let Expression::Eq(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if val {
                    let id = (self.true_(), ind);
                    self.proof_add_havox(id, true)
                } else {
                    // The arguments are inequal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether one side is proven to be equal to other side.
    ///
    /// The equation must be equal to true.
    /// When the equation is true, one side is equal to another.
    pub fn eq_true(&mut self, ind: usize) -> Proof {
        if let Expression::Eq(a, b) = self.exprs[ind] {
            let id = (self.true_(), ind);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((a.min(b), a.max(b)), true)
                } else {
                    // One side is not equal to another, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether one side is proven to be inequal to the other side.
    ///
    /// The equation must be equal to false.
    /// When the equation is false, one side is inequal to another.
    pub fn eq_false(&mut self, ind: usize) -> Proof {
        if let Expression::Eq(a, b) = self.exprs[ind] {
            let id = (self.false_(), ind);
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((a.min(b), a.max(b)), false)
                } else {
                    // One side is equal to the other, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that provably `a ∧ ¬a` results in a paradox.
    pub fn paradox(&mut self, ind: usize) -> Proof {
        if let Expression::And(a, b) = self.exprs[ind] {
            if let Expression::Not(b) = self.exprs[b] {
                let id = (a.min(b), a.max(b));
                if let Some(val) = self.havox(id) {
                    if val {
                        let fa = self.false_();
                        self.proof_add_havox((fa, ind), true)
                    } else {
                        // It is not a paradox, but it is not a contradiction.
                        Proof::Unexpected
                    }
                } else {
                    Proof::Unknown
                }
            } else if let Expression::Not(a) = self.exprs[a] {
                let id = (a.min(b), a.max(b));
                if let Some(val) = self.havox(id) {
                    if val {
                        let fa = self.false_();
                        self.proof_add_havox((fa, ind), true)
                    } else {
                        // It is not a paradox, but it is not a contradiction.
                        Proof::Unexpected
                    }
                } else {
                    Proof::Unknown
                }
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that provably `a ∨ ¬a` results in a tautology.
    pub fn tautology(&mut self, ind: usize) -> Proof {
        if let Expression::Or(a, b) = self.exprs[ind] {
            if let Expression::Not(b) = self.exprs[b] {
                let id = (a.min(b), a.max(b));
                if let Some(val) = self.havox(id) {
                    if val {
                        let tr = self.true_();
                        self.proof_add_havox((tr, ind), true)
                    } else {
                        // It is not a tautology, but it is not a contradiction.
                        Proof::Unexpected
                    }
                } else {
                    Proof::Unknown
                }
            } else if let Expression::Not(a) = self.exprs[a] {
                let id = (a.min(b), a.max(b));
                if let Some(val) = self.havox(id) {
                    if val {
                        let tr = self.true_();
                        self.proof_add_havox((tr, ind), true)
                    } else {
                        // It is not a tautology, but it is not a contradiction.
                        Proof::Unexpected
                    }
                } else {
                    Proof::Unknown
                }
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that the `or` expression is false.
    /// This means that both arguments must be false.
    pub fn or_false(&mut self, ind: usize) -> Proof {
        if let Expression::Or(a, b) = self.exprs[ind] {
            let fa = self.false_();
            let id = (fa, ind);
            if let Some(val) = self.havox(id) {
                if val {
                    let id = (fa, a);
                    if let Some(val) = self.havox(id) {
                        if !val {return Proof::False};
                    } else {
                        // The first argument is always false.
                        self.add_havox(id, true);
                    }
                    let id = (fa, b);
                    if let Some(val) = self.havox(id) {
                        if !val {return Proof::False};
                    } else {
                        // The second argument is always false.
                        self.add_havox(id, true);
                    }
                    Proof::True
                } else {
                    // The `or` expression is not false, but this is not a contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that the `and` expression is true.
    /// This means that both arguments must be true.
    pub fn and_true(&mut self, ind: usize) -> Proof {
        if let Expression::And(a, b) = self.exprs[ind] {
            let tr = self.true_();
            let id = (tr, ind);
            if let Some(val) = self.havox(id) {
                if val {
                    let id = (tr, a);
                    if let Some(val) = self.havox(id) {
                        if !val {return Proof::False};
                    } else {
                        // The first argument is always true.
                        self.add_havox(id, true);
                    }
                    let id = (tr, b);
                    if let Some(val) = self.havox(id) {
                        if !val {return Proof::False};
                    } else {
                        // The second argument is always true.
                        self.add_havox(id, true);
                    }
                    Proof::True
                } else {
                    // The `and` expression is not true, but it is not a contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Check if it can be proven that output of `not` expression is true.
    pub fn not_true(&mut self, ind: usize) -> Proof {
        if let Expression::Not(a) = self.exprs[ind] {
            let id = (self.true_(), ind);
            if let Some(val) = self.havox(id) {
                if val {
                    let fa = self.false_();
                    self.proof_add_havox((fa, a), true)
                } else {
                    // The output is false, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Check if it can be proven that output of `not` expression is false.
    pub fn not_false(&mut self, ind: usize) -> Proof {
        if let Expression::Not(a) = self.exprs[ind] {
            let id = (self.false_(), ind);
            if let Some(val) = self.havox(id) {
                if val {
                    let tr = self.true_();
                    self.proof_add_havox((tr, a), true)
                } else {
                    // The output is false, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Check that it can be proven that an expression is either true or false.
    pub fn excluded_middle(&mut self, ind: usize) -> Proof {
        let id = (self.false_(), ind);
        if let Some(val) = self.havox(id) {
            let tr = self.true_();
            self.proof_add_havox((tr, ind), !val)
        } else {
            let id = (self.true_(), ind);
            if let Some(val) = self.havox(id) {
                let fa = self.false_();
                self.proof_add_havox((fa, ind), !val)
            } else {
                Proof::Unknown
            }
        }
    }

    /// Checks whether it can be proven that `and` expression has equal arguments,
    /// which means that the `and` expression is the same as the argument.
    pub fn eq_and(&mut self, ind: usize) -> Proof {
        if let Expression::And(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((a.min(ind), a.max(ind)), true)
                } else {
                    // The argument as inequal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `and` expression has inequal arguments.
    /// This means that the `and` expression is always false.
    pub fn neq_and(&mut self, ind: usize) -> Proof {
        if let Expression::And(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if !val {
                    let fa = self.false_();
                    self.proof_add_havox((fa, ind), true)
                } else {
                    // The arguments are equal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `or` expression has equal arguments.
    /// This means that the `or` expression is always equal to its argument.
    pub fn eq_or(&mut self, ind: usize) -> Proof {
        if let Expression::Or(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if val {
                    self.proof_add_havox((a.min(ind), ind), true)
                } else {
                    // The arguments are inequal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `or` expression has inequal arguments.
    /// This means the `or` expression is always true.
    pub fn neq_or(&mut self, ind: usize) -> Proof {
        if let Expression::Or(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if !val {
                    let tr = self.true_();
                    self.proof_add_havox((tr, ind), true)
                } else {
                    // The arguments are equal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `imply` expression has equal arguments.
    /// This means the `imply` expression is always true.
    pub fn eq_imply(&mut self, ind: usize) -> Proof {
        if let Expression::Imply(a, b) = self.exprs[ind] {
            let id = (a.min(b), a.max(b));
            if let Some(val) = self.havox(id) {
                if val {
                    let tr = self.true_();
                    self.proof_add_havox((tr, ind), true)
                } else {
                    // The arguments are inequal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks whether it can be proven that `imply` expression has inequal arguments.
    /// This means the `imply` expression is always equal to the second argument.
    pub fn neq_imply(&mut self, ind: usize) -> Proof {
        if let Expression::Imply(a, b) = self.exprs[ind] {
            let id = (a.min(b), b.max(b));
            if let Some(val) = self.havox(id) {
                if !val {
                    self.proof_add_havox((b.min(ind), b.max(ind)), true)
                } else {
                    // The arguments are equal, but there is no contradiction.
                    Proof::Unexpected
                }
            } else {
                Proof::Unknown
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that `and[not] <=> or`.
    ///
    /// This is equivalent to `not(and(a, b)) = or(not(a), not(b))`.
    pub fn path_and_not(&mut self, ind: usize) -> Proof {
        if let Expression::Not(not_ind) = self.exprs[ind] {
            if let Expression::And(a, b) = self.exprs[not_ind] {
                let not_a = self.not(a);
                let not_b = self.not(b);
                let or = self.or(not_a, not_b);
                self.proof_add_havox((ind.min(or), ind.max(or)), true)
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that `or <=> and[not]`.
    ///
    /// This is equivalent to `or(not(a), not(b)) = not(and(a, b))`.
    pub fn path_not_and(&mut self, ind: usize) -> Proof {
        if let Expression::Or(not_a, not_b) = self.exprs[ind] {
            if let (&Expression::Not(a), &Expression::Not(b)) =
                (&self.exprs[not_a], &self.exprs[not_b])
            {
                let and = self.and(a, b);
                let not_and = self.not(and);
                self.proof_add_havox((ind.min(not_and), ind.max(not_and)), true)
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that `or[not] <=> and`.
    ///
    /// This is equivalent to `not(or(a, b)) = and(not(a), not(b))`.
    pub fn path_or_not(&mut self, ind: usize) -> Proof {
        if let Expression::Not(not_ind) = self.exprs[ind] {
            if let Expression::Or(a, b) = self.exprs[not_ind] {
                let not_a = self.not(a);
                let not_b = self.not(b);
                let and = self.and(not_a, not_b);
                self.proof_add_havox((ind.min(and), ind.max(and)), true)
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that `and <=> or[not]`.
    ///
    /// This is equivalent to `or(not(a), not(b)) = not(and(a, b))`.
    pub fn path_not_or(&mut self, ind: usize) -> Proof {
        if let Expression::And(not_a, not_b) = self.exprs[ind] {
            if let (&Expression::Not(a), &Expression::Not(b)) =
                (&self.exprs[not_a], &self.exprs[not_b])
            {
                let or = self.or(a, b);
                let not_or = self.not(or);
                self.proof_add_havox((ind.min(not_or), ind.max(not_or)), true)
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Checks that `not . not <=> id`.
    pub fn not_not(&mut self, ind: usize) -> Proof {
        if let Expression::Not(not_ind) = self.exprs[ind] {
            if let Expression::Not(a) = self.exprs[not_ind] {
                self.proof_add_havox((a.min(ind), a.max(ind)), true)
            } else {
                Proof::Error
            }
        } else {
            Proof::Error
        }
    }

    /// Assume that two expressions are equivalent.
    ///
    /// Returns an assumption that can be used to roll back change.
    pub fn assume_eq(&mut self, a: usize, b: usize) -> Assumption {
        let id = (a.min(b), a.max(b));
        if let Some(val) = self.havox(id) {return Assumption::AlreadyKnown(val)};
        let len = self.history.len();
        self.add_havox(id, true);
        Assumption::Eq {id, history: len}
    }

    /// Assume that two expressions are inequivalent.
    ///
    /// Returns an assumption that can be used to roll back change.
    pub fn assume_neq(&mut self, a: usize, b: usize) -> Assumption {
        let id = (a.min(b), a.max(b));
        if let Some(val) = self.havox(id) {return Assumption::AlreadyKnown(val)};
        let len = self.history.len();
        self.add_havox(id, false);
        Assumption::Neq {id, history: len}
    }

    /// Solves as much as possible using all tactics.
    pub fn solve(&mut self) -> Proof {
        loop {
            let len = self.history.len();
            for i in 0..self.exprs.len() {
                if self.and_true(i) == Proof::False {return Proof::False};
                if self.or_false(i) == Proof::False {return Proof::False};
                if self.true_and(i) == Proof::False {return Proof::False};
                if self.false_and(i) == Proof::False {return Proof::False};
                if self.true_or(i) == Proof::False {return Proof::False};
                if self.false_or(i) == Proof::False {return Proof::False};
                if self.true_imply(i) == Proof::False {return Proof::False};
                if self.false_imply(i) == Proof::False {return Proof::False};
                if self.false_eq(i) == Proof::False {return Proof::False};
                if self.true_eq(i) == Proof::False {return Proof::False};
                if self.paradox(i) == Proof::False {return Proof::False};
                if self.tautology(i) == Proof::False {return Proof::False};
                if self.eq_true(i) == Proof::False {return Proof::False};
                if self.eq_false(i) == Proof::False {return Proof::False};
                if self.eq_and(i) == Proof::False {return Proof::False};
                if self.neq_and(i) == Proof::False {return Proof::False};
                if self.eq_or(i) == Proof::False {return Proof::False};
                if self.neq_or(i) == Proof::False {return Proof::False};
                if self.eq_imply(i) == Proof::False {return Proof::False};
                if self.neq_imply(i) == Proof::False {return Proof::False};
                if self.not_true(i) == Proof::False {return Proof::False};
                if self.not_false(i) == Proof::False {return Proof::False};
                if self.true_not(i) == Proof::False {return Proof::False};
                if self.false_not(i) == Proof::False {return Proof::False};
                if self.excluded_middle(i) == Proof::False {return Proof::False};
                if self.not_not(i) == Proof::False {return Proof::False};

                // These tactics might introduce new expressions.
                if self.path_and_not(i) == Proof::False {return Proof::False};
                if self.path_or_not(i) == Proof::False {return Proof::False};
                if self.path_not_and(i) == Proof::False {return Proof::False};
                if self.path_not_or(i) == Proof::False {return Proof::False};
            }
            if self.history.len() == len {
                return Proof::True;
            }
        }
    }
}

/// Stores assumption, which is extra information added that might lead to inconsistency.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Assumption {
    /// This assumption has already a known value.
    AlreadyKnown(bool),
    /// Two expressions are equivalent.
    Eq {
        /// The edge id that is not equivalent.
        id: (usize, usize),
        /// The length of history when assumption being made.
        history: usize
    },
    /// Two expressions are not equivalent.
    Neq {
        /// The edge id that is not equivalent.
        id: (usize, usize),
        /// The length of history when assumption being made.
        history: usize
    },
}

impl Assumption {
    /// Undoes assumption.
    pub fn undo(&self, graph: &mut Graph) {
        match *self {
            Assumption::AlreadyKnown(_) => {}
            Assumption::Eq {history, ..} | Assumption::Neq {history, ..} => {
                for i in history..graph.history.len() {
                    let id = graph.history[i];
                    graph.havox.remove(&id);
                }
                graph.history.truncate(history);
                graph.cache.borrow_mut().clear();
            }
        }
    }

    /// Undoes and inverts assumption.
    pub fn invert(&self, graph: &mut Graph) -> Assumption {
        self.undo(graph);
        match *self {
            Assumption::AlreadyKnown(_) => *self,
            Assumption::Eq {id, ..} => graph.assume_neq(id.0, id.1),
            Assumption::Neq {id, ..} => graph.assume_eq(id.0, id.1),
        }
    }
}

/// Stores result of a proof.
#[derive(Eq, PartialEq, Copy, Clone, Debug)]
pub enum Proof {
    /// Locally correct and no contradiction so far.
    /// NB! This does not mean that the proof is correct.
    /// This required assigning a value to every variable.
    True,
    /// Contradiction.
    /// There exists some assumption of consequence of assumptions
    /// which contradicts the conclusion of the tactic.
    False,
    /// It is unknown whether the tactic can be applied at this moment.
    /// Add more assumptions and try again, or try a different tactic.
    Unknown,
    /// A contradiction to the assumption of the tactic was found.
    /// This does not mean the proof is wrong, but that this particular tactic is the wrong strategy.
    Unexpected,
    /// This tactic can not be performed on this expression.
    /// Usually due to grammatical error.
    Error,
}

impl From<bool> for Proof {
    fn from(val: bool) -> Proof {
        if val {Proof::True} else {Proof::False}
    }
}

/// Stores a logical expression.
#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub enum Expression {
    /// True.
    True,
    /// False.
    False,
    /// Variable.
    Var(usize),
    /// Logical NOT.
    Not(usize),
    /// Logical AND.
    And(usize, usize),
    /// Logical OR.
    Or(usize, usize),
    /// Logical EQ.
    Eq(usize, usize),
    /// Logical material implication.
    Imply(usize, usize),
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::*;
    use self::test::Bencher;

    #[test]
    fn false_imply() {
        let mut g = Graph::new();
        let a = g.var(0);
        let fa = g.false_();
        let b = g.imply(fa, a);     // false -> a
        assert_eq!(g.false_imply(b), Proof::True);
    }

    #[test]
    fn true_imply() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let c = g.imply(a, b);      // a -> b
        let tr = g.true_();
        let a_tr = g.assume_eq(tr, a);  // a = true
        assert_eq!(g.true_imply(c), Proof::True);
        let a_not_tr = a_tr.invert(g);
        // Only because something is not true, does not mean that it is false.
        // The inequality can be of a different kind than the one between `true` and `false`.
        assert_eq!(g.false_imply(c), Proof::Unknown);
        a_not_tr.undo(g);
    }

    #[test]
    fn invert() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let _ab = g.assume_eq(a, b);    // a = b
        let tr = g.true_();
        let a_tr = g.assume_eq(tr, a);  // a = true
        assert_eq!(g.are_eq(tr, b), Some(true));
        let a_not_tr = a_tr.invert(g);  // a != true
        assert_eq!(g.are_eq(tr, b), Some(false));
        a_not_tr.undo(g);
    }

    #[test]
    fn false_eq() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let eq = g.eq(a, b);
        let _ = g.assume_neq(a, b);
        assert_eq!(g.false_eq(eq), Proof::True);
        let fa = g.false_();
        assert_eq!(g.are_eq(eq, fa), Some(true));
    }

    #[test]
    fn true_eq() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let eq = g.eq(a, b);
        let _ = g.assume_eq(a, b);
        assert_eq!(g.true_eq(eq), Proof::True);
        let tr = g.true_();
        assert_eq!(g.are_eq(eq, tr), Some(true));
    }

    #[test]
    fn eq_true() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let tr = g.true_();
        let eq = g.eq(a, tr);
        let eq_tr = g.assume_eq(eq, tr); // (a = true) = true
        assert_eq!(g.are_eq(a, tr), None);
        assert_eq!(g.eq_true(eq), Proof::True);
        assert_eq!(g.are_eq(a, tr), Some(true));
        eq_tr.undo(g);
        assert_eq!(g.eq_true(eq), Proof::Unknown);
        let _a_neq_true = g.assume_neq(a, tr); // a != trueg
        let _eq_tr = g.assume_eq(eq, tr);    // (a = true) = true
        assert_eq!(g.eq_true(eq), Proof::False);
    }

    #[test]
    fn paradox() {
        // ∀ a { ¬(a ∧ ¬a) }
        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let and = g.and(a, not_a);
        assert_eq!(g.paradox(and), Proof::True);

        // ∀ a { ¬(¬a ∧ a) }
        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let and = g.and(not_a, a);
        assert_eq!(g.paradox(and), Proof::True);

        // a ∧ ¬b       is unknown whether it is a paradox.
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let not_b = g.not(b);
        let and = g.and(a, not_b);
        assert_eq!(g.paradox(and), Proof::Unknown);

        // a ∧ ¬b       is not a paradox if a != b
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let not_b = g.not(b);
        let and = g.and(a, not_b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.paradox(and), Proof::Unexpected);

        // Indirect paradox should not work.
        // This is to avoid unclear proofs.
        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let and = g.and(a, not_a);
        let c = g.var(2);
        let _c_is_and = g.assume_eq(c, and);
        assert_eq!(g.paradox(c), Proof::Error);
        assert_eq!(g.paradox(and), Proof::True);
        let fa = g.false_();
        assert_eq!(g.are_eq(and, fa), Some(true));
        assert_eq!(g.are_eq(c, fa), Some(true));

        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let and = g.and(not_a, a);
        let c = g.var(2);
        let _c_is_and = g.assume_eq(c, and);
        assert_eq!(g.paradox(c), Proof::Error);
        assert_eq!(g.paradox(and), Proof::True);
        let fa = g.false_();
        assert_eq!(g.are_eq(and, fa), Some(true));
        assert_eq!(g.are_eq(c, fa), Some(true));
    }

    #[test]
    fn true_or() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let tr = g.true_();

        let a_is_true = g.assume_eq(a, tr);
        assert_eq!(g.true_or(or), Proof::True);
        a_is_true.undo(g);

        let b_is_true = g.assume_eq(b, tr);
        assert_eq!(g.true_or(or), Proof::True);
        b_is_true.undo(g);
    }

    #[test]
    fn false_and() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let fa = g.false_();

        let a_is_false = g.assume_eq(a, fa);
        assert_eq!(g.false_and(and), Proof::True);
        a_is_false.undo(g);

        let b_is_false = g.assume_eq(b, fa);
        assert_eq!(g.false_and(and), Proof::True);
        b_is_false.undo(g);
    }

    #[test]
    fn or_false() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let fa = g.false_();

        let _ = g.assume_eq(a, fa);
        let _ = g.assume_eq(b, fa);
        let _ = g.assume_eq(or, fa);
        assert_eq!(g.or_false(or), Proof::True);
    }

    #[test]
    fn and_true() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let tr = g.true_();

        let _ = g.assume_eq(a, tr);
        let _ = g.assume_eq(b, tr);
        let _ = g.assume_eq(and, tr);
        assert_eq!(g.and_true(and), Proof::True);
    }

    #[test]
    fn eq_and() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let and = g.and(a, a);
        assert_eq!(g.eq_and(and), Proof::True);
        assert_eq!(g.are_eq(and, a), Some(true));

        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let _a_eq_b = g.assume_eq(a, b);
        assert_eq!(g.eq_and(and), Proof::True);
        assert_eq!(g.are_eq(and, a), Some(true));
        assert_eq!(g.are_eq(and, b), Some(true));
    }

    #[test]
    fn neq_and() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.neq_and(and), Proof::True);
        let fa = g.false_();
        assert_eq!(g.are_eq(and, fa), Some(true));
    }

    #[test]
    fn eq_or() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let or = g.or(a, a);
        assert_eq!(g.eq_or(or), Proof::True);
        assert_eq!(g.are_eq(or, a), Some(true));

        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let _a_eq_b = g.assume_eq(a, b);
        assert_eq!(g.eq_or(or), Proof::True);
        assert_eq!(g.are_eq(or, a), Some(true));
        assert_eq!(g.are_eq(or, b), Some(true));
    }

    #[test]
    fn neq_or() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.neq_or(or), Proof::True);
        let tr = g.true_();
        assert_eq!(g.are_eq(or, tr), Some(true));
    }

    #[test]
    fn eq_imply() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let imply = g.imply(a, b);
        let _a_eq_b = g.assume_eq(a, b);
        assert_eq!(g.eq_imply(imply), Proof::True);
        let tr = g.true_();
        assert_eq!(g.are_eq(imply, tr), Some(true));
    }

    #[test]
    fn neq_imply() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let imply = g.imply(a, b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.neq_imply(imply), Proof::True);
        assert_eq!(g.are_eq(imply, b), Some(true));
    }

    #[test]
    fn and_commutative() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and1 = g.and(a, b);
        let and2 = g.and(b, a);
        assert_eq!(g.are_eq(and1, and2), Some(true));
    }

    #[test]
    fn or_commutative() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or1 = g.or(a, b);
        let or2 = g.or(b, a);
        assert_eq!(g.are_eq(or1, or2), Some(true));
    }

    #[test]
    fn eq_commutative() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let eq1 = g.eq(a, b);
        let eq2 = g.eq(b, a);
        assert_eq!(g.are_eq(eq1, eq2), Some(true));
    }

    #[test]
    fn propagate_equality() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let c = g.var(2);
        let d = g.var(3);
        let _ = g.assume_eq(a, b);
        let _ = g.assume_eq(b, c);
        let _ = g.assume_eq(c, d);
        assert_eq!(g.are_eq(a, c), Some(true));
        assert_eq!(g.are_eq(a, d), Some(true));
    }

    #[test]
    fn propagate_inequality() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let c = g.var(2);
        let d = g.var(3);
        let _ = g.assume_neq(a, b);
        let _ = g.assume_eq(a, c);
        let _ = g.assume_eq(b, d);
        assert_eq!(g.are_eq(c, d), Some(false));
    }

    #[bench]
    fn bench_propagate_equality(bencher: &mut Bencher) {
        let ref mut g = Graph::new();
        for i in 0..1000 {
            let _ = g.var(i);
        }
        for i in 1..1000 {
            let a = g.var(i-1);
            let b = g.var(i);
            let _ = g.assume_eq(a, b);
        }

        let a = g.var(0);
        let b = g.var(999);
        bencher.iter(|| {
            assert_eq!(g.are_eq(a, b), Some(true));
        });
    }

    #[bench]
    fn bench_propagate_inequality(bencher: &mut Bencher) {
        let ref mut g = Graph::new();
        for i in 0..1000 {
            let _ = g.var(i);
            let _ = g.var(1000+i);
        }
        for i in 1..1000 {
            let a = g.var(i-1);
            let b = g.var(i);
            let _ = g.assume_eq(a, b);

            let a = g.var(1000+i-1);
            let b = g.var(1000+i);
            let _ = g.assume_eq(a, b);
        }

        let a = g.var(999);
        let b = g.var(1000);
        let _ = g.assume_neq(a, b);

        let a = g.var(0);
        let b = g.var(1999);
        bencher.iter(|| {
            assert_eq!(g.are_eq(a, b), Some(false));
        });
    }

    #[test]
    fn proof_1() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let a_imply_b = g.imply(a, b);
        let and = g.and(a_imply_b, a);
        let imply = g.imply(and, b);
        let tr = g.true_();
        let _ = g.assume_eq(imply, tr);
        let _ = g.assume_eq(and, tr);
        assert_eq!(g.solve(), Proof::True);

        assert_eq!(g.are_eq(b, tr), Some(true));
        assert_eq!(g.are_eq(and, tr), Some(true));
        assert_eq!(g.are_eq(a, tr), Some(true));
        assert_eq!(g.are_eq(a_imply_b, tr), Some(true));
    }

    #[test]
    fn proof_2() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let and = g.and(a, not_a);
        assert_eq!(g.solve(), Proof::True);

        let fa = g.false_();
        assert_eq!(g.are_eq(and, fa), Some(true));
    }

    #[test]
    fn proof_3() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let or = g.or(a, not_a);
        assert_eq!(g.solve(), Proof::True);

        let tr = g.true_();
        assert_eq!(g.are_eq(or, tr), Some(true));
    }

    #[test]
    fn proof_4() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let eq = g.eq(a, a);
        assert_eq!(g.solve(), Proof::True);

        let tr = g.true_();
        assert_eq!(g.are_eq(eq, tr), Some(true));
    }

    #[test]
    fn proof_5() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let tr = g.true_();
        let eq = g.eq(a, tr);
        let eq_tr = g.assume_eq(eq, tr); // (a = true) = true
        assert_eq!(g.are_eq(a, tr), None);

        assert_eq!(g.solve(), Proof::True);

        assert_eq!(g.are_eq(a, tr), Some(true));
        eq_tr.undo(g);
        assert_eq!(g.eq_true(eq), Proof::Unknown);

        let _a_neq_true = g.assume_neq(a, tr); // a != trueg
        let _eq_tr = g.assume_eq(eq, tr);    // (a = true) = true
        assert_eq!(g.eq_true(eq), Proof::False);
    }

    #[test]
    fn proof_6() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let and = g.and(a, a);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(and, a), Some(true));

        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let _a_eq_b = g.assume_eq(a, b);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(and, a), Some(true));
        assert_eq!(g.are_eq(and, b), Some(true));
    }

    #[test]
    fn proof_7() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.solve(), Proof::True);
        let fa = g.false_();
        assert_eq!(g.are_eq(and, fa), Some(true));
    }

    #[test]
    fn proof_8() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let or = g.or(a, a);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(or, a), Some(true));

        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let _a_eq_b = g.assume_eq(a, b);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(or, a), Some(true));
        assert_eq!(g.are_eq(or, b), Some(true));
    }

    #[test]
    fn proof_9() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.solve(), Proof::True);
        let tr = g.true_();
        assert_eq!(g.are_eq(or, tr), Some(true));
    }

    #[test]
    fn proof_10() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let imply = g.imply(a, b);
        let _a_eq_b = g.assume_eq(a, b);
        assert_eq!(g.solve(), Proof::True);
        let tr = g.true_();
        assert_eq!(g.are_eq(imply, tr), Some(true));
    }

    #[test]
    fn proof_11() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let imply = g.imply(a, b);
        let _a_neq_b = g.assume_neq(a, b);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(imply, b), Some(true));
    }

    #[test]
    fn proof_12() {
        // Using example from `Surprising Strong Assumptions` paper
        // (for more information, see path semantics repository)
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);

        let imply = g.imply(a, b);
        let a_eq_b = g.eq(a, b);
        let neq = g.not(a_eq_b);
        let and1 = g.and(imply, neq);

        let not_a = g.not(a);
        let and2 = g.and(not_a, b);

        let eq = g.eq(and1, and2);

        let tr = g.true_();
        let fa = g.false_();

        let _ = g.assume_eq(eq, tr);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(and1, and2), Some(true));

        let and1_tr = g.assume_eq(and1, tr);
        assert_eq!(g.solve(), Proof::True);

        assert_eq!(g.are_eq(imply, tr), Some(true));
        assert_eq!(g.are_eq(neq, tr), Some(true));
        assert_eq!(g.are_eq(a_eq_b, fa), Some(true));
        assert_eq!(g.are_eq(a, b), Some(false));
        assert_eq!(g.are_eq(imply, b), Some(true));
        assert_eq!(g.are_eq(b, tr), Some(true));
        assert_eq!(g.are_eq(not_a, tr), Some(true));
        assert_eq!(g.are_eq(a, fa), Some(true));

        let _ = and1_tr.invert(g);
        assert_eq!(g.solve(), Proof::True);

        assert_eq!(g.are_eq(and1, tr), Some(false));
        assert_eq!(g.are_eq(and1, fa), Some(true));
        assert_eq!(g.are_eq(and1, and2), Some(true));
        assert_eq!(g.are_eq(and2, fa), Some(true));
        assert_eq!(g.are_eq(and2, tr), Some(false));

        assert_eq!(g.are_eq(b, fa), None);
        assert_eq!(g.are_eq(not_a, fa), None);

        let _ = g.assume_eq(b, tr);
        let _ = g.assume_eq(not_a, fa);
        assert_eq!(g.solve(), Proof::True);

        assert_eq!(g.are_eq(a, tr), Some(true));
        assert_eq!(g.are_eq(not_a, fa), Some(true));
        assert_eq!(g.are_eq(imply, fa), Some(false));
        assert_eq!(g.are_eq(a_eq_b, tr), Some(true));
        assert_eq!(g.are_eq(neq, fa), Some(true));
    }

    #[test]
    fn proof_13() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let tr = g.true_();
        let and = g.and(a, tr);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(and, a), Some(true));
    }

    #[test]
    fn proof_14() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let fa = g.false_();
        let and = g.and(a, fa);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(and, fa), Some(true));
    }

    #[test]
    fn proof_15() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let fa = g.false_();
        let or = g.or(a, fa);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(or, a), Some(true));
    }

    #[test]
    fn proof_16() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let tr = g.true_();
        let or = g.or(a, tr);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(or, tr), Some(true));
    }

    #[test]
    fn proof_17() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let eq = g.eq(a, b);
        let _ = g.assume_neq(a, b);
        assert_eq!(g.solve(), Proof::True);
        let fa = g.false_();
        assert_eq!(g.are_eq(eq, fa), Some(true));
    }

    #[test]
    fn proof_18() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let eq = g.eq(a, b);
        let _ = g.assume_eq(a, b);
        assert_eq!(g.solve(), Proof::True);
        let tr = g.true_();
        assert_eq!(g.are_eq(eq, tr), Some(true));
    }

    #[test]
    fn path_and_not() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let and = g.and(a, b);
        let not_and = g.not(and);
        // assert_eq!(g.path_and_not(not_and), Proof::True);
        assert_eq!(g.solve(), Proof::True);
        let not_a = g.not(a);
        let not_b = g.not(b);
        let or = g.or(not_a, not_b);
        assert_eq!(g.are_eq(not_and, or), Some(true));
    }

    #[test]
    fn path_not_and() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let not_a = g.not(a);
        let not_b = g.not(b);
        let or = g.or(not_a, not_b);
        // assert_eq!(g.path_not_and(or), Proof::True);
        assert_eq!(g.solve(), Proof::True);
        let and = g.and(a, b);
        let not_and = g.not(and);
        assert_eq!(g.are_eq(or, not_and), Some(true));
    }

    #[test]
    fn path_or_not() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let or = g.or(a, b);
        let not_or = g.not(or);
        // assert_eq!(g.path_or_not(not_or), Proof::True);
        assert_eq!(g.solve(), Proof::True);
        let not_a = g.not(a);
        let not_b = g.not(b);
        let and = g.and(not_a, not_b);
        assert_eq!(g.are_eq(not_or, and), Some(true));
    }

    #[test]
    fn path_not_or() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let b = g.var(1);
        let not_a = g.not(a);
        let not_b = g.not(b);
        let and = g.and(not_a, not_b);
        // assert_eq!(g.path_not_or(and), Proof::True);
        assert_eq!(g.solve(), Proof::True);
        let or = g.or(a, b);
        let not_or = g.not(or);
        assert_eq!(g.are_eq(and, not_or), Some(true));
    }

    #[test]
    fn path_not_not() {
        let ref mut g = Graph::new();
        let a = g.var(0);
        let not_a = g.not(a);
        let not_not_a = g.not(not_a);
        // assert_eq!(g.not_not(not_not_a), Proof::True);
        assert_eq!(g.solve(), Proof::True);
        assert_eq!(g.are_eq(not_not_a, a), Some(true));
    }
}
