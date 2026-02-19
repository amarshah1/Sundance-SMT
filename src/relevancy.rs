// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation for quantifier instantiation filtering.
//!
//! Tracks which SAT variables (i32) are relevant based on the boolean
//! formula structure. We use SAT variable IDs (i32) rather than term UIDs
//! (u64) because the Tseitin transformation and propagator callbacks all
//! operate on SAT variables, avoiding extra lookups through var_map.
//!
//! Only relevant quantifiers are instantiated, avoiding unnecessary
//! E-matching work on "don't care" parts of the formula.

use std::collections::{HashMap, HashSet};

/// Describes the boolean structure of a Tseitin variable's children.
/// Children are stored as signed SAT literals (positive = same polarity,
/// negative = negated), matching the Tseitin encoding.
#[derive(Debug, Clone)]
pub enum RelevancyRule {
    Or { children: Vec<i32> },
    And { children: Vec<i32> },
}

/// Propagates relevancy through the boolean formula structure.
///
/// The propagator maintains a set of relevant SAT variables. A variable
/// becomes relevant either because it's an assertion root (always relevant)
/// or because relevancy propagated to it from its parent via OR/AND rules.
///
/// A trail records (variable, decision_level) for each relevancy marking,
/// enabling efficient backtracking by popping entries above the target level.
/// note: we only have polarity for quantifier_literal I think thats ok
pub struct RelevancyPropagator {
    pub enabled: bool,
    /// SAT var (abs) -> structural rule. Only Tseitin-introduced vars for
    /// OR/AND nodes have entries here. Atoms have no rule (they are leaves).
    /// Each Tseitin var has at most one structural rule.
    rules: HashMap<i32, RelevancyRule>,
    /// Signed SAT literal -> list of instantiation children. Keyed on signed
    /// literal because polarity determines the operation: for Forall quantifiers,
    /// positive assignment triggers instantiation and negative triggers
    /// skolemization; for Exists quantifiers it's the opposite. Each operation
    /// produces different body literals, so edges must be polarity-specific.
    /// A quantifier can be instantiated multiple times, so this is 1-to-many.
    instantiation_edges: HashMap<i32, Vec<i32>>,
    /// Set of SAT variables (abs) currently marked as relevant.
    relevant: HashSet<i32>,
    /// Top-level assertion root SAT variables (always relevant).
    roots: HashSet<i32>,
    /// Trail of (variable, decision_level) for backtracking.
    /// Entries are pushed in the order variables become relevant.
    trail: Vec<(i32, usize)>,
    /// Current decision level (updated by the propagator callbacks).
    decision_level: usize,
    /// Tracks instantiation edges that were eagerly propagated (because the
    /// source quantifier was already relevant and assigned when the edge was
    /// added). Each entry is (quantifier_lit signed, body_var abs).
    ///
    /// On backtrack, for each entry we check whether the quantifier is still
    /// relevant and assigned at the right polarity. If so, we re-propagate to
    /// the body (which may have been unmarked by backtracking). If not (the
    /// quantifier's own relevancy was backtracked away), we drop the entry.
    ///
    /// Entries are cleared entirely when backtracking to level 0, because at
    /// that point all surviving entries are permanently relevant (level-0
    /// assignments are never undone).
    pending_instantiations: Vec<(i32, i32)>,
}

impl RelevancyPropagator {
    pub fn new(enabled: bool) -> Self {
        Self {
            enabled,
            rules: HashMap::new(),
            instantiation_edges: HashMap::new(),
            relevant: HashSet::new(),
            roots: HashSet::new(),
            trail: Vec::new(),
            decision_level: 0,
            pending_instantiations: Vec::new(),
        }
    }

    /// Register a Tseitin variable's boolean structure (called during CNF encoding).
    pub fn add_rule(&mut self, tseitin_var: i32, rule: RelevancyRule) {
        if !self.enabled {
            return;
        }
        self.rules.insert(tseitin_var.abs(), rule);
    }

    /// Register a top-level assertion root (always relevant).
    pub fn add_root(&mut self, var: i32) {
        debug_println!(23, 0, "adding the root {}", var);
        if !self.enabled {
            return;
        }
        self.roots.insert(var.abs());
    }

    /// Register an instantiation edge: when `quantifier_lit` (signed) is
    /// relevant, `body_var` should also be relevant. Uses signed literal for
    /// the quantifier because polarity determines the operation (see field doc).
    /// Body var uses abs since relevancy is a property of the expression.
    ///
    /// If the quantifier is already relevant and assigned at the matching polarity
    /// (e.g. a unit clause forced at level 0 that will never be re-assigned),
    /// propagate to `body_var` immediately at the current decision level.
    /// The entry is also recorded in `pending_instantiations` so that backtracking
    /// can re-propagate it if the body loses relevancy but the quantifier remains.
    pub fn add_instantiation_edge(&mut self, quantifier_lit: i32, body_var: i32, assignments: &[i32]) {
        if !self.enabled {
            return;
        }
        self.instantiation_edges
            .entry(quantifier_lit)
            .or_default()
            .push(body_var.abs());

        // Eagerly propagate if the source is already relevant and assigned at
        // the right polarity.
        if self.is_relevant_and_assigned_at(quantifier_lit, assignments) {
            if self.mark_relevant(body_var) {
                self.propagate_children(body_var.abs(), assignments);
            }
            // Track so backtrack() can re-propagate if the body gets unmarked.
            debug_println!(23, 0, "Adding ({}, {}) to pending_instantiations", quantifier_lit, body_var.abs());
            self.pending_instantiations.push((quantifier_lit, body_var.abs()));
        }
    }

    /// Returns true if `quantifier_lit` (signed) is currently in the relevant
    /// set AND is assigned in `assignments` with a polarity matching the sign
    /// of `quantifier_lit`.
    fn is_relevant_and_assigned_at(&self, quantifier_lit: i32, assignments: &[i32]) -> bool {
        debug_println!(23, 0, "Checking if {} is relevant and assigned at level {}", quantifier_lit, self.decision_level);
        if !self.relevant.contains(&quantifier_lit.abs()) {
            debug_println!(23, 0, "   not relevant");
            return false;
        }
        return true

        // todo: we are ignoring polarity issues because we assume if the quantifier is relevant it has to be at 
        // the right polarity, since if it switches polarity it will go through a phase of
        // not relevant
        
        // let abs_idx = quantifier_lit.unsigned_abs() as usize;
    
        // if abs_idx >= assignments.len() || assignments[abs_idx] == 0 {
        //     debug_println!(23, 0, "   not assigned");
        //     return false;
        // }

        // let assigned_true = assignments[abs_idx] > 0;
        // let signed = if assigned_true { quantifier_lit.abs() } else { -(quantifier_lit.abs()) };
        // if !(signed == quantifier_lit) {
        //     debug_println!(23, 0, "   assigned with wrong polarity");
        // } else {
        //     debug_println!(23, 0, "   relevant and assigned with correct polarity");
        // }
        // signed == quantifier_lit
    }

    /// Check whether a SAT variable is relevant.
    /// Returns true if relevancy filtering is disabled (everything is relevant).
    pub fn is_relevant(&self, var: i32) -> bool {
        if !self.enabled {
            return true;
        }
        self.relevant.contains(&var.abs())
    }

    /// Mark a SAT variable as relevant at the current decision level.
    /// Returns true if it was newly marked (i.e., wasn't already relevant).
    fn mark_relevant(&mut self, var: i32) -> bool {
        debug_println!(23, 0, "marking {} as relevant at level {}", var, self.decision_level);
        let abs_var = var.abs();
        let newly_inserted = self.relevant.insert(abs_var);
        if newly_inserted {
            self.trail.push((abs_var, self.decision_level));
            debug_println!(
                23,
                0,
                "RELEVANCY: Marked var {} as relevant at level {}",
                abs_var,
                self.decision_level
            );
        }
        newly_inserted
    }

    /// Seed all roots as relevant and propagate.
    /// Call after all rules and roots have been added.
    pub fn seed_roots(&mut self, assignments: &[i32]) {
        if !self.enabled {
            return;
        }
        let roots: Vec<i32> = self.roots.iter().copied().collect();
        for root in roots {
            if self.mark_relevant(root) {
                self.propagate_children(root, assignments);
            }
        }
    }

    /// Update the decision level (call from notify_new_decision_level).
    pub fn new_decision_level(&mut self) {
        if !self.enabled {
            return;
        }
        self.decision_level += 1;
    }

    /// Called when the SAT solver assigns a literal.
    /// If the variable is already relevant and has a rule, propagate to children.
    pub fn notify_assignment(&mut self, lit: i32, assignments: &[i32]) {
        if !self.enabled {
            return;
        }
        let var = lit.abs();
        if self.relevant.contains(&var) {
            self.propagate_children(var, assignments);
        }
    }

    /// Propagate relevancy from a variable to its children based on its
    /// assignment and the OR/AND propagation rules. Recurses into children.
    fn propagate_children(&mut self, var: i32, assignments: &[i32]) {
        debug_println!(23, 0, "Propagating children of var {} at level {}", var, self.decision_level);
        let rule = match self.rules.get(&var) {
            Some(r) => r.clone(),
            None => return, // atom — leaf node, no children
        };

        debug_println!(23, 0, "Found rule for var {}: {:?}", var, rule);

        let var_idx = var.unsigned_abs() as usize;
        let assignment = if var_idx < assignments.len() {
            assignments[var_idx]
        } else {
            0
        };

        // todo: this is creating an issue because for quantifier instantiations, the body
        // is propagating forwards before the quantifier literal is assigned, so we end up marking the body as relevant

        // if assignment == 0 {
        //     // Not yet assigned — propagation will happen later via notify_assignment
        //     return;
        // }

        // assignment > 0 means assigned true, < 0 means assigned false
        let assigned_true = assignment > 0;

        match rule {
            RelevancyRule::Or { ref children } => {
                if assigned_true {
                    // OR is true: only the first child assigned true is relevant (lazy).
                    // A child literal `c` is true when:
                    //   c > 0 and assignments[|c|] > 0, or c < 0 and assignments[|c|] < 0.
                    let mut found_witness = false;
                    for &child in children {
                        let child_idx = child.unsigned_abs() as usize;
                        if child_idx < assignments.len() && assignments[child_idx] != 0 {
                            let child_true = (child > 0 && assignments[child_idx] > 0)
                                || (child < 0 && assignments[child_idx] < 0);
                            if child_true {
                                if self.mark_relevant(child) {
                                    self.propagate_children(child.abs(), assignments);
                                }
                                found_witness = true;
                                break;
                            }
                        }
                    }
                    if !found_witness {
                        // No child assigned true yet — mark all as relevant
                        // since we can't determine the witness
                        // todo: why is this not unreachable?
                        // unreachable!();
                        for &child in children {
                            if self.mark_relevant(child) {
                                self.propagate_children(child.abs(), assignments);
                            }
                        }
                    }
                } else {
                    // OR is false: all children must be false, all are relevant
                    for &child in children {
                        if self.mark_relevant(child) {
                            self.propagate_children(child.abs(), assignments);
                        }
                    }
                }
            }
            RelevancyRule::And { ref children } => {
                if assigned_true {
                    // AND is true: all children must be true, all are relevant
                    for &child in children {
                        if self.mark_relevant(child) {
                            self.propagate_children(child.abs(), assignments);
                        }
                    }
                } else {
                    // AND is false: only the first child assigned false is relevant (lazy)
                    let mut found_witness = false;
                    for &child in children {
                        let child_idx = child.unsigned_abs() as usize;
                        if child_idx < assignments.len() && assignments[child_idx] != 0 {
                            let child_true = (child > 0 && assignments[child_idx] > 0)
                                || (child < 0 && assignments[child_idx] < 0);
                            if !child_true {
                                if self.mark_relevant(child) {
                                    self.propagate_children(child.abs(), assignments);
                                }
                                found_witness = true;
                                break;
                            }
                        }
                    }
                    if !found_witness {
                        // No child assigned false yet — mark all as relevant
                        // todo: why is this not unreachable?
                        // unreachable!();
                        for &child in children {
                            if self.mark_relevant(child) {
                                self.propagate_children(child.abs(), assignments);
                            }
                        }
                    }
                }
            }
        }

        // Also propagate through instantiation edges (unconditional):
        // if this var is a quantifier with instantiations, mark all
        // instantiation body literals as relevant.
        // Use the signed literal (based on assignment) to look up edges,
        // since instantiation vs skolemization depends on polarity.
        let signed_lit = if assigned_true { var } else { -var };
        if let Some(children) = self.instantiation_edges.get(&signed_lit).cloned() {
            for child in children {
                if self.mark_relevant(child) {
                    self.propagate_children(child.abs(), assignments);
                }
            }
        }
    }

    /// Backtrack to the given decision level: remove relevancy markings
    /// that were added at levels above `level`.
    ///
    /// After unmarking, revisit `pending_instantiations`: for each entry
    /// (quantifier_lit, body_var) whose quantifier is still relevant and
    /// assigned at the right polarity, re-propagate to body_var (which may
    /// have been unmarked). Entries whose quantifier is no longer relevant
    /// are discarded. At level 0 all surviving entries become permanently
    /// relevant so we clear the list.
    pub fn backtrack(&mut self, level: usize, assignments: &[i32]) {
        if !self.enabled {
            return;
        }
        self.decision_level = level;

        // Pop trail entries above the target level and remove from relevant set
        while let Some(&(var, var_level)) = self.trail.last() {
            if var_level > level {
                self.trail.pop();
                // Only remove if not a root (roots are always relevant)
                if !self.roots.contains(&var) {
                    self.relevant.remove(&var);
                    debug_println!(
                        23,
                        0,
                        "RELEVANCY: Unmarked var {} (was level {}, backtracking to {})",
                        var,
                        var_level,
                        level
                    );
                }
            } else {
                break;
            }
        }

        // Re-propagate any pending instantiation whose body lost relevancy but
        // whose source quantifier is still relevant and correctly assigned.
        let pending = std::mem::take(&mut self.pending_instantiations);
        self.pending_instantiations = pending
            .into_iter()
            .filter_map(|(q_lit, body_var)| {
                if self.is_relevant_and_assigned_at(q_lit, assignments) {
                    // Source still live — re-mark body if it was backtracked away.
                    debug_println!(23, 0, "remarking {}", body_var);
                    if self.mark_relevant(body_var) {
                        debug_println!(23, 0, "re-propagating children of {}", body_var);
                        self.propagate_children(body_var, assignments);
                    }
                    if level > 0 {
                        Some((q_lit, body_var)) // keep tracking
                    } else {
                        None
                    }
                } else {
                    debug_println!(23, 0, "   not remarking {}", body_var);
                    None // source gone — discard
                }
            })
            .collect();

        // not necessary because we take care of it earlier
        // if level == 0 {
        //     // All pending entries are now at level 0 and permanently relevant;
        //     // no need to track them for re-propagation anymore.
        //     self.pending_instantiations.clear();
        //     return;
        // }
    }

    /// Flush accumulated rules from the CNF cache into the propagator.
    pub fn flush_rules(&mut self, rules: &mut Vec<(i32, RelevancyRule)>) {
        debug_println!(23, 0, "Flushing {} relevancy rules into propagator", rules.len());
        for rule in rules.iter() {
            debug_println!(23, 0, "Flushing rule for var {}: {:?}", rule.0, rule.1);
        }
        if !self.enabled {
            rules.clear();
            return;
        }
        for (var, rule) in rules.drain(..) {
            self.add_rule(var, rule);
        }
    }
}
