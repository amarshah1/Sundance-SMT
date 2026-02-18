# Relevancy Filtering for Quantifier Instantiation

## Overview

This document describes the relevancy filtering feature added to Sundance. Relevancy propagation tracks which SAT variables are "relevant" — i.e., their truth value actually matters for determining satisfiability of the top-level formula. Irrelevant quantifiers are skipped during instantiation, avoiding unnecessary E-matching work.

## Motivation

In DPLL(T)-based SMT solvers, the SAT engine assigns Boolean values to all atoms, but many are "don't cares." For example, in `(or A B)` where `A` is true, the value of `B` doesn't matter. Without relevancy filtering, Sundance would instantiate quantifiers inside `B` even though their truth value is irrelevant. This wastes time on E-matching and generates unnecessary clauses.

## Flag

```
--relevancy <true|false>    (default: true)
```

When disabled (`--relevancy false`), `is_relevant()` always returns `true`, making the feature a no-op.

## Files Modified

### `src/config.rs`
- Added `--relevancy` CLI flag (default `true`).

### `src/relevancy.rs` (NEW)
Core implementation of the relevancy propagator.

**Data structures:**
- `RelevancyRule` enum: `Or { children: Vec<i32> }`, `And { children: Vec<i32> }` — describes the boolean structure of Tseitin variables.
- `RelevancyPropagator` struct:
  - `rules: HashMap<i32, RelevancyRule>` — structural rules from Tseitin encoding (1-to-1 per Tseitin var).
  - `instantiation_edges: HashMap<i32, Vec<i32>>` — keyed on **signed** SAT literal. Maps a quantifier literal (with specific polarity) to body literals that should become relevant when the quantifier is. Signed because Forall-positive triggers instantiation while Forall-negative triggers skolemization, producing different body literals.
  - `relevant: HashSet<i32>` — set of SAT variables currently marked relevant.
  - `roots: HashSet<i32>` — top-level assertion roots (always relevant).
  - `trail: Vec<(i32, usize)>` — records `(variable, decision_level)` for each marking, enabling efficient backtracking.
  - `decision_level: usize` — current decision level.

**Key methods:**
- `add_rule()` — register a Tseitin variable's OR/AND structure.
- `add_root()` — register a top-level assertion root.
- `add_instantiation_edge()` — register quantifier → body relevancy edge (signed key).
- `is_relevant()` — check if a variable is relevant (returns `true` when disabled).
- `mark_relevant()` — mark a variable relevant and push to trail.
- `seed_roots()` — mark all roots relevant and propagate.
- `notify_assignment()` — called when SAT assigns a literal; propagates to children if relevant.
- `propagate_children()` — recursive propagation based on OR/AND rules and assignment values.
- `backtrack()` — pop trail entries above target level, re-propagate from remaining relevant vars.
- `flush_rules()` — transfer accumulated rules from `CNFCache` staging buffer into the propagator.
- `new_decision_level()` — increment internal decision level counter.

### `src/lib.rs`
- Added `pub mod relevancy;`.

### `src/cnf.rs`
- Added `use crate::relevancy::RelevancyRule;`.
- Added `relevancy_rules: Vec<(i32, RelevancyRule)>` and `relevancy_roots: Vec<i32>` fields to `CNFCache`.
- In `cnf_nnf_tseitin`, AND and OR branches now push `(nv, RelevancyRule::And/Or { children: vs })` to `cnf_cache.relevancy_rules` after creating Tseitin clauses.
- Note: rules are also recorded for non-root nodes (e.g., boolean args inside function applications), but these are harmless since propagation only reaches vars reachable from roots.

### `src/egraphs/egraph.rs`
- Added `use crate::relevancy::RelevancyPropagator;`.
- Added `pub relevancy: RelevancyPropagator` field to `Egraph`.
- Added `relevancy_enabled: bool` parameter to `Egraph::new()`.

### `src/main.rs`
- Passes `args.relevancy` to `Egraph::new()`.
- After each assertion's CNF encoding, records the root SAT variable via `egraph.relevancy.add_root(root_var)` using `cnf_cache.var_map[nnf_term.uid()]`.
- After the CNF loop, calls `flush_rules()` and `seed_roots()`.

### `src/cadical_propagator.rs`
- In `notify_assignment`: calls `egraph.relevancy.notify_assignment(lit, assignments)` after recording the assignment.
- In `notify_new_decision_level`: calls `egraph.relevancy.new_decision_level()`.
- In `notify_backtrack`: calls `egraph.relevancy.backtrack(level, assignments)` after resetting assignments.
- In `cb_check_found_model`: calls `egraph.relevancy.flush_rules()` after `instantiate_quantifiers` returns, to incorporate new Tseitin rules from instantiated terms.

### `src/quantifiers/quantifier.rs`
- After checking quantifier assignment, added relevancy gate:
  ```rust
  if !egraph.relevancy.is_relevant(quantifier_literal) { continue; }
  ```
  If relevancy filtering is disabled, `is_relevant` returns `true` (no-op).
- **Instantiation path**: added `assert!(final_clause.len() == 1)` and `assert!(body_lit == egraph.get_lit_from_term(&nnf_term))` to validate the final clause structure. Registers instantiation edge via `egraph.relevancy.add_instantiation_edge(-quantifier_literal, body_lit)`.
- **Skolemization path**: registers instantiation edge via `egraph.relevancy.add_instantiation_edge(-quantifier_literal, skolemized_term_literal)`.
- In both cases, `-quantifier_literal` is used because the clause `[quantifier_literal, body]` means `¬quantifier_literal ⟹ body`, so `-quantifier_literal` is the active polarity that triggers the body.

## Propagation Rules

| Connective | Assigned Value | Which children become relevant? |
|---|---|---|
| **OR** | true | First child assigned true (lazy — one witness suffices) |
| **OR** | false | All children (every disjunct must be false) |
| **OR** | unassigned | None yet — propagation deferred to `notify_assignment` |
| **AND** | true | All children (every conjunct must be true) |
| **AND** | false | First child assigned false (lazy — one falsifier suffices) |
| **AND** | unassigned | None yet — propagation deferred to `notify_assignment` |
| **Instantiation edge** | N/A | Unconditional: if quantifier is relevant, body is relevant |

When no witness/falsifier is found (e.g., children not yet assigned), all children are conservatively marked relevant as a fallback.

## Backtracking

The trail records `(variable, decision_level)` for each relevancy marking. On backtrack to level `L`:
1. Pop trail entries with level > `L`, removing them from the relevant set (unless they're roots).
2. Re-propagate from all still-relevant variables to handle any structural changes.

---

## Future Work: Term-Level Relevancy Filtering

The current implementation is **coarse-grained**: it tracks relevancy at the boolean formula structure level and uses it to skip entire quantifiers. Z3 goes further with **term-level relevancy**, which would also filter which e-graph terms are fed to the E-matching engine. Here's what would be needed:

### 1. E-node Relevancy Tracking

Add a relevancy flag to each e-node in the e-graph. An e-node becomes relevant when:
- It appears as a subterm of a relevant boolean atom.
- It's created by a congruence closure step involving relevant terms.
- It's part of a relevant quantifier's trigger pattern match.

This would require modifying `egraph.rs` to maintain a `relevant_enodes: HashSet<u64>` set.

### 2. Relevant E-node Callback

Similar to Z3's `relevant_eh(enode)`, add a callback that fires when an e-node becomes relevant. This would notify the E-matching engine:

```rust
// In egraph or a new relevancy module:
fn relevant_eh(&mut self, term_uid: u64) {
    // Notify the matching engine that this term is now available
    // for trigger pattern matching
}
```

### 3. Filter Function Maps by Relevancy

Currently, `function_maps` contains all function applications in the e-graph, and `match_term` iterates over all of them. With term-level relevancy:

- `find_assignments_on_term` would skip terms in `function_maps` that aren't relevant.
- Alternatively, maintain a separate `relevant_function_maps` that only contains relevant terms, updated incrementally as terms become relevant.

### 4. Propagation Through the E-graph

When a boolean atom like `f(a, b) = g(c)` becomes relevant:
- Mark `f(a, b)`, `g(c)`, `a`, `b`, `c` as relevant e-nodes.
- When congruence closure merges two relevant e-classes, the merged class is relevant.
- When a new term is created by quantifier instantiation, it inherits relevancy from its parent quantifier.

### 5. Integration Points

The main changes would be in:
- `egraphs/congruence_closure.rs` — propagate relevancy through unions.
- `quantifiers/quantifier.rs` — filter `function_maps` iteration in `find_assignments_on_term`.
- `cadical_propagator.rs` — mark atoms relevant when they're assigned and the corresponding boolean variable is relevant.

### 6. Expected Impact

Term-level filtering would primarily help on problems with many function applications where only a small fraction are relevant to the current branch of the search. The coarse-grained approach already handles the common case of irrelevant quantifiers; term-level filtering would additionally reduce the cost of E-matching for relevant quantifiers by shrinking the candidate set.
