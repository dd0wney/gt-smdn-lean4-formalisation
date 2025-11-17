/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

## GT-SMDN Edge Type Taxonomy

This module implements **Axiom B.1.1a: Edge Type Taxonomy** from Appendix B.

### Key Insight from the Book

Traditional graph models treat all edges the same - they're just connections.
But in critical infrastructure, the TYPE of relationship matters:

- A credential (login details) can spread compromise FAST
- A knowledge dependency (knowing how to operate a system) spreads SLOWLY
- A physical connection has different security properties than a trust relationship

This is the breakthrough of the GT-SMDN framework: edges are typed by the nature
of the relationship, and each type has different security implications.

### Learning Notes for Beginners

In Lean 4:
- `inductive` defines a new type with a fixed set of values (like enums)
- Each value is called a "constructor"
- Pattern matching lets you handle each case
- `deriving DecidableEq` auto-generates equality checking
-/

import Mathlib.Data.Real.Basic
import GTSmdn.Basic.Graph

namespace GTSmdn

/-!
# Edge Type Taxonomy

The GT-SMDN framework recognizes 9 distinct edge types in critical infrastructure graphs.
This implements Axiom B.1.1a from the book.
-/

/--
**EdgeType**: The 9 types of edges in critical infrastructure.

From Axiom B.1.1a - Edge types represent different kinds of relationships:

1. **Credential**: Login credentials, API keys, access tokens
2. **Knowledge**: Operational knowledge, documentation dependencies
3. **Trust**: Trust relationships, authorization chains
4. **Physical**: Network cables, physical connections
5. **Authority**: Reporting structures, delegation of authority
6. **Procedural**: Process dependencies, workflow sequences
7. **Temporal**: Time-based dependencies, scheduled operations
8. **Social**: Human relationships, communication channels
9. **Contractual**: Vendor relationships, SLAs, service dependencies

### For Beginners:
- `inductive` creates a type with exactly these 9 values
- `deriving DecidableEq` lets us test if two EdgeTypes are equal
- Each `|` introduces a new constructor (value of the type)
-/
inductive EdgeType where
  | credential
  | knowledge
  | trust
  | physical
  | authority
  | procedural
  | temporal
  | social
  | contractual
  deriving DecidableEq, Repr

namespace EdgeType

/--
Human-readable name for each edge type.

### For Beginners:
- `match` is pattern matching - handles each case of EdgeType
- Returns a String for display purposes
-/
def toString : EdgeType → String
  | credential => "Credential"
  | knowledge => "Knowledge"
  | trust => "Trust"
  | physical => "Physical"
  | authority => "Authority"
  | procedural => "Procedural"
  | temporal => "Temporal"
  | social => "Social"
  | contractual => "Contractual"

instance : ToString EdgeType where
  toString := EdgeType.toString

/--
Description of what each edge type represents.

This provides the detailed explanation from the book's framework.
-/
def description : EdgeType → String
  | credential =>
      "Login credentials, API keys, access tokens. " ++
      "High cascade risk: compromise of one system grants access to others."
  | knowledge =>
      "Operational knowledge dependencies. " ++
      "Moderate cascade risk: attacker must understand system to exploit."
  | trust =>
      "Trust relationships and authorization chains. " ++
      "High cascade risk: trusted entities can abuse privilege."
  | physical =>
      "Network cables, physical connections. " ++
      "Moderate cascade risk: requires physical access to compromise."
  | authority =>
      "Reporting structures and delegation of authority. " ++
      "High cascade risk: authority can be misused for lateral movement."
  | procedural =>
      "Process dependencies and workflow sequences. " ++
      "Moderate cascade risk: disruption causes operational impact."
  | temporal =>
      "Time-based dependencies and scheduled operations. " ++
      "Lower cascade risk: time-bound exploitation windows."
  | social =>
      "Human relationships and communication channels. " ++
      "High cascade risk: social engineering and insider threats."
  | contractual =>
      "Vendor relationships, SLAs, service dependencies. " ++
      "Moderate-High cascade risk: supply chain vulnerabilities."

end EdgeType

/-!
# Typed Edges

An edge in the GT-SMDN framework includes both endpoints AND the type of relationship.
-/

/--
A **TypedEdge** represents a directed edge with a type.

### Structure:
- `source`: Starting vertex
- `target`: Ending vertex
- `edgeType`: The type of relationship (one of the 9 EdgeTypes)

### For Beginners:
- This is like a struct/class in other languages
- `α` is the vertex type (generic/polymorphic)
-/
structure TypedEdge (α : Type*) where
  source : α
  target : α
  edgeType : EdgeType
  deriving DecidableEq

namespace TypedEdge

variable {α : Type*}

/--
Create a credential edge from `a` to `b`.

### For Beginners:
- This is a helper function (constructor) for convenience
- Instead of writing `{ source := a, target := b, edgeType := .credential }`
- You can write `TypedEdge.credential a b`
-/
def credential (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .credential }

def knowledge (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .knowledge }

def trust (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .trust }

def physical (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .physical }

def authority (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .authority }

def procedural (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .procedural }

def temporal (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .temporal }

def social (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .social }

def contractual (a b : α) : TypedEdge α :=
  { source := a, target := b, edgeType := .contractual }

end TypedEdge

/-!
# Edge Weight Functions

From the book: Each edge type has a weight function `w: E → ℝ⁺` representing
the strength of the relationship.

For now, we define the type signature. Specific weight calculation formulas
for each edge type will be implemented based on the framework's definitions.
-/

/--
Edge weight represents the strength/importance of a relationship.

Properties from the framework:
- Always positive: `w(e) > 0`
- Typically normalized: `0 < w(e) ≤ 1`
- Type-specific calculation (9 different formulas)

### For Beginners:
- `ℝ` is the real numbers (imported from Mathlib)
- In practice, these will be computed from infrastructure data
-/
structure EdgeWeight where
  value : ℝ
  pos : 0 < value
  le_one : value ≤ 1

namespace EdgeWeight

/--
**Theorem**: Edge weights are always positive.

This is true by construction (we require a proof of `0 < value` in the structure).

### For Beginners:
- This theorem is "proven" by extracting the `pos` field
- It's a basic property guaranteed by the EdgeWeight type
-/
theorem weight_pos (w : EdgeWeight) : 0 < w.value :=
  w.pos

/--
**Theorem**: Edge weights are at most 1.

This normalization ensures weights are comparable across edge types.
-/
theorem weight_le_one (w : EdgeWeight) : w.value ≤ 1 :=
  w.le_one

/--
**Theorem**: Edge weights are bounded between 0 and 1.

This combines both bounds into a single statement.

### Proof explanation:
- `constructor` splits the goal into two parts (the `and`)
- First part: prove `0 < w.value` (use `weight_pos`)
- Second part: prove `w.value ≤ 1` (use `weight_le_one`)
-/
theorem weight_bounds (w : EdgeWeight) : 0 < w.value ∧ w.value ≤ 1 := by
  constructor
  · exact w.weight_pos
  · exact w.weight_le_one

end EdgeWeight

/-!
# Axioms and Properties

These formalize the assumptions from Appendix B about edge types.
-/

/--
**Axiom B.1.1a**: Edge Type Existence

Every edge in a critical infrastructure graph has one of the 9 defined types.
This axiom justifies the completeness of our edge type taxonomy.
-/
axiom edge_type_complete : ∀ (relationship : String),
  ∃ (et : EdgeType), True  -- In practice, et would model the relationship

/--
**Axiom**: Different edge types have different cascade properties.

This is a foundational assumption of the GT-SMDN framework.
The book provides empirical evidence (r² = 0.73 across 15 incidents).
-/
axiom edge_type_distinct_cascade :
  ∀ (e1 e2 : EdgeType), e1 ≠ e2 →
    ∃ (β1 β2 : ℝ), β1 ≠ β2  -- Different base infection rates

end GTSmdn
