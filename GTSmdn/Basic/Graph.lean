/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

## GT-SMDN Graph Theory Foundations

This module provides the basic graph theory definitions needed for the GT-SMDN framework.
It implements Axiom B.1.1 from the book: Network Graph Representation.

### Learning Notes for Lean 4 Beginners

Lean 4 is a theorem prover where you:
1. Define structures and types
2. State theorems about them
3. Prove theorems using tactics

Key syntax:
- `structure` defines a new type with fields
- `def` defines a function or value
- `theorem` states something to prove
- `by` starts a proof using tactics
- Common tactics: `intro`, `apply`, `exact`, `rw` (rewrite), `simp` (simplify)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Basic Graph Definitions

We build on Mathlib's SimpleGraph to add the specific structures needed for
critical infrastructure modeling in the GT-SMDN framework.
-/

-- Define a universe variable for types (Lean's way of handling type hierarchies)
universe u v

namespace GTSmdn

/--
A `CriticalInfraGraph` represents a critical infrastructure system as a graph.

This implements **Axiom B.1.1: Network Graph Representation** from Appendix B:
"Critical infrastructure systems can be modeled as graphs G = (V, E) where:
- V: vertices representing components (servers, switches, humans, processes, software)
- E: edges representing dependencies, connections, flows, trust relationships"

### For Beginners:
- `structure` creates a new type with named fields
- `α` is a type parameter (like generics in other languages)
- `[DecidableEq α]` means we can check if two vertices are equal
- `[Fintype α]` means there are finitely many vertices
- We don't require connectivity to allow representing disconnected networks
-/
structure CriticalInfraGraph (α : Type u) where
  /-- The underlying simple graph structure -/
  graph : SimpleGraph α

namespace CriticalInfraGraph

-- Make α implicit in the following definitions
variable {α : Type u}

/--
The number of vertices in the graph.

### For Beginners:
- `def` defines a function
- `: ℕ` specifies the return type (natural numbers)
- `Fintype.card α` counts the elements of type α
-/
def numVertices [Fintype α] (_G : CriticalInfraGraph α) : ℕ :=
  Fintype.card α

/--
The degree of a vertex (number of edges connected to it).

### For Beginners:
- We define degree as the number of neighbors
- A neighbor is a vertex v such that there's an edge to it
- We count the neighbors using Finset.card
-/
def degree [Fintype α] [DecidableEq α] (G : CriticalInfraGraph α) [DecidableRel G.graph.Adj] (v : α) : ℕ :=
  (Finset.univ.filter (fun w => G.graph.Adj v w)).card

/-!
## Basic Theorems

These simple theorems demonstrate how to prove properties in Lean 4.
They're not deep mathematical results, but good learning examples.
-/

/--
**Theorem**: The number of vertices is always non-negative.

### Proof explanation:
- This is trivially true because cardinality returns a natural number
- Natural numbers are always ≥ 0 by definition
-/
theorem numVertices_nonneg [Fintype α] (G : CriticalInfraGraph α) : 0 ≤ G.numVertices := by
  exact Nat.zero_le _

/--
**Theorem**: In any graph, every vertex has degree ≥ 0.

### Proof explanation:
- This is trivially true because degree returns a natural number (it's the cardinality of a set)
- Natural numbers are always ≥ 0 by definition
-/
theorem degree_nonneg [Fintype α] [DecidableEq α] (G : CriticalInfraGraph α) [DecidableRel G.graph.Adj] (v : α) :
    0 ≤ G.degree v := by
  exact Nat.zero_le _

/--
**Axiom B.1.1**: Graph representation axiom.

This states that critical infrastructure systems can be represented as graphs.
Since this is an axiom (not proven from more basic principles), we state it
but don't provide a proof.

### For Beginners:
- `axiom` declares something we assume to be true without proof
- Use axioms sparingly - they're the foundations of your theory
- This axiom is justified by empirical observation and the book's framework
-/
axiom network_representable (InfrastructureSystem : Type u) :
    ∃ (α : Type u), Nonempty (CriticalInfraGraph α)

end CriticalInfraGraph

/-!
## Example Usage

Here's how to use these definitions (commented out for now):

```lean
-- Define vertices for a simple network
inductive SimpleNetwork
  | server1
  | server2
  | switch
  | workstation
  deriving DecidableEq, Fintype

-- Create a graph (you'd need to define the actual edges)
def exampleGraph : CriticalInfraGraph SimpleNetwork := {
  graph := ...,  -- Define edges here
  connected := ...  -- Prove it's connected
}

-- Query the graph
#eval exampleGraph.numVertices  -- Would output: 4
```
-/

end GTSmdn
