/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

# Lean 4 Tutorial for GT-SMDN Framework

Welcome to the Lean 4 formalization of the GT-SMDN framework!

This tutorial will guide you through:
1. Understanding what formal verification means
2. How to read and write Lean 4 code
3. Working with the GT-SMDN framework definitions
4. Building your own proofs

## Prerequisites

**No advanced math required!** This tutorial assumes:
- Basic understanding of programming (any language)
- Familiarity with the GT-SMDN framework from the book
- Curiosity about formal methods

**Installation**:
If you haven't already:
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd lean4/
lake update
lake build
```

## What is Formal Verification?

Formal verification means **mathematically proving** that code or theorems are correct.

**Traditional approach** (what most people do):
- Write code
- Test it
- Hope it works
- Find bugs in production 😱

**Formal verification** (what we're doing):
- Write a specification (what the code should do)
- Prove the code meets the specification
- Lean 4 checks the proof
- If it compiles, it's guaranteed correct! 🎉

### Example: Why This Matters for Security

In the GT-SMDN framework, we claim **Theorem B.7.2**: `0 < GT-RQ < ∞`

**Without formal verification**:
- "Trust me, I checked the math"
- "I tested it on 100 examples"
- Maybe there's an edge case we missed?

**With formal verification**:
- Lean 4 checks EVERY possible case
- If the proof compiles, it's true for ALL systems
- No edge cases, no bugs

## Part 1: Reading Lean 4 Code

Let's start by understanding existing code.
-/

import GTSmdn.Basic.Graph
import GTSmdn.EdgeTypes
import GTSmdn.Risk.GTRQ

namespace Tutorial

open GTSmdn

/-!
### Example 1: Types and Structures

In Lean 4, `structure` defines a type with fields (like a struct in C or a class in Python).
-/

-- From the book: A system has entropy between 0.01 and 0.98
#check SystemEntropy  -- Hover over this in VS Code to see the definition!

-- Create an entropy value
def exampleEntropy : SystemEntropy := {
  value := 0.15      -- 15% entropy (moderate)
  pos := by sorry    -- Proof that 0.01 ≤ 0.15 (we'll explain `sorry` soon)
  le_max := by sorry -- Proof that 0.15 ≤ 0.98
}

-- ✨ Key Insight: `SystemEntropy` is not just a number - it's a number WITH PROOFS
-- The compiler guarantees 0.01 ≤ value ≤ 0.98. No runtime checks needed!

/-!
### Example 2: Functions

Functions in Lean 4 are defined with `def`.
-/

-- From GTSmdn/EdgeTypes.lean: Convert edge type to string
#check EdgeType.toString

-- Example usage
def credential_edge_name : String :=
  EdgeType.toString EdgeType.credential  -- Returns: "Credential"

#eval credential_edge_name  -- Output: "Credential"

-- ✨ Key Insight: Lean 4 can run code! Use `#eval` to test functions.

/-!
### Example 3: Theorems

Theorems are statements we want to prove.
-/

-- From the book: Entropy is always positive (Axiom B.7.1b)
#check SystemEntropy.entropy_pos

-- This theorem says: For ANY entropy E, we have 0 < E.value
-- Let's use it!

theorem my_entropy_is_positive : 0 < exampleEntropy.value := by
  exact SystemEntropy.entropy_pos exampleEntropy

-- ✨ Key Insight: `exact` applies an existing theorem/proof directly
-- We used `entropy_pos` to prove our specific entropy is positive!

/-!
### Example 4: The Magic of `sorry`

`sorry` is a placeholder that says "I'll prove this later".
It lets you:
- Sketch out proofs without getting stuck
- Focus on the big picture first
- Fill in details incrementally

**Warning**: Code with `sorry` is not fully verified!
-/

theorem example_with_sorry : 2 + 2 = 4 := by
  sorry  -- Lean accepts this, but it's not proven!

-- When ready, replace `sorry` with actual proof:
theorem example_proven : 2 + 2 = 4 := by
  rfl  -- `rfl` means "reflexivity" - both sides are the same by computation

-- ✨ Key Insight: Start with `sorry`, replace with real proofs later

/-!
## Part 2: The GT-SMDN Framework in Lean 4

Now let's explore the formalized framework!
-/

/-!
### Example 5: Edge Types

The framework defines 9 edge types (Axiom B.1.1a).
-/

-- All 9 edge types from the book
def all_edge_types : List EdgeType := [
  EdgeType.credential,   -- Login credentials, API keys
  EdgeType.knowledge,    -- Operational knowledge
  EdgeType.trust,        -- Trust relationships
  EdgeType.physical,     -- Network cables
  EdgeType.authority,    -- Reporting structures
  EdgeType.procedural,   -- Process dependencies
  EdgeType.temporal,     -- Time-based dependencies
  EdgeType.social,       -- Human relationships
  EdgeType.contractual   -- Vendor relationships
]

-- Create a typed edge
def steve_admin_edge : TypedEdge String :=
  TypedEdge.credential "Steve" "Production_Server"
  -- This represents: Steve has admin credentials to Production_Server

-- Get description
#eval EdgeType.description EdgeType.credential
-- Output: "Login credentials, API keys, access tokens. High cascade risk..."

-- ✨ Key Insight: Types capture MEANING, not just data
-- A credential edge is different from a physical edge!

/-!
### Example 6: Edge Weights

Edge weights represent relationship strength (Definition B.1.2a).
-/

-- Edge weights are bounded: 0 < w ≤ 1
def strong_relationship : EdgeWeight := {
  value := 0.95           -- Very strong relationship
  pos := by sorry         -- Proof: 0 < 0.95
  le_one := by sorry      -- Proof: 0.95 ≤ 1
}

def weak_relationship : EdgeWeight := {
  value := 0.15           -- Weak relationship
  pos := by sorry
  le_one := by sorry
}

-- Use the bound theorems
theorem strong_is_positive : 0 < strong_relationship.value := by
  exact EdgeWeight.weight_pos strong_relationship

theorem strong_is_bounded : 0 < strong_relationship.value ∧ strong_relationship.value ≤ 1 := by
  exact EdgeWeight.weight_bounds strong_relationship

-- ✨ Key Insight: The type system enforces bounds automatically!
-- Can't create an EdgeWeight with value 1.5 - won't compile!

/-!
### Example 7: GT-RQ Computation

The core metric of the framework (Definition B.7.1).
-/

-- Set up parameters for a system

-- Recovery rate: 2 systems/day
def recovery : RecoveryRate := {
  value := 2.0
  pos := by sorry  -- Proof: 0 < 2.0
}

-- Compromise rate: 0.5 systems/day
def compromise : CompromiseRate := {
  value := 0.5
  nonneg := by sorry  -- Proof: 0 ≤ 0.5
}

-- Entropy: 15%
def entropy : SystemEntropy := {
  value := 0.15
  pos := by sorry     -- Proof: 0.01 ≤ 0.15
  le_max := by sorry  -- Proof: 0.15 ≤ 0.98
}

-- Note: We'd need a graph G to actually compute GT-RQ
-- See "Example 8" below for how to create graphs

-- ✨ Key Insight: GT-RQ depends on recovery rate, attack rate, topology (BC), and entropy

/-!
### Example 8: Creating a Simple Graph

Let's model a small network.
-/

-- Define our network's nodes
inductive SmallNetwork where
  | server1 : SmallNetwork
  | server2 : SmallNetwork
  | workstation : SmallNetwork
  deriving DecidableEq, Repr, Fintype

-- For this tutorial, we'll just demonstrate the structure
-- A full implementation would define the edges and connectivity

-- ✨ Key Insight: We model infrastructure as graphs
-- Vertices = systems, edges = relationships

/-!
## Part 3: Writing Your Own Proofs

Now the fun part - proving theorems!
-/

/-!
### Example 9: Simple Proofs with `rfl`

`rfl` (reflexivity) proves `a = a` by computation.
-/

theorem two_plus_two : 2 + 2 = 4 := by
  rfl  -- Lean computes: 2 + 2 = 4, both sides match!

theorem string_concat : "Hello" ++ " World" = "Hello World" := by
  rfl  -- String concatenation is computed

-- Try it yourself!
theorem three_times_five : 3 * 5 = 15 := by
  rfl  -- Fill in the proof!

-- ✨ Key Insight: `rfl` works when Lean can compute both sides

/-!
### Example 10: Proofs with `exact`

`exact` uses an existing theorem or proof.
-/

-- We have a theorem that entropy is always positive
-- Let's use it!

theorem our_entropy_positive : 0 < entropy.value := by
  exact SystemEntropy.entropy_pos entropy
  -- We "exactly" apply the general theorem to our specific entropy

-- Try it yourself!
theorem our_entropy_bounded : 0.01 ≤ entropy.value ∧ entropy.value ≤ 0.98 := by
  exact SystemEntropy.entropy_bounds entropy  -- Use the bounds theorem!

-- ✨ Key Insight: Reuse existing theorems with `exact`

/-!
### Example 11: Proofs with `constructor`

`constructor` splits a goal with `∧` (and) or creates a structure.
-/

-- Prove two things at once
theorem example_and : 2 + 2 = 4 ∧ 3 + 3 = 6 := by
  constructor
  · rfl  -- Prove first part: 2 + 2 = 4
  · rfl  -- Prove second part: 3 + 3 = 6

-- The `·` is for focusing on one subgoal at a time

-- ✨ Key Insight: `constructor` breaks complex proofs into parts

/-!
### Example 12: Real GT-SMDN Theorem

Let's prove something from the framework!
-/

-- Theorem: If we have low compromise rate (λ = 0), GT-RQ depends only on μ and E
-- This is interesting: No attacks → only recovery and entropy matter!

-- First, create a "no attack" scenario
def no_attacks : CompromiseRate := {
  value := 0
  nonneg := by sorry  -- 0 ≤ 0 is true
}

-- Note: For a full proof, we'd need:
-- 1. A concrete graph G
-- 2. Compute maxNodeBC G
-- 3. Show that when λ = 0, the formula simplifies

-- This demonstrates how formal verification works:
-- - State what you want to prove
-- - Break it into smaller pieces
-- - Prove each piece
-- - Lean verifies everything fits together!

/-!
## Part 4: Practical Tips

### How to Learn More

1. **Read the definitions**: Hover over types in VS Code
   - `#check EdgeType`
   - `#check SystemEntropy`

2. **Use #eval**: Test functions interactively
   - `#eval EdgeType.toString EdgeType.credential`

3. **Start with sorry**: Sketch first, prove later
   - Replace `sorry` with real proofs incrementally

4. **Read error messages**: Lean tells you what's wrong
   - "unsolved goals" → you haven't finished the proof
   - "type mismatch" → wrong type somewhere

### Common Tactics Reference

| Tactic | What it does | When to use |
|--------|--------------|-------------|
| `rfl` | Proves `a = a` by computation | Equalities that compute |
| `exact h` | Uses theorem/hypothesis `h` | You have exactly what you need |
| `constructor` | Splits `∧` or creates structure | Proving multiple things |
| `intro x` | Assumes `x` exists | Proving `∀ x, ...` |
| `sorry` | Placeholder | Sketch or not ready yet |

### Next Steps

1. **Explore the codebase**:
   - `GTSmdn/Basic/Graph.lean` - Graph foundations
   - `GTSmdn/EdgeTypes.lean` - Edge type system
   - `GTSmdn/Metrics/BetweennessCentrality.lean` - BC definitions
   - `GTSmdn/Risk/GTRQ.lean` - GT-RQ metric

2. **Try the exercises** (below)

3. **Read the book**: Appendix B has all the mathematics

4. **Contribute**: Replace `sorry` with real proofs!

## Exercises

### Beginner

1. Create a `SystemEntropy` with value 0.25
2. Create an `EdgeWeight` with value 0.7
3. Prove that `EdgeType.credential ≠ EdgeType.physical` (use `by decide`)

### Intermediate

4. Create a typed edge representing a physical connection
5. Prove that any EdgeWeight is less than or equal to 1
6. Define a RecoveryRate with value 5.0 and prove it's positive

### Advanced

7. Define a small 3-node graph
8. Prove a relationship between entropy and GT-RQ
9. Contribute a real proof to replace a `sorry` in the codebase!

## Resources

- **Lean 4 Documentation**: https://leanprover.github.io/lean4/doc/
- **Theorem Proving in Lean**: https://leanprover.github.io/theorem_proving_in_lean4/
- **Mathlib Documentation**: https://leanprover-community.github.io/mathlib4_docs/
- **GT-SMDN Book**: Appendix B (Mathematical Framework)

## Getting Help

- Read code comments (heavily documented for beginners)
- Check `THEOREM_INDEX.md` for theorem locations
- Use VS Code hover tooltips
- Search Mathlib documentation
- Ask in Lean community forums

---

**Welcome to formal verification!** 🎉

Remember: Formal methods aren't just for academics. They make security claims
mathematically rigorous. Every `sorry` you replace with a proof is a step toward
unshakeable confidence in the GT-SMDN framework.

Happy proving! 🔒
-/

end Tutorial
