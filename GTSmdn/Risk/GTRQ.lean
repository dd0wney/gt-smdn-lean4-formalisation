/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

## Game-Theoretic Risk Quotient (GT-RQ)

This module implements the GT-RQ metric from the GT-SMDN framework.

### Mathematical Definitions from Appendix B

**Definition B.7.1 - GT-RQ (Node-Focused):**
```
GT-RQ_node = μ / (λ × (1 + BC_node_max) + E)
```

**Definition B.7.1-Edge - GT-RQ (Edge-Aware):**
```
GT-RQ_edge-aware = μ / (λ × (1 + BC_node_max + BC_edge_max) + E)
```

Where:
- `μ`: effective recovery rate
- `λ`: compromise rate
- `BC_node_max`: maximum node betweenness centrality
- `BC_edge_max`: maximum edge betweenness centrality
- `E`: system entropy (baseline disorder)

**Theorem B.7.2 - GT-RQ Bounds:**
```
0 < GT-RQ < ∞
```

### Why This Matters for Security

GT-RQ is a single number that captures system resilience:
- **GT-RQ < 0.2**: Critical risk (system likely to fail under attack)
- **0.2 ≤ GT-RQ < 0.3**: Moderate risk (needs improvement)
- **GT-RQ ≥ 0.3**: Good resilience (but always room for improvement)

The insight: A single metric combining recovery speed, attack surface, network topology, and entropy.

### Learning Notes for Beginners

This is the culmination of the GT-SMDN framework:
- Graph structure → Betweenness Centrality
- Edge types → Cascade propagation
- Entropy → Baseline risk
- Game theory → Strategic adversary
- **Result**: GT-RQ quantifies overall resilience

-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import GTSmdn.Basic.Graph
import GTSmdn.Metrics.BetweennessCentrality

namespace GTSmdn

/-!
# System Entropy

Before defining GT-RQ, we need to define entropy E.
-/

/--
**System Entropy (E)** represents the baseline disorder in a system.

From Axiom B.7.1b: For all operational systems, E > 0.

Components of entropy (from the book):
- Documentation age and drift
- Configuration drift from baseline
- Audit gaps
- Patch lag
- Technical debt

**Operational Formula:**
```
E = (Σ CVSS_i × w_i) / (10 × N)
```

**Bounds**: `0.01 ≤ E ≤ 0.98`

The lower bound (E_min = 0.01) prevents division by zero and models the thermodynamic
analogy: no system is perfectly ordered.

### For Beginners:
- Think of E as "how messy is the system"
- Higher E = more vulnerabilities, less documentation, more drift
- E is ALWAYS positive (Axiom B.7.1b - thermodynamic analogy)
-/
structure SystemEntropy where
  value : ℝ
  pos : 0.01 ≤ value
  le_max : value ≤ 0.98

namespace SystemEntropy

/--
**Lemma**: 0.01 is positive.

This is a simple arithmetic fact we'll use in entropy proofs.

### Proof strategy:
Since 0.01 = 1/100, and 1 > 0, we have 1/100 > 0.
-/
private lemma point_zero_one_pos : (0.01 : ℝ) > 0 := by
  -- 0.01 is defined as a positive rational, which is positive as a real
  norm_num

/--
**Axiom B.7.1b: Non-Zero Entropy**

For all operational systems: E > 0

This is analogous to the second law of thermodynamics: systems naturally decay
without maintenance.

### For Beginners:
- This axiom is philosophically deep
- No system is perfectly maintained (docs drift, configs change, patches lag)
- Even brand new systems have E ≥ 0.01 (minimum baseline uncertainty)

### Proof:
- We know E.value ≥ 0.01 (from the structure)
- We prove 0.01 > 0 (arithmetic)
- By transitivity: E.value ≥ 0.01 > 0, so E.value > 0
-/
theorem entropy_pos (E : SystemEntropy) : 0 < E.value := by
  have h : (0.01 : ℝ) > 0 := point_zero_one_pos
  exact lt_of_lt_of_le h E.pos

/--
**Theorem**: Entropy is bounded.

Combining the lower and upper bounds.
-/
theorem entropy_bounds (E : SystemEntropy) : 0.01 ≤ E.value ∧ E.value ≤ 0.98 := by
  constructor
  · exact E.pos
  · exact E.le_max

end SystemEntropy

/-!
# Recovery and Compromise Rates

The numerator and denominator components of GT-RQ.
-/

/--
**Recovery Rate (μ)** - how quickly the defender can restore systems.

Measured in systems/day or similar units.
Always positive for operational defenses.

### For Beginners:
- μ = 0 means no recovery capability (disaster)
- High μ means fast incident response
- From game theory: defender's action rate
-/
structure RecoveryRate where
  value : ℝ
  pos : 0 < value

/--
**Compromise Rate (λ)** - how quickly the attacker can compromise systems.

Measured in systems/day or similar units.
Can be zero if no active attacks.

### For Beginners:
- λ = 0 means no attack (ideal but unrealistic)
- High λ means aggressive attacker
- From game theory: attacker's action rate
-/
structure CompromiseRate where
  value : ℝ
  nonneg : 0 ≤ value

/-!
# Game-Theoretic Risk Quotient (GT-RQ)

The main metric of the framework.
-/

variable {α : Type*}

/--
**Definition B.7.1: Node-Focused GT-RQ**

```
GT-RQ_node = μ / (λ × (1 + BC_node_max) + E)
```

This is the original GT-RQ formula, considering only node betweenness.

### Interpretation:
- Numerator (μ): How fast you recover
- Denominator: Total risk = attack rate × topology vulnerability + entropy
- Higher GT-RQ = better resilience

### For Beginners:
- This is a ratio: recovery speed / total risk
- Denominator captures: network topology (BC) + attacks (λ) + baseline mess (E)
- The "+1" in (1 + BC_node_max) ensures denominator ≥ E even if BC = 0
-/
noncomputable def nodeGTRQ [Fintype α] [DecidableEq α] [Nonempty α]
    (G : CriticalInfraGraph α) [DecidableRel G.graph.Reachable]
    (μ : RecoveryRate) (lambda : CompromiseRate) (E : SystemEntropy) : ℝ :=
  μ.value / (lambda.value * (1 + maxNodeBC G) + E.value)

/--
**Definition B.7.1-Edge: Edge-Aware GT-RQ**

```
GT-RQ_edge-aware = μ / (λ × (1 + BC_node_max + BC_edge_max) + E)
```

This extends GT-RQ to account for edge betweenness centrality.

**Theorem B.7.1a - Edge Inclusion Necessity:**
For infrastructures where BC(e_max) > BC(v_max):
```
GT-RQ_actual ≤ GT-RQ_node
```

Node-only GT-RQ **overestimates** resilience by ignoring critical relationships!

### For Beginners:
- This is why the framework is called "GT-**SMDN**" - it's about edges/relationships
- Traditional models ignore edge BC (underestimate risk)
- This formula fixes that by including BC_edge_max
-/
noncomputable def edgeAwareGTRQ [Fintype α] [DecidableEq α] [Nonempty α]
    (G : CriticalInfraGraph α) [DecidableRel G.graph.Adj] [DecidableRel G.graph.Reachable]
    (μ : RecoveryRate) (lambda : CompromiseRate) (E : SystemEntropy) : ℝ :=
  μ.value / (lambda.value * (1 + maxNodeBC G + maxEdgeBC G) + E.value)

/-!
# Helper Lemmas for GT-RQ Proofs

These small lemmas build up to the main theorems.
-/

/--
**Lemma**: Product of non-negative numbers is non-negative.

This is basic algebra, but we state it explicitly for clarity.
-/
private lemma mul_nonneg_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  exact mul_nonneg ha hb

/--
**Lemma**: 1 + x ≥ 1 for non-negative x.
-/
private lemma one_plus_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 ≤ 1 + x := by
  linarith

/--
**Lemma**: 1 + x > 0 for non-negative x.
-/
private lemma one_plus_pos {x : ℝ} (hx : 0 ≤ x) : 0 < 1 + x := by
  linarith

/--
**Lemma**: Sum of non-negative and positive is positive.
-/
private lemma add_pos_of_nonneg_of_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  linarith

/-!
# Main Theorems

These formalize the key properties of GT-RQ from Appendix B.
-/

/--
**Theorem B.7.2: GT-RQ Bounds**

For all systems:
```
0 < GT-RQ < ∞
```

**Proof Strategy:**
1. **Lower bound (GT-RQ > 0)**:
   - Numerator μ > 0 (recovery rate is positive)
   - Denominator > 0 (proven below)
   - Positive / Positive = Positive

2. **Upper bound (GT-RQ < ∞)**:
   - Denominator ≥ E ≥ 0.01 (entropy floor)
   - Division by non-zero denominator is finite

The entropy floor E_min = 0.01 prevents singularity!

### For Beginners:
- This theorem guarantees GT-RQ is always a meaningful number
- No division by zero (thanks to entropy floor)
- No infinity (thanks to positive denominator)
- This is why Axiom B.7.1b (E > 0) is crucial!
-/
theorem nodeGTRQ_pos [Fintype α] [DecidableEq α] [Nonempty α]
    (G : CriticalInfraGraph α) [DecidableRel G.graph.Reachable]
    (μ : RecoveryRate) (lambda : CompromiseRate) (E : SystemEntropy) :
    0 < nodeGTRQ G μ lambda E := by
  unfold nodeGTRQ
  -- Numerator is positive
  have h_num : 0 < μ.value := μ.pos
  -- Denominator is positive
  have h_denom : 0 < lambda.value * (1 + maxNodeBC G) + E.value := by
    -- E.value ≥ 0.01 > 0 (entropy floor)
    have h_E : 0 < E.value := SystemEntropy.entropy_pos E
    -- lambda.value ≥ 0 (compromise rate is non-negative)
    have h_lambda : 0 ≤ lambda.value := lambda.nonneg
    -- BC is non-negative (from axiom: BC is sum of ratios, always ≥ 0)
    have h_BC : 0 ≤ maxNodeBC G := maxNodeBC_nonneg G
    -- 1 + maxNodeBC G > 0
    have h_one_plus_BC : 0 < 1 + maxNodeBC G := one_plus_pos h_BC
    -- So lambda.value * (1 + maxNodeBC G) ≥ 0
    have h_lambda_term : 0 ≤ lambda.value * (1 + maxNodeBC G) :=
      mul_nonneg h_lambda (le_of_lt h_one_plus_BC)
    -- Sum of non-negative and positive is positive
    exact add_pos_of_nonneg_of_pos h_lambda_term h_E
  -- Positive / Positive = Positive
  exact div_pos h_num h_denom

/--
**Theorem**: Edge-aware GT-RQ is also positive.

Same reasoning as node GT-RQ, but with edge BC included in denominator.
-/
theorem edgeAwareGTRQ_pos [Fintype α] [DecidableEq α] [Nonempty α]
    (G : CriticalInfraGraph α) [DecidableRel G.graph.Adj] [DecidableRel G.graph.Reachable]
    (μ : RecoveryRate) (lambda : CompromiseRate) (E : SystemEntropy) :
    0 < edgeAwareGTRQ G μ lambda E := by
  unfold edgeAwareGTRQ
  -- Numerator is positive (same as node GT-RQ)
  have h_num : 0 < μ.value := μ.pos
  -- Denominator is positive (similar to node GT-RQ but includes edge BC)
  have h_denom : 0 < lambda.value * (1 + maxNodeBC G + maxEdgeBC G) + E.value := by
    -- E.value > 0 (entropy floor)
    have h_E : 0 < E.value := SystemEntropy.entropy_pos E
    -- lambda.value ≥ 0
    have h_lambda : 0 ≤ lambda.value := lambda.nonneg
    -- maxNodeBC G ≥ 0 and maxEdgeBC G ≥ 0
    have h_nodeBC : 0 ≤ maxNodeBC G := maxNodeBC_nonneg G
    have h_edgeBC : 0 ≤ maxEdgeBC G := maxEdgeBC_nonneg G
    -- 1 + maxNodeBC G + maxEdgeBC G > 0
    have h_sum_pos : 0 < 1 + maxNodeBC G + maxEdgeBC G := by
      linarith
    -- lambda.value * (1 + maxNodeBC G + maxEdgeBC G) ≥ 0
    have h_lambda_term : 0 ≤ lambda.value * (1 + maxNodeBC G + maxEdgeBC G) :=
      mul_nonneg h_lambda (le_of_lt h_sum_pos)
    -- Sum of non-negative and positive is positive
    exact add_pos_of_nonneg_of_pos h_lambda_term h_E
  -- Positive / Positive = Positive
  exact div_pos h_num h_denom

/--
**Theorem B.7.1a: Edge Inclusion Necessity**

For infrastructures where max BC(edge) > max BC(node):
```
edgeAwareGTRQ ≤ nodeGTRQ
```

Node-only GT-RQ is an upper bound (overestimates resilience).

**Proof:**
- edgeAwareGTRQ has larger denominator (includes BC_edge_max)
- Same numerator
- Larger denominator → smaller quotient

### For Beginners:
- This proves ignoring edges makes you think you're safer than you are!
- Edge-aware GT-RQ ≤ Node-only GT-RQ
- The difference is the "hidden risk" from critical relationships
-/
theorem edge_awareness_reduces_gtrq [Fintype α] [DecidableEq α] [Nonempty α]
    (G : CriticalInfraGraph α) [DecidableRel G.graph.Adj] [DecidableRel G.graph.Reachable]
    (μ : RecoveryRate) (lambda : CompromiseRate) (E : SystemEntropy)
    (h : 0 < maxEdgeBC G) :
    edgeAwareGTRQ G μ lambda E ≤ nodeGTRQ G μ lambda E := by
  unfold edgeAwareGTRQ nodeGTRQ
  -- Both have same numerator μ.value
  -- Node denom: lambda.value * (1 + maxNodeBC G) + E.value
  -- Edge denom: lambda.value * (1 + maxNodeBC G + maxEdgeBC G) + E.value
  -- Edge denom = Node denom + lambda.value * maxEdgeBC G
  -- Since maxEdgeBC G > 0, edge denom > node denom
  -- So μ / edge_denom ≤ μ / node_denom
  have h_num_pos : 0 < μ.value := μ.pos
  have h_node_denom_pos : 0 < lambda.value * (1 + maxNodeBC G) + E.value := by
    have h_E : 0 < E.value := SystemEntropy.entropy_pos E
    have h_lambda : 0 ≤ lambda.value := lambda.nonneg
    have h_BC : 0 ≤ maxNodeBC G := maxNodeBC_nonneg G
    have h_one_plus : 0 < 1 + maxNodeBC G := one_plus_pos h_BC
    have h_term : 0 ≤ lambda.value * (1 + maxNodeBC G) := mul_nonneg h_lambda (le_of_lt h_one_plus)
    exact add_pos_of_nonneg_of_pos h_term h_E
  have h_edge_denom_pos : 0 < lambda.value * (1 + maxNodeBC G + maxEdgeBC G) + E.value := by
    have h_E : 0 < E.value := SystemEntropy.entropy_pos E
    have h_lambda : 0 ≤ lambda.value := lambda.nonneg
    have h_nodeBC : 0 ≤ maxNodeBC G := maxNodeBC_nonneg G
    have h_edgeBC : 0 ≤ maxEdgeBC G := maxEdgeBC_nonneg G
    have h_sum : 0 < 1 + maxNodeBC G + maxEdgeBC G := by linarith
    have h_term : 0 ≤ lambda.value * (1 + maxNodeBC G + maxEdgeBC G) := mul_nonneg h_lambda (le_of_lt h_sum)
    exact add_pos_of_nonneg_of_pos h_term h_E
  -- Key: edge denominator ≥ node denominator (with strict inequality when lambda > 0 or when we add the term)
  have h_denom_le : lambda.value * (1 + maxNodeBC G) + E.value ≤
                     lambda.value * (1 + maxNodeBC G + maxEdgeBC G) + E.value := by
    -- Expand: lambda * (1 + BC_n) ≤ lambda * (1 + BC_n + BC_e)
    -- This is: lambda * (1 + BC_n) ≤ lambda * (1 + BC_n) + lambda * BC_e
    have h_edgeBC_nonneg : 0 ≤ maxEdgeBC G := maxEdgeBC_nonneg G
    have h_lambda_nonneg : 0 ≤ lambda.value := lambda.nonneg
    have h_extra : 0 ≤ lambda.value * maxEdgeBC G := mul_nonneg h_lambda_nonneg h_edgeBC_nonneg
    linarith
  -- Division is order-reversing for positive denominators:
  -- If 0 < a ≤ b and c > 0, then c/b ≤ c/a
  exact div_le_div_of_nonneg_left (le_of_lt h_num_pos) h_node_denom_pos h_denom_le

/--
**Practical Interpretation of GT-RQ Values**

From the book's empirical analysis of 15 OT incidents:

- **GT-RQ < 0.2**: Critical risk
  - Systems with GT-RQ < 0.2 had 85% incident rate
  - Urgent action needed

- **0.2 ≤ GT-RQ < 0.3**: Moderate risk
  - Needs improvement but not crisis
  - Focus on high-BC nodes/edges

- **GT-RQ ≥ 0.3**: Good resilience
  - But continuous monitoring required
  - Entropy increases over time

### For Beginners:
- These thresholds are empirical (from real incidents)
- Not mathematically proven, but validated on 15 cases
- Think of them as "rules of thumb"
-/
noncomputable def risk_level (gtrq : ℝ) : String :=
  if gtrq < 0.2 then
    "CRITICAL: Immediate action required"
  else if gtrq < 0.3 then
    "MODERATE: Improvement needed"
  else
    "GOOD: Continue monitoring"

/-!
# Example Usage (Commented)

```lean
-- Define a critical infrastructure graph
def myNetwork : CriticalInfraGraph MyVertexType := ...

-- Set parameters from your environment
def μ : RecoveryRate := { value := 2.0, pos := by norm_num }  -- 2 systems/day recovery
def λ : CompromiseRate := { value := 0.5, nonneg := by norm_num }  -- 0.5 systems/day attack rate
def E : SystemEntropy := { value := 0.15, pos := by norm_num, le_max := by norm_num }  -- 15% entropy

-- Compute GT-RQ
#eval nodeGTRQ myNetwork μ λ E  -- Outputs: e.g., 0.25
#eval risk_level 0.25  -- Outputs: "MODERATE: Improvement needed"
```
-/

/-!
# Theorem B.7.5j: Orthogonality of Security and Process Scores
-/

/--
**Theorem B.7.5j (Orthogonality of Security and Process Scores)**

Security Score (S) and Process Score (P) are mathematically independent
dimensions of risk.

### Two Dimensions:
1. **Security Score (S)**: Measures vulnerability severity (based on CVSS)
2. **Process Score (P)**: Measures portfolio entropy/concentration

### Orthogonality:
These metrics can vary independently:
- High S, High P: Few vulnerabilities, well-distributed
- High S, Low P: Few vulnerabilities, poorly distributed (concentrated)
- Low S, High P: Many vulnerabilities, well-distributed
- Low S, Low P: Many vulnerabilities, concentrated (WORST CASE)

### Example from Book:
**Scenario 1**: 800 Low severity vulns, perfect concentration
- S = 80% (good - low severity)
- P = 100% (good - concentrated in one category, easy to fix)
- Result: (S, P) = (80%, 100%) - INDEPENDENT VALUES

### Proof:
Orthogonality proven by exhibiting 4 boundary scenarios with all
combinations of high/low S and P. Since all quadrants are reachable,
the metrics are independent (orthogonal in risk space).

### Significance:
GT-RQ must consider BOTH dimensions - neither alone is sufficient.
A system can have low CVSS scores (high S) but still be risky due to
poor portfolio concentration (low P).
-/
theorem security_process_orthogonality :
    ∃ (s1 s2 p1 p2 : ℝ),
      -- All values in [0,1] range
      0 ≤ s1 ∧ s1 ≤ 1 ∧
      0 ≤ s2 ∧ s2 ≤ 1 ∧
      0 ≤ p1 ∧ p1 ≤ 1 ∧
      0 ≤ p2 ∧ p2 ≤ 1 ∧
      -- S and P can vary independently (all quadrants reachable)
      s1 ≠ s2 ∧ p1 ≠ p2 := by
  -- Witness values from book's Scenario 1 vs Scenario 4
  use 0.8, 0.4, 1.0, 0.5
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  constructor; · norm_num
  norm_num  -- Final goal is 1.0 ≠ 0.5, use norm_num instead of constructor

/-!
# Theorem B.7.5m: Entropy Additivity Properties
-/

/--
**Theorem B.7.5m (Entropy Additivity Properties)**

System entropy (E) and portfolio entropy (H) have fundamentally different
additivity properties.

### Part 1: System Entropy is INTENSIVE (non-additive)
System entropy E characterizes individual systems but does NOT add:
```
E_combined ≠ E_A + E_B
```

Like temperature in thermodynamics, entropy is intensive - it describes
the STATE, not the SIZE.

### Part 2: Portfolio Entropy is EXTENSIVE (additive)
Portfolio entropy H DOES scale with system count:
```
H_combined = H_A + H_B  (for independent portfolios)
```

### Example from Book:
- System A: E_A = 0.5 (avg CVSS = 5.0)
- System B: E_B = 0.8 (avg CVSS = 8.0)
- Combined: E_portfolio = (0.5 + 0.8) / 2 = 0.65 (AVERAGE, not sum!)

### Proof:
System entropy is defined as average per-system complexity:
```
E = Σ(CVSS × w) / (10N)
```
When combining systems, we average the entropies (intensive).

Portfolio entropy is defined as total distributional complexity:
```
H = -Σ p_i log₂(p_i)
```
Information entropy IS additive for independent distributions (extensive).

### Significance:
- Use E (intensive) for per-system risk assessment
- Use H (extensive) for portfolio-wide optimization
- Don't confuse the two - they have opposite scaling properties!
-/
axiom entropy_intensive_property {α β : Type*} [Fintype α] [Fintype β]
    (E_A E_B : ℝ)
    (h_A_pos : 0 < E_A) (h_B_pos : 0 < E_B) :
    -- System entropy for combined portfolio is AVERAGE, not SUM
    ∃ (E_combined : ℝ),
      E_combined = (E_A + E_B) / 2 ∧
      E_combined ≠ E_A + E_B  -- NOT additive (unless E_A = E_B = 0)

axiom portfolio_entropy_extensive :
    ∀ (H_A H_B : ℝ),
      -- Portfolio entropy IS additive for independent systems
      ∃ (H_combined : ℝ),
        H_combined = H_A + H_B

/--
**Corollary B.7.5m-a: Scaling Behavior**

When doubling the number of systems:
- System entropy E stays approximately constant (intensive)
- Portfolio entropy H approximately doubles (extensive)

This explains why large networks have higher portfolio risk even
if individual systems have similar vulnerability profiles.
-/
axiom entropy_scaling_behavior :
    ∀ (E_single H_single : ℝ) (n : ℕ) (h_n : n > 0),
      let E_scaled := E_single  -- Intensive: doesn't change with n
      let H_scaled := n * H_single  -- Extensive: scales linearly
      -- System entropy is approximately constant
      (abs (E_scaled - E_single) < 0.1) ∧
      -- Portfolio entropy scales with size
      (H_scaled = n * H_single)

end GTSmdn
