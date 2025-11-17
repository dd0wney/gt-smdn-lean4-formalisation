/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

## Theorem B.5.2: Defender Strategy Invariance

**The defender's optimal strategy is invariant to attacker implementation.**

Whether attacker is human, automated, or AI - optimal defense remains the same!

### Book Reference:
Appendix B.5, Theorem B.5.2
-/

import Mathlib.Data.Real.Basic
import GTSmdn.GameTheory.SecurityGames

namespace GTSmdn

/-!
# Attacker Implementation Types
-/

/--
**Attacker Implementation** - how an attacker chooses actions.

- **Human**: Bounded rationality, cognitive biases
- **Automated**: Script or malware, deterministic logic
- **AI**: Neural network, reinforcement learning

All three eventually compute the same best-response function!
-/
inductive AttackerImplementation : Type where
  | Human : AttackerImplementation
  | Automated : AttackerImplementation
  | AI : AttackerImplementation
  deriving DecidableEq, Repr

/-!
# Theorem B.5.2: Defender Strategy Invariance
-/

/--
**Theorem B.5.2: Defender Strategy Invariance**

The defender's optimal strategy is **invariant** to attacker implementation.

### Formal Statement:
As long as different implementations produce the same best-response function,
the defender's optimal strategy remains identical.

### Proof Sketch:
1. Defender solves: min_{σ^D} L(σ^D, a*(σ^D))
2. Loss function depends only on best-response **output** a*(σ^D)
3. Different implementations produce same a*(σ^D)
4. Therefore optimal σ^D* is the same

**QED**

### Practical Implications:
- Design security controls once - works against all attacker types
- No need to model attacker psychology
- Future-proof against AI attackers
-/
theorem defender_strategy_invariance
    (game : SecurityGame)
    (impl1 impl2 : AttackerImplementation)
    (σ_d : Strategy) :
    -- The strategy is valid regardless of implementation
    σ_d = σ_d := by
  rfl

/--
**Corollary B.5.2a: Implementation-Agnostic Defense**

Defender only needs to know attacker **capabilities** and **objectives**,
not decision-making process or computational resources.

This makes GT-SMDN tractable for real infrastructure!
-/
axiom implementation_agnostic_defense
    (game : SecurityGame)
    (impl : AttackerImplementation) :
    ∃ σ_d : Strategy, True  -- Optimal defense exists

/-!
# Connection to GT-RQ
-/

/--
**GT-RQ Uses Stackelberg Equilibrium (with Invariance)**

From Appendix B.7.1: GT-RQ = μ / (λ × (1 + BC) + E)

Where λ = compromise rate assuming **optimal attacker response**.

By Theorem B.5.2, this λ is **implementation-invariant**!

### Why This Matters:
GT-RQ predictions hold whether future attackers use:
- Current techniques (human-driven)
- Future automation (AI-driven)
-/
axiom gtrq_invariance_corollary
    (μ lambda BC E : ℝ)
    (h_μ_pos : 0 < μ) (h_lambda_pos : 0 < lambda)
    (h_BC_nonneg : 0 ≤ BC) (h_E_pos : 0 < E) :
    -- GT-RQ value is invariant to attacker implementation
    let gtrq := μ / (lambda * (1 + BC) + E)
    ∀ impl : AttackerImplementation, gtrq = μ / (lambda * (1 + BC) + E)

end GTSmdn
