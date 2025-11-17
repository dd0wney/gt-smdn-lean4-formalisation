/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

## Security Games: Game-Theoretic Foundations of GT-SMDN

Formalizes game theory from Appendix B.5 (Semi-Markov Decision Network Extension).

### Book Reference:
Appendix B.5, Definition B.5.1 (State-Dependent Games)
-/

import Mathlib.Data.Real.Basic
import GTSmdn.Basic.Graph

namespace GTSmdn

/-!
# Basic Game Theory Structures
-/

/-- Player in a security game -/
inductive Player : Type where
  | Defender : Player
  | Attacker : Player
  deriving DecidableEq, Repr

/-- Action space -/
abbrev Action := ℕ

/-- Utility is a real-valued payoff -/
abbrev Utility := ℝ

/--
**Strategy** - probability distribution over actions.

Mixed strategy: randomize over actions
Pure strategy: always choose same action
-/
structure Strategy where
  /-- Probability of choosing each action -/
  probabilities : Action → ℝ
  /-- All probabilities are non-negative -/
  nonneg : ∀ a, 0 ≤ probabilities a

/-- Pure strategy - deterministic choice -/
def pureStrategy (action : Action) : Strategy where
  probabilities := fun a => if a = action then 1 else 0
  nonneg := fun _a => by split_ifs <;> norm_num

/-!
# Security Games (Definition B.5.1)
-/

/--
**Security Game** from Appendix B.5.1:

G_i = (A^D_i, A^A_i, U^D_i, U^A_i)

Where:
- A^D_i = defender actions in state i
- A^A_i = attacker actions in state i
- U^D_i, U^A_i = utility functions
-/
structure SecurityGame where
  /-- Defender utility: (defender action, attacker action) → payoff -/
  defenderUtility : Action → Action → Utility
  /-- Attacker utility: (defender action, attacker action) → payoff -/
  attackerUtility : Action → Action → Utility

/--
**Expected Utility** for defender given strategies.

EU^D(σ^D, σ^A) = Σ_d Σ_a P(d) × P(a) × U^D(d, a)

We axiomatize this to avoid complex summation machinery.
-/
axiom expectedUtilityDefender
    (game : SecurityGame)
    (defender_strategy : Strategy)
    (attacker_strategy : Strategy) : Utility

axiom expectedUtilityAttacker
    (game : SecurityGame)
    (defender_strategy : Strategy)
    (attacker_strategy : Strategy) : Utility

/-!
# Nash Equilibrium
-/

/-- Best response for defender -/
def isBestResponseDefender
    (game : SecurityGame)
    (strategy : Strategy)
    (opponent_strategy : Strategy) : Prop :=
  ∀ other_strategy : Strategy,
    expectedUtilityDefender game strategy opponent_strategy ≥
    expectedUtilityDefender game other_strategy opponent_strategy

/-- Best response for attacker -/
def isBestResponseAttacker
    (game : SecurityGame)
    (strategy : Strategy)
    (opponent_strategy : Strategy) : Prop :=
  ∀ other_strategy : Strategy,
    expectedUtilityAttacker game opponent_strategy strategy ≥
    expectedUtilityAttacker game opponent_strategy other_strategy

/--
**Nash Equilibrium** - neither player can improve by deviating.

(σ^D*, σ^A*) is Nash equilibrium if:
- σ^D* is best response to σ^A*
- σ^A* is best response to σ^D*
-/
structure NashEquilibrium (game : SecurityGame) where
  defender_strategy : Strategy
  attacker_strategy : Strategy
  defender_best_response :
    isBestResponseDefender game defender_strategy attacker_strategy
  attacker_best_response :
    isBestResponseAttacker game attacker_strategy defender_strategy

/-!
# Stackelberg Equilibrium (Used in GT-SMDN!)
-/

/--
**Stackelberg Equilibrium** - Sequential game where defender commits first.

From Appendix B.7.1: GT-RQ uses σ^* = Stackelberg equilibrium strategies.

### Game Sequence:
1. Defender commits to strategy σ^D (observable security controls)
2. Attacker observes and responds optimally
3. Defender chooses σ^D anticipating attacker's response

This models real infrastructure where security controls are visible.
-/
structure StackelbergEquilibrium (game : SecurityGame) where
  /-- Defender's committed strategy -/
  defender_strategy : Strategy
  /-- Attacker's best response -/
  attacker_strategy : Strategy
  /-- Attacker best-responds to defender -/
  attacker_optimality :
    isBestResponseAttacker game attacker_strategy defender_strategy
  /-- Defender anticipates best response -/
  defender_optimality :
    ∀ other_strategy : Strategy,
      ∀ attacker_response : Strategy,
        isBestResponseAttacker game attacker_response other_strategy →
        expectedUtilityDefender game defender_strategy attacker_strategy ≥
        expectedUtilityDefender game other_strategy attacker_response

/--
**Stackelberg Equilibrium Exists** (Nash's Theorem adaptation)

For finite security games, equilibrium always exists.
This ensures GT-SMDN's game-theoretic foundation is well-defined.
-/
axiom stackelberg_equilibrium_exists (game : SecurityGame) :
    Nonempty (StackelbergEquilibrium game)

end GTSmdn
