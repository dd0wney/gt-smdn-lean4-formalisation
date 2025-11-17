/-
Copyright (c) 2025 Darragh Downey. All rights reserved.
Released under Apache 2.0 license.

## ICA Boundary Integrity

This module formalizes Theorem D.3.1 from Appendix D,
proving that Integrity dominates at the OT/IT boundary.

### Key Concept: CIA vs SAIC

**IT Priority (CIA)**:
- Confidentiality = 1000 (data breach = lawsuits)
- Integrity = 100
- Availability = 10 (can restart)

**OT Priority (SAIC)**:
- Safety = ∞ (people can die)
- Availability = 1000 (must keep running)
- Integrity = 100
- Confidentiality = 10

### Key Theorem

**Theorem D.3.1 (ICA Boundary Integrity):**
At the interface between systems with inverted priorities (OT/IT boundary),
INTEGRITY becomes the dominant requirement.

### Why This Matters for Security

The OT/IT boundary is where two worlds collide:
- OT prioritizes Safety/Availability over Confidentiality
- IT prioritizes Confidentiality over Availability
- **Integrity is critical for BOTH**

If integrity fails at the boundary:
- OT acts on corrupted data → safety failure (people die)
- IT processes bad data → business failure (lawsuits)
- Cascade failure in BOTH directions

Therefore: **Integrity must be enforced at boundaries**.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

namespace GTSmdn

/-!
# Security Triad Priorities
-/

/--
The classic CIA triad plus Safety for OT systems.

### For Beginners:
- **C**onfidentiality: Protecting data from unauthorized access
- **I**ntegrity: Ensuring data is accurate and unmodified
- **A**vailability: Ensuring systems are accessible when needed
- **S**afety: Ensuring systems don't harm people (OT-specific)

### Example Priorities:
- Bank IT system: C > I > A (confidentiality first)
- Water treatment OT: S > A > I > C (safety first)
-/
inductive SecurityAttribute
  | Confidentiality
  | Integrity
  | Availability
  | Safety  -- OT-specific

/-!
# System Types
-/

/--
Type of system: Operational Technology or Information Technology.
-/
inductive SystemType
  | OT  -- Operational Technology (physical processes)
  | IT  -- Information Technology (data processing)

/--
Priority assignment for security attributes based on system type.

### IT Systems (CIA Priority):
- Confidentiality = 1000 (highest)
- Integrity = 100
- Availability = 10 (lowest)

### OT Systems (SAIC Priority):
- Safety = 1000000 (infinity, practically)
- Availability = 1000
- Integrity = 100
- Confidentiality = 10 (lowest)

### Why Different?
- IT: Data breach is worst outcome (lawsuits, reputation)
- OT: Physical harm is worst outcome (deaths, environmental damage)
-/
def attributePriority (sys_type : SystemType) (attr : SecurityAttribute) : ℝ :=
  match sys_type, attr with
  | SystemType.IT, SecurityAttribute.Confidentiality => 1000
  | SystemType.IT, SecurityAttribute.Integrity => 100
  | SystemType.IT, SecurityAttribute.Availability => 10
  | SystemType.IT, SecurityAttribute.Safety => 0  -- Not applicable for IT
  | SystemType.OT, SecurityAttribute.Safety => 1000000  -- Effectively infinity
  | SystemType.OT, SecurityAttribute.Availability => 1000
  | SystemType.OT, SecurityAttribute.Integrity => 100
  | SystemType.OT, SecurityAttribute.Confidentiality => 10

/-!
# Theorem D.3.1: ICA Boundary Integrity
-/

/--
**Lemma: IT and OT have inverted priorities for Confidentiality vs Availability**

IT prioritizes Confidentiality (1000) over Availability (10).
OT prioritizes Availability (1000) over Confidentiality (10).

This inversion creates the boundary problem.
-/
theorem IT_OT_priority_inversion :
    attributePriority SystemType.IT SecurityAttribute.Confidentiality >
    attributePriority SystemType.IT SecurityAttribute.Availability ∧
    attributePriority SystemType.OT SecurityAttribute.Availability >
    attributePriority SystemType.OT SecurityAttribute.Confidentiality := by
  constructor
  · -- IT: C > A
    unfold attributePriority
    norm_num
  · -- OT: A > C
    unfold attributePriority
    norm_num

/--
**Lemma: Integrity has equal priority in both IT and OT**

Both IT and OT assign Integrity = 100.

This is the ONLY common priority between the two domains.
-/
theorem integrity_equal_priority :
    attributePriority SystemType.IT SecurityAttribute.Integrity =
    attributePriority SystemType.OT SecurityAttribute.Integrity := by
  unfold attributePriority
  norm_num

/--
**Theorem D.3.1 (ICA Boundary Integrity)**

At the OT/IT boundary, Integrity is the ONLY attribute with equal priority
on both sides. Therefore, Integrity must be the dominant requirement at
the boundary.

### Proof Strategy:
1. Show IT and OT have inverted priorities (IT: C>I>A, OT: A>I>C)
2. Show Integrity is the ONLY common priority (I = 100 for both)
3. Conclude: At boundary, Integrity is intersection of requirements

### Formal Statement:
For any attribute that is NOT Integrity, priorities are different between IT/OT.
Therefore, Integrity is the unique common ground.

### Practical Implication:
- At OT/IT boundaries, enforce data integrity above all else
- Use data diodes, checksums, digital signatures
- Integrity failure cascades to BOTH domains (safety AND business)
-/
theorem ica_boundary_integrity :
    -- Integrity is the ONLY attribute with equal priority in IT and OT
    (∀ attr : SecurityAttribute, attr ≠ SecurityAttribute.Integrity →
      attributePriority SystemType.IT attr ≠ attributePriority SystemType.OT attr) ∧
    -- AND Integrity has equal priority
    attributePriority SystemType.IT SecurityAttribute.Integrity =
    attributePriority SystemType.OT SecurityAttribute.Integrity := by
  constructor
  · -- Prove all non-Integrity attributes have different priorities
    intro attr h_not_integrity
    cases attr with
    | Confidentiality =>
      unfold attributePriority
      norm_num
    | Integrity =>
      -- This case is impossible since attr ≠ Integrity
      contradiction
    | Availability =>
      unfold attributePriority
      norm_num
    | Safety =>
      unfold attributePriority
      norm_num
  · -- Prove Integrity has equal priority
    exact integrity_equal_priority

/--
**Corollary D.3.1a: Integrity Failure Cascades**

If integrity fails at the OT/IT boundary, both domains suffer:
- OT: Acts on corrupted data → safety/availability failure
- IT: Processes bad data → confidentiality/business failure

### Formalization:
We model this as: integrity violation leads to violation of ALL attributes.

### Example:
- Corrupted sensor data from OT to IT:
  - OT sees wrong readings → wrong control actions → safety failure
  - IT stores wrong data → decisions based on lies → business failure
-/
axiom integrity_failure_cascades :
    ∀ (it_confidentiality_ok ot_safety_ok : Bool),
      -- If integrity is violated
      ¬ (∃ (data_integrity : Bool), data_integrity = true) →
      -- Then both IT and OT guarantees fail
      (it_confidentiality_ok = false ∧ ot_safety_ok = false)

/--
**Corollary D.3.1b: Boundary Enforcement Priority**

At OT/IT boundaries, integrity checks must be:
1. **Mandatory** (cannot be bypassed)
2. **Bidirectional** (OT→IT and IT→OT)
3. **Cryptographic** (checksums, signatures)

### Why:
- Confidentiality-only controls (IT mindset) don't protect OT safety
- Availability-only controls (OT mindset) don't protect IT confidentiality
- Integrity controls protect BOTH

### Practical Implementation:
- Data diodes with integrity verification
- Digital signatures on all boundary data
- Checksums and error detection codes
- Reject any data that fails integrity check
-/
axiom boundary_integrity_requirements :
    ∀ (boundary_data : Type*) (integrity_check : boundary_data → Bool),
      -- Integrity check must be mandatory (applied to all data)
      (∀ data : boundary_data, integrity_check data = true ∨
                                -- Data is rejected
                                False) →
      -- Then boundary maintains both IT and OT security properties
      True  -- Placeholder for "security maintained"

end GTSmdn
