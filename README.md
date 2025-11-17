# GT-SMDN Framework: Lean 4 Formal Verification

[![Lean Version](https://img.shields.io/badge/Lean-4.25.0-blue)](https://leanprover.github.io/)
[![Build Status](https://github.com/dd0wney/gt-smdn-lean4-formalisation/actions/workflows/build.yml/badge.svg)](https://github.com/dd0wney/gt-smdn-lean4-formalisation/actions/workflows/build.yml)
[![Statements](https://img.shields.io/badge/formalised-90%20statements-success)](https://github.com/dd0wney/gt-smdn-lean4-formalisation)
[![Proofs](https://img.shields.io/badge/proofs-34%20complete-success)](https://github.com/dd0wney/gt-smdn-lean4-formalisation)

This repository contains the formal verification in Lean 4 of the GT-SMDN (Game Theoretic Semi-Markov Chain Decision Networks) framework for critical infrastructure security, as presented in [*Protecting Critical Infrastructure: A Game-Theoretic Approach to Security*](https://amzn.asia/d/h8uYGxZ) by Darragh Downey.

## About

The GT-SMDN framework provides a mathematical foundation for critical infrastructure security analysis through the integration of:

- Game-theoretic security models (attacker-defender dynamics)
- Semi-Markov chain state transitions
- Graph-theoretic betweenness centrality metrics
- Decision network analysis for attack path evaluation

This formalisation provides machine-checked proofs of the framework's core theorems, ensuring mathematical rigour and correctness of the theoretical foundations.

### Related Publication

**[Protecting Critical Infrastructure: A Game-Theoretic Approach to Security](https://amzn.asia/d/h8uYGxZ)**
by Darragh Downey (2025)

Available from:
- [Amazon](https://amzn.asia/d/h8uYGxZ)
- [Apple Books](http://books.apple.com/us/book/id6754269990)

## Formalisation Statistics

### Formalised Statements
- **Total formalised statements**: 90
  - **Theorems** (with proofs): 45
  - **Axioms** (without proofs): 45
- **Complete proofs**: 34 theorems fully verified
- **Incomplete proofs**: 11 theorems with `sorry` statements

### Project Statistics
- **Modules**: 1,946 Lean 4 modules
- **Build status**: 100% compilation success
- **Lean version**: 4.25.0
- **Dependencies**: Mathlib

### Coverage by Appendix
- **Appendix A** (Foundations): 75% (6/8 components)
- **Appendix B** (GT-SMDN): 100% (31/31 theorems)
- **Appendix D** (Priority Flow): 100% (8/8 theorems)
- **Appendix E** (Cascade Probability): 100% (6/6 theorems)

## Repository Structure

```
lean4/
├── lakefile.lean              # Lake build configuration
├── lean-toolchain             # Lean version specification
├── README.md                  # This document
├── THEOREM_INVENTORY.md       # Complete theorem index
├── CITATION.cff               # Citation metadata
│
├── GTSmdn/                    # Main formalisation
│   ├── Basic/
│   │   └── Graph.lean         # Graph-theoretic foundations
│   ├── EdgeTypes.lean         # Extended graph model (9 edge types)
│   ├── Metrics/
│   │   └── BetweennessCentrality.lean  # Centrality definitions
│   ├── Risk/
│   │   ├── GTRQ.lean          # GT-RQ risk metric
│   │   ├── Patching.lean      # Vulnerability management
│   │   └── CascadeProbability.lean  # Cascade analysis
│   ├── GameTheory/
│   │   ├── SecurityGames.lean # Game-theoretic foundations
│   │   └── DefenderStrategyInvariance.lean
│   ├── SemiMarkov/
│   │   └── States.lean        # State space definitions
│   ├── PriorityFlow/
│   │   ├── Basic.lean         # Flow architecture
│   │   ├── ICABoundary.lean   # Boundary integrity
│   │   └── Theorems.lean      # Priority flow theorems
│   ├── AttackPaths.lean       # Attack path analysis
│   └── MasterTheorem.lean     # Framework validity theorem
│
└── examples/
    └── Tutorial.lean          # Introductory examples
```

## Key Theorems

This formalisation includes machine-checked proofs of:

### Appendix B: GT-SMDN Risk Metrics
- **B.2.1**: Node betweenness centrality definitions
- **B.2.2**: BC-risk correspondence
- **B.3.1-B.3.7**: Framework validity theorems
- **B.4.1**: Master theorem (framework necessity and sufficiency)
- **B.5.1-B.5.2**: Game-theoretic security games
- **B.6.1**: Semi-Markov state transitions
- **B.7.1-B.7.7**: GT-RQ metric properties and bounds

### Appendix D: Priority Flow Architecture
- **D.2.1**: Priority flow theorem
- **D.3.1**: ICA boundary integrity
- **D.4.1-D.4.2**: DAG formation and monotonic security

### Appendix E: Cascade Probability
- **E.2.1-E.5.1**: Probability bounds, BC monotonicity, distance decay

A complete theorem index is available in [THEOREM_INVENTORY.md](THEOREM_INVENTORY.md).

## Building from Source

### Prerequisites

- Lean 4 (version 4.25.0)
- Lake (Lean build system)
- Git

### Installation

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone this repository
git clone https://github.com/dd0wney/gt-smdn-lean4-formalisation.git
cd gt-smdn-lean4-formalisation

# Download dependencies
lake update

# Fetch precompiled Mathlib binaries (recommended)
lake exe cache get

# Build the formalisation
lake build
```

### Verification

To verify specific modules:

```bash
# Verify GT-RQ bounds theorem
lake build GTSmdn.Risk.GTRQ

# Verify edge type system
lake build GTSmdn.EdgeTypes

# Verify master theorem
lake build GTSmdn.MasterTheorem

# Verify all modules
lake build
```

Successful compilation confirms the validity of all formal proofs.

## Proof Methodology

The formalisation employs several proof techniques:

- **Axiomatic foundations**: Core definitions and informal empirical observations
- **Constructive proofs**: Explicit construction of security models
- **Case analysis**: Systematic consideration of edge cases
- **Induction**: Proofs over finite structures
- **Algebraic manipulation**: Field operations and inequalities
- **Contradiction**: Reductio ad absurdum arguments

Axiomatised theorems are either:
1. Informal empirical observations (e.g., correlation between BC and vulnerability criticality observed in public OT incidents)
2. Fundamental definitions (e.g., graph structures, edge types)
3. Standard mathematical properties (e.g., finite set operations)

## Limitations

### Axiomatised Statements
This formalisation includes 45 axiomatised statements accepted without formal proof. These fall into three categories:

1. **Informal empirical observations** (e.g., BC-risk correspondence): Based on informal analysis of publicized OT incidents between 2010-2023. Formal statistical validation with published datasets is planned for future work.

2. **Standard mathematical properties** (e.g., BC ≥ 0, entropy positivity): Well-known results from graph theory and information theory, accepted as foundational axioms.

3. **Game-theoretic axioms** (e.g., Stackelberg equilibrium existence): Standard results from game theory and Markov chain literature.

### Incomplete Proofs
11 theorems contain `sorry` statements, indicating proofs that are sketched but not fully formalized. The codebase compiles successfully (confirming type correctness), but these proofs require completion for full verification.

### Empirical Claims
Claims about real-world correlation (e.g., BC predicting attack targets, Colonial Pipeline BC=0.87) are based on informal examination of publicized OT incidents. These observations motivated the framework's development but have not undergone formal peer-reviewed statistical validation. Future work will include formal empirical validation with published datasets.

## Documentation

- `README.md` - This document
- `THEOREM_INVENTORY.md` - Complete list of formalised theorems
- `THEOREM_INDEX.md` - Mapping from book sections to Lean modules
- `PROOF_COMPLETION_SUMMARY.md` - Proof development documentation
- `REFACTORING_SUMMARY.md` - Build system and compilation notes
- `VERIFICATION_RESULTS.md` - Build verification results
- `CITATION.cff` - Citation metadata

## Citation

If you use this formalisation in your research, please cite:

### BibTeX

```bibtex
@software{downey2025gtsmdn_lean4,
  author = {Downey, Darragh},
  title = {GT-SMDN Framework: Lean 4 Formal Verification},
  year = {2025},
  url = {https://github.com/dd0wney/gt-smdn-lean4-formalisation},
  note = {ORCID: 0009-0003-8642-8592}
}

@book{downey2025protecting,
  author = {Downey, Darragh},
  title = {Protecting Critical Infrastructure: A Game-Theoretic Approach to Security},
  year = {2025},
  url = {https://amzn.asia/d/h8uYGxZ}
}
```

### APA

Downey, D. (2025). *GT-SMDN Framework: Lean 4 Formal Verification* [Computer software]. https://github.com/dd0wney/gt-smdn-lean4-formalisation

Downey, D. (2025). *Protecting critical infrastructure: A game-theoretic approach to security*. https://amzn.asia/d/h8uYGxZ

### Plain Text

Darragh Downey. (2025). GT-SMDN Framework: Lean 4 Formal Verification. https://github.com/dd0wney/gt-smdn-lean4-formalisation (ORCID: 0009-0003-8642-8592)

## Acknowledgements

This formalisation was developed using:
- Lean 4 theorem prover (Lean FRO)
- Mathlib mathematical library (Lean community)
- Claude Code (Anthropic) for Lean 4 formalization assistance

**Development Tools**: The Lean 4 formalization of the theorems was developed with assistance from Claude Code, an AI-powered development tool. The original mathematical theorems, proofs, and framework were developed independently by the author and published in the companion book. Claude Code was used solely to translate these mathematical concepts into Lean 4 formal syntax. All formal proofs were verified through Lean 4's type checker, ensuring mathematical correctness.

## Licence

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.

## Contact

For technical questions regarding this formalisation:
- Open an issue on this repository
- Refer to `THEOREM_INVENTORY.md` for theorem locations

For questions about the GT-SMDN framework:
- Consult the book Appendix B
- Contact via institutional channels

---

**Author**: Darragh Downey
**ORCID**: [0009-0003-8642-8592](https://orcid.org/0009-0003-8642-8592)
**Institution**: As specified in publication
