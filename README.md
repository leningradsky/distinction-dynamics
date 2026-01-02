# Distinction Dynamics — Formal Verification in Agda

## Overview

This project formally derives the structure of physics from a single axiom:

```
Δ ≠ ∅  (Distinction exists)
```

**17 modules, ~8000 lines of verified Agda code.**

## The Derivation Chain

```
Δ ≠ ∅
  │
  ▼
TRIADA (minimal closure requires 3 elements)
  │
  ├─► S₃ → SU(2) → Spin 1/2 → DIRAC EQUATION
  │
  ├─► U(1) phase → A_μ → MAXWELL → QED
  │
  └─► SU(3) → QCD (confinement, asymptotic freedom)
  │
  ▼
SU(3) × SU(2) × U(1) = STANDARD MODEL
  │
  ▼
Δ⁴-INVARIANTS
  ├─► ⟨I - G⟩ = 0 (balance)
  ├─► D_{n+1}/D_n → φ (golden ratio)
  ├─► 0 < S_loc < ∞ (entropy)
  └─► c = const (speed limit)
  │
  ▼
MINKOWSKI → EINSTEIN → COSMOLOGY
  │
  ▼
THERMODYNAMICS (second law, arrow of time)
```

## Modules

| Module | Lines | Content |
|--------|-------|---------|
| DistinctionDynamics.agda | 348 | Main module, overview |
| S3toSO3.agda | 422 | S₃ → SO(3), A₃ ≅ Z₃ |
| TriadSU2.agda | 522 | Z₆ → Z₃ double covering |
| TriadToSU2.agda | 673 | Rotation matrices |
| SpinorPhysics.agda | 581 | Pauli, spinors, 360°→-1 |
| Electroweak.agda | 486 | SU(2)×U(1), generations |
| Delta4Invariants.agda | 491 | Balance, φ, entropy, c |
| Gravity.agda | 446 | Curvature, Einstein, Λ |
| QuantumMechanics.agda | 477 | Wave function, Born |
| ParticleMasses.agda | 495 | Higgs, mass gap |
| Maxwell.agda | 440 | F_μν, Maxwell equations |
| Thermodynamics.agda | 366 | Second law, Landauer |
| Dirac.agda | 519 | Clifford, Dirac equation |
| QED.agda | 378 | Quantum electrodynamics |
| QCD.agda | 480 | Strong force, confinement |
| Cosmology.agda | 430 | Friedmann, inflation, Λ(t) |
| StandardModel.agda | 446 | Complete SM unification |

## Requirements

- **Agda** version 2.6.x or later
- No external libraries required (self-contained)

### Installing Agda

Ubuntu/Debian:
```bash
sudo apt install agda
```

macOS (Homebrew):
```bash
brew install agda
```

From Hackage:
```bash
cabal install Agda
```

## Compilation

### Compile all modules:
```bash
./compile.sh
```

### Compile individual module:
```bash
agda --safe ModuleName.agda
```

### Check without compiling:
```bash
agda --safe --only-scope-checking ModuleName.agda
```

## Verified Results

### Testable Predictions

| Prediction | DD Value | Experiment | Status |
|------------|----------|------------|--------|
| Mass gap QCD | φ·Λ ≈ 1.6 GeV | 1.5-1.7 GeV | ✓ |
| m_H / m_W | ≈ φ = 1.618 | 1.555 | 4% off |
| v_gravity = c | exactly c | \|c_gw-c\|/c < 10⁻¹⁵ | ✓ |
| 3 generations | = Triada | 3 | ✓ |
| 3 colors | = Triada | 3 | ✓ |
| Λ > 0 | background Δ-activity | accelerating ✓ | ✓ |

### Derived (not postulated)

- Spin 1/2 from double covering Z₆ → Z₃
- Standard Model gauge group SU(3)×SU(2)×U(1)
- Speed of light c = const
- Minkowski signature (+,-,-,-)
- Maxwell equations from U(1)
- Dirac equation from Clifford algebra
- Second law of thermodynamics
- Arrow of time

## Philosophy

**Standard approach:** ~30 parameters postulated, structure given empirically

**DD approach:** One axiom, everything else follows as theorems

The claim: Physics is not a collection of independent laws, but the **unique necessary structure** of distinction.

## Author

Andrey (Андрей)  
Independent researcher

## License

MIT License
