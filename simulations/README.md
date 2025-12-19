# Δ-Dynamics Simulations

Computational demonstrations of Distinction Dynamics principles.

## Overview

These simulations show how complex structure emerges from the simple axiom **Δ ≠ ∅**.

## Files

### `delta_dynamics.py`

Main simulation of Δ-field dynamics on a 2D lattice.

**Features**:
- Diffusion, self-reference Δ(Δ), and triadic interactions
- Convergence to φ⁻¹ = 0.618... critical point
- Fisher information metric computation
- Phase field for gauge structure
- Structure factor analysis

**Usage**:
```bash
cd simulations
python delta_dynamics.py
```

## The Δ-Field Equation

```
∂Δ/∂t = D∇²Δ + F(Δ) + βΔ(Δ) + γT(Δ) + η
```

Where:
- `D∇²Δ`: Diffusion (distinctions spread)
- `F(Δ)`: Potential forcing toward φ⁻¹
- `βΔ(Δ)`: Self-reference (gradient-sensitive)
- `γT(Δ)`: Triadic 3-body correlations
- `η`: Quantum fluctuations (noise)

## Key Results

1. **φ-Convergence**: The field self-organizes to mean ≈ φ⁻¹ = 0.618
2. **Structure Factor**: Power-law scaling suggests scale invariance
3. **Phase Coherence**: Gauge-like structure emerges spontaneously
4. **Fisher Metric**: Non-trivial geometry from distinguishability

## Theoretical Background

See:
- `DD-MATHEMATICAL-FOUNDATIONS.md` - Core DD theory
- `DD-LITERATURE-CONNECTIONS.md` - Related work
- `MATSUEDA-SUMMARY.md` - Fisher → AdS proof

## Dependencies

```
numpy
scipy
matplotlib
```

## Example Output

The simulation produces:
- Evolution snapshots showing structure emergence
- Entropy evolution (complexity from nothing)
- Structure factor (emergent length scales)
- Fisher metric visualization (DD spacetime)

## Connection to Physics

| Simulation Feature | Physical Interpretation |
|-------------------|------------------------|
| Δ-field | Local distinction intensity |
| φ⁻¹ attractor | Golden ratio criticality |
| Phase field | Gauge degrees of freedom |
| Fisher metric | Emergent spacetime geometry |
| Triadic kernel | SU(3)-like 3-body forces |

## Future Work

- [ ] 3D simulation for full SU(3) structure
- [ ] GPU acceleration for larger systems
- [ ] Connection to actual entanglement spectra
- [ ] DESI cosmology predictions

---
*Part of Distinction Dynamics research program*
