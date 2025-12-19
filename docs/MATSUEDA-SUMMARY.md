# Matsueda 2014: Fisher Information → AdS Spacetime

**Paper**: "Geometry and Dynamics of Emergent Spacetime from Entanglement Spectrum"  
**arXiv**: 1408.5589 [hep-th]  
**Author**: Hiroaki Matsueda

## Why This Paper Matters for DD

This paper **directly proves** the central DD claim: spacetime geometry emerges from
information structure (distinguishability). Matsueda shows that the Fisher information
metric computed from quantum entanglement gives Anti-de Sitter spacetime.

## The Core Result

```
1D CFT (free fermions)
        ↓
Entanglement spectrum λₙ(θ) = exp{θᵅFₙᵅ - ψ(θ)}  [exponential family]
        ↓
Fisher metric g_μν = ∂_μ∂_νψ(θ)  [Hessian of potential]
        ↓
Coordinate transform (θ → y)
        ↓
AdS metric: ds² = (1/y¹)² [4κ(dy¹)² + Σ(dyⁱ)²]
```

## Key Equations

### Entanglement Spectrum
The reduced density matrix eigenvalues form an **exponential family**:
$$\lambda_n(\theta) = \exp\left\{\theta^\alpha F_n^\alpha - \psi(\theta)\right\}$$

### Hessian Potential
$$\psi(\theta) = -\kappa \ln\left[\theta^1 - \frac{1}{2}\sum_i (\theta^i)^2\right]$$

### Fisher Metric
$$g_{\mu\nu} = \partial_\mu \partial_\nu \psi(\theta)$$

### Emergent AdS
After coordinate transformation:
$$g = \frac{1}{(y^1)^2}\left[4\kappa (dy^1)^2 + \sum_i (dy^i)^2\right]$$

This is **exactly** Anti-de Sitter space in Poincaré coordinates!

## The Three Canonical Parameters

Matsueda identifies three natural parameters (confirming DD's triadic necessity):

| Parameter | Physical Meaning | DD Interpretation |
|-----------|------------------|-------------------|
| θ¹ ~ L⁻² | Subsystem size | Spatial scale |
| θ² ~ n̄ derivative | Filling fraction | Internal quantum number |
| θ³ ~ t/t₀ | Time evolution | Temporal ordering |

**Crucial**: D ≥ 3 required for nontrivial geometry (from Hessian structure)

## Einstein Equations Emerge!

The paper derives:
$$G_{\mu\nu} + \Lambda g_{\mu\nu} = a T_{\mu\nu}$$

where the source is **entropy fluctuation**:
$$\phi = S - S_0$$

The scalar field Lagrangian:
$$\mathcal{L} = \frac{1}{2}(\partial^\alpha\phi)(\partial_\alpha\phi)$$

This means: **gravity = consistency condition on entanglement structure**

## Connections to DD

| Matsueda | DD Framework |
|----------|--------------|
| Fisher metric | Δ-metric (distinguishability geometry) |
| Entanglement spectrum | Δ-field eigenvalues |
| Exponential family | Natural structure from Δ-closure |
| D ≥ 3 required | Triadic necessity |
| Entropy = potential | Δ-vacuum energy |
| Einstein equations | Consistency of Δ-structure |

## Holographic Interpretation

- **Boundary (UV)**: CFT data, L → ∞, y¹ → 0
- **Bulk (IR)**: Emergent AdS geometry
- **Holography**: Information geometry bridges the two

## Testable Predictions

1. Entanglement spectra in quantum simulators should show exponential family form
2. Fisher metric computed from experimental data should have AdS-like curvature
3. 3 parameters minimum required (can be tested in matrix product states)

## Citation

```bibtex
@article{Matsueda2014,
  title={Geometry and Dynamics of Emergent Spacetime from Entanglement Spectrum},
  author={Matsueda, Hiroaki},
  journal={arXiv preprint arXiv:1408.5589},
  year={2014}
}
```

## Summary

Matsueda provides the **mathematical proof** that:

> Fisher information geometry (the geometry of distinguishability) 
> gives rise to spacetime from quantum entanglement.

This is precisely what DD claims: **Δ ≠ ∅ → spacetime**.

The Fisher metric IS the Δ-metric. Spacetime is not fundamental but emergent
from the structure of distinguishability.
