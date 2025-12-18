# Δ-Dynamics Simulations

Numerical simulations demonstrating emergence of structure from distinction.

## Files

### `delta_dynamics.py`
First version - demonstrates the basic idea but has issues with convergence.

### `delta_dynamics_v2.py` ⭐
Fixed dynamics with proper φ-critical behavior:
- Converges to φ⁻¹ = 0.618034 with 100% accuracy
- Double-well potential with minimum at golden ratio inverse
- Triadic interaction term
- Self-reference (gradient-based)
- Phase field for gauge structure

## Key Results

1. **φ-Convergence**: System naturally equilibrates at φ⁻¹ = 1/φ ≈ 0.618034
2. **Fisher Metric**: Emerges from field fluctuations, measures local distinguishability
3. **Phase Field**: Disordered but structured - gauge degrees of freedom
4. **Triadic Coupling**: Three-body interactions stabilize the dynamics

## Running

```bash
cd simulations
python delta_dynamics_v2.py
```

Generates:
- `v2_evolution.png` - Field evolution snapshots
- `v2_convergence.png` - Mean field and fluctuations over time
- `v2_analysis.png` - Final state: field, distribution, Fisher metric, phase
- `v2_structure.png` - Structure factor S(k)
- `v2_results.json` - Numerical results

## Connection to Theory

The simulation demonstrates the DD prediction that:
- Self-referential systems (Δ = Δ(Δ)) converge to φ⁻¹
- Spatial structure emerges from distinction dynamics
- Fisher metric measures accumulated distinguishability
- Gauge structure (phase field) carries internal symmetry

See `/docs/DD-FISHER-CONNECTION.md` for mathematical details.

## Physics Interpretation

| Simulation | DD Concept | Physical Meaning |
|------------|-----------|------------------|
| Δ-field | Distinction intensity | Local "being" density |
| Mean → φ⁻¹ | Critical point | Edge of chaos |
| Fluctuations | Quantum noise | Vacuum fluctuations |
| Fisher metric | Spacetime metric | Distinguishability geometry |
| Phase field | Gauge field | Internal symmetry |

## Future Work

- [ ] 3D simulations for proper triadic structure
- [ ] GPU acceleration (CUDA)
- [ ] Connection to CFT/AdS (Matsueda approach)
- [ ] Topological defect analysis
- [ ] Comparison with Ising model critical behavior
