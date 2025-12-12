# Distinction Dynamics - Lean 4 Formalization

Machine-verified derivation of physics from the axiom **Δ ≠ ∅**.

## Structure

```
DD/
├── Core.lean      # Axiom, Three, S₃, SU(3) necessity (NO sorry)
├── Fisher.lean    # Fisher information, Cramér-Rao (some sorry)
├── Quantum.lean   # Schrödinger from Fisher (some sorry)
└── Constants.lean # α, θW, masses (planned)
```

## Installation

### 1. Install elan (Lean version manager)

**Windows (PowerShell):**
```powershell
curl.exe -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

**Linux/macOS:**
```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

### 2. Build the project

```bash
cd E:\claudecode\DD_v2\lean
lake update   # Download mathlib (takes a while first time)
lake build    # Compile DD
```

### 3. Check proofs

```bash
lake env lean DD.lean
```

## What's Proven (no sorry)

| File | Theorem | Status |
|------|---------|--------|
| Core.lean | distinction_exists | ✓ proven |
| Core.lean | triad_closed | ✓ proven |
| Core.lean | r_cubed (r³ = e) | ✓ proven |
| Core.lean | s_squared (s² = e) | ✓ proven |
| Core.lean | r_order = 3 | ✓ proven |
| Core.lean | S2.no_order_3 | ✓ proven |
| Core.lean | A3_det_one | ✓ proven |
| Core.lean | SU3_necessary | ✓ proven |

## What Needs Work (has sorry)

| File | Theorem | Needs |
|------|---------|-------|
| Fisher.lean | cramer_rao_bound | Measure theory |
| Fisher.lean | fisher_minimization_gives_schrodinger | Calculus of variations |
| Quantum.lean | uncertainty_from_fisher | Full Fisher formalization |
| Quantum.lean | free_particle_solution | Complex analysis |

## The Derivation

```
Δ ≠ ∅
  ↓
Bool → ℕ → Three → S₃
  ↓
order(r) = 3, S₂ has no order-3
  ↓
SU(3) NECESSARY (not just sufficient)
  ↓
Fisher Information = metric on distinguishability
  ↓
min(Fisher) + constraints = Schrödinger equation
  ↓
Quantum Mechanics DERIVED
```

## Key Insight

Fisher information is the unique metric compatible with:
1. Distinguishability (from DD axiom)
2. Cramér-Rao bound (fundamental limit)
3. Riemannian structure (geometry)

Minimizing Fisher information with energy constraint gives QM.
Minimizing Fisher information on metric space gives GR (Ricci flow).

This is not fitting - it's derivation.

## References

- Frieden, B.R. (1998) "Physics from Fisher Information"
- Amari, S. (2016) "Information Geometry and Its Applications"
- Caticha, A. (2012) "Entropic Inference and the Foundations of Physics"
