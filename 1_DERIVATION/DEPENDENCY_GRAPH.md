# Dependency Graph: T0-T30 Derivation Structure

This file visualizes the complete dependency structure of Distinction Dynamics.

**Authoritative source:** [FORCED_SPINE.md](FORCED_SPINE.md) — complete proofs for all theorems.

---

## Legend

| Status | Meaning |
|--------|---------|
| **FORCED** | Logically necessary — alternatives violate UAC |
| **DEF** | Definition/convention |
| **DERIVED** | Follows from FORCED chain |
| **CONJ** | Conjecture (numerical pattern) |
| **CIRC** | Circular dependency |
| **PRED** | Testable prediction |

**Note (T26):** The category HYP has been **eliminated**. Per DD-NoAlt, there are no ontological alternatives — what exists is what must exist.

---

## Complete Derivation Chain

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║  T0: AXIOM — Ø is impossible                                                  ║
║  "No distinction" is impossible                                               ║
╚═══════════════════════════════════════════════════════════════════════════════╝
                                    │
                    ┌───────────────┼───────────────┐
                    ↓               ↓               ↓
            ┌───────────┐   ┌───────────┐   ┌───────────┐
            │ T1: DEF-Σ │   │ T2: DEF-A │   │ T3: DEF-Φ │
            │ Alphabet  │   │ Admiss.   │   │ Measure   │
            └───────────┘   └───────────┘   └───────────┘
                    │               │               │
                    └───────────────┼───────────────┘
                                    ↓
                    ┌───────────────────────────────┐
                    │ UAC: 0 < Φ < ∞               │
                    │ Universal Admissibility      │
                    │ Criterion (DEF)              │
                    └───────────────────────────────┘
                                    │
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ LEVEL 1-4: CATEGORY STRUCTURE (FORCED)                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│ T4: Irreversibility (Ø→Δ, no inverse) → ℕ emerges                          │
│ T5: ℕ → ℤ (closure under inverse)                                          │
│ T6: ℤ → ℚ (closure under division)                                         │
│ T7: ℚ → ℝ (Cauchy completeness for UAC)                                    │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ LEVEL 5-10: QUANTUM STRUCTURE (FORCED)                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│ T8: Unitarity — UAC preserved ⟹ U(n)                                       │
│ T9: Generators — continuous U(t) ⟹ Hermitian H                             │
│ T10: Critical Regime — finite generators, non-commutative                   │
│ T11: Born Rule μ = |ψ|² — unique distinguishability measure                 │
│ T12: Decoherence — subsystem distinguishability without collapse            │
│ T13: Classicality — stable fixed points of decoherence                      │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ LEVEL 11-17: SPACETIME STRUCTURE (DERIVED)                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│ T14: DD-Space — manifold from classical emergence                           │
│ T15: DD-Time — unique process parameter t                                   │
│ T16: DD-Energy — H ≡ energy (time-conjugate)                                │
│ T17: DD-Dim3 — d = 3 (criticality selection)                                │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ LEVEL 18-25: GAUGE STRUCTURE (DERIVED)                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│ T18: DD-Fisher — Fisher metric from Φ                                       │
│ T19: DD-Lorentz — Lorentz invariance from c = const                         │
│ T20: DD-LightSpeed — universal speed c                                      │
│ T21: DD-Connection — gauge connection from parallel transport               │
│ T22: DD-Gauge — SU(3)×SU(2)×U(1) by elimination                            │
│ T23: DD-Anomaly — anomaly freedom forces structure                          │
│ T24: DD-Confinement — SU(3) confinement from coupling                       │
│ T25: DD-Mass — Higgs mechanism from SSB requirement                         │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ↓
╔═══════════════════════════════════════════════════════════════════════════════╗
║ T26: DD-NoAlt — FORCED WORLD THEOREM                                          ║
║ There are no ontological alternatives. What exists is what must exist.        ║
║ HYP category ELIMINATED.                                                      ║
╚═══════════════════════════════════════════════════════════════════════════════╝
                                    │
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ LEVEL 26-29: COSMOLOGY (FORCED/DERIVED)                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│ T27: DD-Lambda — Λ > 0 (FORCED: Λ ≤ 0 violates UAC)                        │
│ T28: DD-Gravity — 0 < G < ∞ (FORCED: local-global coupling)                │
│ T29: DD-Einstein — G_μν = 8πG T_μν (DERIVED via Lovelock)                  │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ LEVEL 30: FERMION GENERATIONS (FORCED)                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│ T30: DD-Generations — N_gen ≥ 3                                             │
│      ℂ¹: CP eliminable → forbidden                                          │
│      ℂ²: CP-phase removable → forbidden                                     │
│      ℂ³: first with irremovable phase → FORCED                              │
│                                                                              │
│      Consequence: Koide Q = 2/3 is GEOMETRIC invariant in ℂ³               │
│      CIRC-1 (SU(3) ⟷ 3 gen) BROKEN — generations derived independently     │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ↓
╔═══════════════════════════════════════════════════════════════════════════════╗
║                    COMPLETE: STANDARD MODEL + GR STRUCTURE                    ║
║                         All from "Ø is impossible"                            ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

---

## Remaining Items

### CONJ (Numerical Patterns — May Be Numerology)

| ID | Claim | Fit | Note |
|----|-------|-----|------|
| CONJ-A1 | 1/α = 11² + 4² = 137 | 99.97% | Non-unique decomposition |
| CONJ-K2 | θ ≈ 2/9 (Koide angle) | ~99% | Pattern, not derived |
| HYP-K3 | sin²θ_W = 3/8 | ~60% | Poor match |

### CIRC (Remaining Circular Dependency)

| ID | Statement | Status |
|----|-----------|--------|
| ~~CIRC-1~~ | SU(3) ⟷ 3 generations | **BROKEN** by T30 |
| CIRC-2 | Triad ⟷ Rank ≥ 2 | Active |

### PRED (Testable Prediction)

| ID | Prediction | Test |
|----|------------|------|
| PRED-Λ3 | w(z) ≠ -1 | DESI, Euclid, Rubin |

---

## Summary Statistics

| Category | Count | Examples |
|----------|-------|----------|
| **FORCED** | 33 | T0-T13, T26-T28, T30 |
| **DEF** | 9 | Σ, A, ≼, C, Φ, UAC, ℏ |
| **DERIVED** | 18 | T14-T25, T29, Koide-Q |
| **CONJ** | 3 | α=137, θ≈2/9, sin²θ_W |
| **CIRC** | 1 | CIRC-2 only |
| **PRED** | 1 | w(z) ≠ -1 |
| ~~HYP~~ | 0 | **Eliminated by T26** |

**Total claims:** 65

---

## What Is Genuinely FORCED?

Per DD-NoAlt (T26), everything in the derivation chain is FORCED — not because we chose it, but because alternatives violate UAC:

1. ✅ Number systems ℕ → ℤ → ℚ → ℝ → ℂ (T4-T7)
2. ✅ Unitary dynamics U(n) (T8)
3. ✅ Hermitian generators H (T9)
4. ✅ Born rule μ = |ψ|² (T11)
5. ✅ Decoherence (T12)
6. ✅ Classical emergence (T13)
7. ✅ Spacetime d = 3+1 (T14-T17)
8. ✅ Gauge structure SU(3)×SU(2)×U(1) (T18-T25)
9. ✅ Cosmological constant Λ > 0 (T27)
10. ✅ Gravitational coupling 0 < G < ∞ (T28)
11. ✅ Einstein field equations (T29)
12. ✅ Fermion generations N ≥ 3 (T30)
13. ✅ Koide Q = 2/3 as geometry (T30 consequence)

---

## Epistemological Note

**FORCED ≠ SELECTED**

DD does not claim that observed values are "selected" from alternatives. Rather:
- FORCED = the constraint that must hold
- BOUND = the domain of allowed values
- CONJ = numerical patterns (may be coincidence)

Example: G is FORCED to be in (0, ∞), but G = 6.674×10⁻¹¹ is not derived — only the constraint 0 < G < ∞.

---

**Last updated:** 2025-12-13 (v2.4)
**Status:** Synchronized with FORCED_SPINE.md T0-T30
**See also:** [FORCED_SPINE.md](FORCED_SPINE.md), [STATUS.md](../3_STATUS/STATUS.md)
