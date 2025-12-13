# Claims and Status Reference

Complete list of all claims with their status and location.

---

## FORCED Claims (33)

| ID | Statement | Location |
|----|-----------|----------|
| DD-Generations | N_gen ≥ 3 (fermion generations) | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Gravity | 0 < G < ∞ (gravitational coupling) | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Lambda | Λ > 0 (cosmological constant) | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-NoAlt | No ontological alternatives | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| L1 | Σ+ is non-empty | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| L2 | ≼ is partial order | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| L3 | C is thin | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| L4 | C is small | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-5 | Bool (binary structure) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-6 | Δ = Δ(Δ) (self-application) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-7 | {Δⁿ} infinite (irreversibility) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-8 | ℕ ≅ {Δⁿ} | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-9 | ℤ (iteration comparison) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-10 | ℚ (commensurability) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-11 | ℝ (limit closure) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| Chain-12 | ℂ (automorphism closure) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| DD-Unitarity | U(n) dynamics | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| DD-Time | t ∈ ℝ (history parameter) | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| DD-Generator | H hermitian, U(t)=e^{-itH} | [FORCED_CHAIN.md](../1_DERIVATION/FORCED_CHAIN.md) |
| DD-Factorization | ⊗ℋᵢ tensor structure | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| CR-1 | Finite local valence | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| CR-2 | Finite generators | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| CR-3 | Non-polynomial growth | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| CR-4 | Non-commutativity or branching | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| CR-5 | ≥ 2 non-commuting generators | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| CR-6 | Finite presentation | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| CR-7 | Automorphism structure | [CRITICAL_REGIME.md](../1_DERIVATION/CRITICAL_REGIME.md) |
| P1 | Φ invariance | [UAC.md](../0_CORE/UAC.md) |
| P2 | Φ monotonicity | [UAC.md](../0_CORE/UAC.md) |
| P3 | Φ boundary sensitivity | [UAC.md](../0_CORE/UAC.md) |
| P4 | Φ locality | [UAC.md](../0_CORE/UAC.md) |
| P5 | Φ dimensionlessness | [UAC.md](../0_CORE/UAC.md) |
| Φ-unique | Φ = path entropy | [UAC.md](../0_CORE/UAC.md) |

---

## DEF Claims (9)

| ID | Statement | Location |
|----|-----------|----------|
| DEF-AX | Ø is impossible | [AXIOM.md](../0_CORE/AXIOM.md) |
| DEF-Σ | Alphabet Σ, words Σ+ | [DEFINITIONS.md](../0_CORE/DEFINITIONS.md) |
| DEF-A | Admissibility A | [DEFINITIONS.md](../0_CORE/DEFINITIONS.md) |
| DEF-≼ | Prefix order | [DEFINITIONS.md](../0_CORE/DEFINITIONS.md) |
| DEF-C | Category C | [DEFINITIONS.md](../0_CORE/DEFINITIONS.md) |
| DEF-UAC | 0 < Φ < ∞ criterion | [UAC.md](../0_CORE/UAC.md) |
| DEF-Φ | Path entropy functional | [DEFINITIONS.md](../0_CORE/DEFINITIONS.md) |
| DEF-ℏ | Planck constant (unit choice) | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) T27 note |

---

## UNTRACED Claims (0) — formerly HYP

**All claims now traced.** Per DD-NoAlt (T26), DD-Lambda (T27), and DD-Gravity (T28):

| ID | Statement | Was | Now |
|----|-----------|-----|-----|
| ~~HYP-Q2(G)~~ | ~~Gravitational constant G~~ | UNTRACED | **FORCED** (DD-Gravity T28) |
| ~~HYP-Q2(ℏ)~~ | ~~Planck constant ℏ~~ | UNTRACED | **DEF** (unit choice) |
| ~~HYP-Λ1~~ | ~~Λ > 0~~ | UNTRACED | **FORCED** (DD-Lambda T27) |
| ~~HYP-P3~~ | ~~Dynamics~~ | UNTRACED | **DERIVED** (DD-Generator T10) |

**UNTRACED = 0. All fundamental physics is FORCED/DERIVED.**

---

## DERIVED Claims (17)

| ID | Statement | Depends On | Location |
|----|-----------|------------|----------|
| DD-Born | μ(ψ) = \|ψ\|² (Born rule) | DD-Unitarity, DD-Factorization | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Decoherence | No collapse, measurement relative | DD-Unitarity, DD-Factorization, DD-Born | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Classicality | Classical states = stable fixed points | Criticality, DD-Decoherence | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Space | Manifold structure of space | Criticality, DD-Classicality | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Time-Unique | Time as unique process parameter | Criticality, DD-Time, DD-Space | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Energy | H = energy (structural identification) | DD-Time, DD-Generator | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Dim3 | d = 3 (criticality selection) | Criticality, DD-Space, DD-Time-Unique, DD-Connection | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Connection | Gauge connection A_μ (local phase coherence) | Criticality, ℂ, Unitarity, DD-Factorization | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Gauge | SU(3)×SU(2)×U(1) (elimination proof) | Criticality, DD-Dim3, DD-Connection | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Lorentz | SO(1,3) Lorentz invariance | DD-Time-Unique, DD-Space, Criticality | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Fisher | Fisher metric uniqueness (Chentsov) | Chain-12, DD-Born, Chentsov's theorem | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-LightSpeed | Universal speed c | DD-Lorentz, DD-Space | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Mass | Mass mechanism (Higgs/SSB) | DD-Gauge, DD-Connection, Criticality | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| DD-Einstein | G_μν = 8πG T_μν (field equations) | DD-Gravity, DD-NoAlt, Lovelock | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) |
| ~~SU(3)-unique~~ | ~~SU(3) is unique~~ | **SUBSUMED** by DD-Gauge | [BRIDGES.md](../2_EXPRESSION/BRIDGES.md) |
| Koide-Q | Q = 2/3 (geometric invariant in ℂ³) | DD-Generations, ℤ₃ | [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) T30 |
| Koide-ε | ε = √2 | Koide-Q | [BRIDGES.md](../2_EXPRESSION/BRIDGES.md) |

---

## CONJ Claims (3)

| ID | Statement | Fit | Location |
|----|-----------|-----|----------|
| CONJ-A1 | 1/α = 11² + 4² = 137 | 99.97% | [BRIDGES.md](../2_EXPRESSION/BRIDGES.md) |
| CONJ-K2 | θ ≈ 2/9 | ~99% | [BRIDGES.md](../2_EXPRESSION/BRIDGES.md) |
| HYP-K3 | sin²θ_W = 3/8 | — | Numerical pattern |

---

## CIRC Claims (1)

| ID | Statement | Location |
|----|-----------|----------|
| ~~CIRC-1~~ | ~~SU(3) ⟷ 3 generations~~ | **BROKEN** by DD-Generations (T30) |
| CIRC-2 | Triad ⟷ Rank ≥ 2 | [CIRCULARITIES.md](../2_EXPRESSION/CIRCULARITIES.md) |

---

## PRED Claims (1)

| ID | Statement | Test | Location |
|----|-----------|------|----------|
| PRED-Λ3 | w(z) ≠ -1 | DESI, Euclid | [BRIDGES.md](../2_EXPRESSION/BRIDGES.md) |

---

## Summary

| Status | Count |
|--------|-------|
| FORCED | 33 |
| DEF | 9 |
| DERIVED | 18 |
| UNTRACED | 0 |
| CONJ | 3 |
| CIRC | 1 |
| PRED | 1 |
| **Total** | **65** |

**Note (T30):** UNTRACED = 0. All fundamental physics derived:
- 18 → DERIVED (including Koide as geometry)
- 3 → FORCED (Λ > 0, G, N_gen ≥ 3)
- 1 → DEF (ℏ)
- 3 → CONJ
- 1 → CIRC (CIRC-1 broken by T30)

**See FORCED_SPINE.md T0-T30 for complete derivation chain.**

All fundamental constants, GR equations, and generations now derived:
- c: DERIVED (DD-LightSpeed)
- ℏ: DEF (unit choice)
- G: FORCED (DD-Gravity)
- Λ: FORCED (DD-Lambda)
- G_μν = 8πG T_μν: DERIVED (DD-Einstein)
- N_gen ≥ 3: FORCED (DD-Generations)
- Koide Q = 2/3: DERIVED (geometric invariant in ℂ³)
