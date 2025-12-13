# STATUS.md — Master Truth File

**Last updated:** 2025-12-13

This file is the authoritative source for the logical status of all claims in the repository.
README.md must not contradict this file.

---

## Label Definitions

| Label | Meaning |
|-------|---------|
| **FORCED** | Logically necessary from axiom + definitions |
| **FORCED*** | Forced given interpretation (caveat documented) |
| **DEF** | Definition or convention (added structure) |
| **HYP** | Hypothesis requiring external justification |
| **DERIVED** | Follows rigorously from HYP + FORCED/DEF |
| **CONJ** | Conjecture, pattern match, possible numerology |
| **CIRC** | Circular dependency (mutual consistency, not derivation) |
| **PRED** | Testable empirical prediction |

---

## Layer 0: Core (0_CORE/)

| ID | Statement | Status | File |
|----|-----------|--------|------|
| DEF-AX | Ø is impossible | **Axiom** | AXIOM.md |
| DEF-Σ | Alphabet Σ, non-empty words Σ+ | DEF | DEFINITIONS.md |
| DEF-A | Admissibility A ⊆ Σ+ with (A1-A3) | DEF | DEFINITIONS.md |
| DEF-≼ | Prefix order on A | DEF | DEFINITIONS.md |
| DEF-C | Category C induced by ≼ | DEF | DEFINITIONS.md |
| DEF-UAC | 0 < Φ(S) < ∞ (admissibility criterion) | DEF | UAC.md |
| P1 | Φ invariance | FORCED | UAC.md |
| P2 | Φ monotonicity | FORCED | UAC.md |
| P3 | Φ boundary sensitivity | FORCED | UAC.md |
| P4 | Φ locality aggregation | FORCED | UAC.md |
| P5 | Φ dimensionlessness | FORCED | UAC.md |
| Φ-unique | Φ = lim sup (1/n) log P(n) | FORCED | UAC.md, P1-P5 |
| DEF-Φ | Path entropy functional | DEF | DEFINITIONS.md |

---

## Layer 1: Forced Chain (1_DERIVATION/)

| ID | Statement | Status | Depends On |
|----|-----------|--------|------------|
| L1 | Σ+ is non-empty | FORCED | DEF-Σ |
| L2 | ≼ is partial order | FORCED | DEF-≼ |
| L3 | C is thin | FORCED | DEF-C |
| L4 | C is small | FORCED | DEF-C |
| Chain-5 | Bool (binary structure X/¬X) | FORCED | DEF-Σ |
| Chain-6 | Δ = Δ(Δ) (self-application) | FORCED | DEF-AX |
| Chain-7 | Recursion (unbounded iteration) | FORCED* | Chain-6 |
| Chain-8 | ℕ (natural numbers) | FORCED | Chain-7 |
| CR-1 | Finite local valence (Φ < ∞) | FORCED | DEF-UAC |
| CR-2 | Finite generators | FORCED | CR-1 |
| CR-3 | Non-polynomial growth (Φ > 0) | FORCED | DEF-UAC |
| CR-4 | Non-commutativity or branching | FORCED | CR-3 |
| CR-5 | Minimal: ≥ 2 non-commuting generators | FORCED | CR-3, CR-4 |
| CR-6 | Finite presentation | FORCED | CR-1, CR-5 |
| CR-7 | Automorphism structure emerges | FORCED | CR-6 |

**Caveat for Chain-7:** The interpretation of Δ = Δ(Δ) as unfolding process (rather than static fixed point) is an interpretive choice. Marked FORCED* to indicate this.

**Critical Regime (CR-1 to CR-7):** Structural constraints from 0 < Φ < ∞. See `1_DERIVATION/CRITICAL_REGIME.md`.

---

## Layer 2: Bridges (2_EXPRESSION/)

### Hypotheses (HYP)

| ID | Statement | Status | Depends On |
|----|-----------|--------|------------|
| HYP-C1 | Continuum emergence | HYP | Chain-8, DEF-C |
| HYP-F1 | Fisher metric ≡ distinction geometry | HYP | HYP-C1 |
| HYP-F2 | Time parameter emergence (ℕ → ℝ) | HYP | Chain-7 |
| HYP-F3 | Fisher-Ricci geometric flow | HYP | HYP-F1, HYP-F2 |
| HYP-Q1 | Fisher → Schrödinger equation | HYP | HYP-F1, HYP-F2 |
| HYP-Q2 | Physical constants ℏ, c, G | HYP (input) | — |
| HYP-G1 | Local gauge invariance | HYP | HYP-S4 |
| HYP-G2 | Anomaly freedom | HYP (empirical) | HYP-Q1, HYP-G1 |
| HYP-G3 | Asymptotic freedom | HYP (empirical) | — |
| HYP-G4 | Confinement | HYP (empirical) | — |
| HYP-S1 | 3 spatial dimensions from triad | CONJ | CIRC-2 |
| HYP-S2 | Time dimension from U(1) phase | HYP | HYP-Q1 |
| HYP-S3 | Lorentz invariance | HYP | HYP-S1 |
| HYP-S4 | Fisher geometry ≡ spacetime | HYP | HYP-F1, HYP-S3 |
| HYP-P1 | Higgs mechanism | HYP | — |
| HYP-P2 | Fermion generations | HYP | — |
| HYP-K1 | √m parameterization | HYP | — |
| HYP-K3 | sin²θ_W = 3/8 | HYP | — |
| HYP-Λ1 | Λ > 0 (cosmological constant) | HYP (empirical) | — |
| HYP-P3 | Dynamics / time evolution | HYP | — |

### Derived (DERIVED)

| ID | Statement | Status | Depends On |
|----|-----------|--------|------------|
| SU(3)-unique | SU(3) is unique strong gauge group | DERIVED | HYP-G1, HYP-G2, HYP-G3, HYP-G4 |
| Koide-Q | Q = 2/3 | DERIVED | ℤ₃ symmetry, HYP-K1 |
| Koide-ε | ε = √2 | DERIVED | Koide-Q |

### Conjectures (CONJ)

| ID | Statement | Status | Empirical Fit |
|----|-----------|--------|---------------|
| CONJ-A1 | 1/α = 11² + 4² = 137 | CONJ | 99.97% |
| CONJ-K2 | θ ≈ λ ≈ 2/9 | CONJ | ~99% |
| CONJ-Λ2 | Λ_eff = k(Δ + F + M) | CONJ | — |

### Circular Dependencies (CIRC)

| ID | Statement | Status |
|----|-----------|--------|
| CIRC-1 | SU(3) ⟷ 3 generations | Mutual consistency |
| CIRC-2 | Triad ⟷ Rank ≥ 2 | Minimality assumed |

### Predictions (PRED)

| ID | Statement | Status | Falsifiability |
|----|-----------|--------|----------------|
| PRED-Λ3 | w(z) ≠ -1 | PRED | If w = -1.000 ± 0.001, ruled out |

---

## Summary Counts

| Status | Count |
|--------|-------|
| FORCED | 21 |
| DEF | 8 |
| HYP | 20 |
| DERIVED | 3 |
| CONJ | 3 |
| CIRC | 2 |
| PRED | 1 |

---

## Open Gaps

| Gap | Description | Blocking |
|-----|-------------|----------|
| ~~GAP-1~~ | ~~Φ functional undefined~~ | **CLOSED** — see UAC.md |
| GAP-2 | Continuum not derived | HYP-C1 is hypothesis |
| GAP-3 | Time (ℕ → ℝ) not derived | HYP-F2 is hypothesis |
| GAP-4 | Chain-7 interpretation | FORCED* caveat unresolved |
| GAP-5 | α = 137 formula unjustified | CONJ-A1 may be numerology |
| GAP-6 | 3+1 dimensions weak argument | HYP-S1 downgraded to CONJ |

---

## Verification Status

| Component | Status |
|-----------|--------|
| Agda proofs | 16 files, 0 postulates |
| Lean proofs | Partial (some sorry) |
| Python verification | 36 files |
| LaTeX documentation | 31 chapters |

---

## File Cross-Reference

- Axiom: `0_CORE/AXIOM.md`
- Definitions: `0_CORE/DEFINITIONS.md`
- UAC: `0_CORE/UAC.md`
- Forced chain: `1_DERIVATION/FORCED_CHAIN.md`
- Critical regime: `1_DERIVATION/CRITICAL_REGIME.md`
- Dependency graph: `1_DERIVATION/DEPENDENCY_GRAPH.md`
- Bridges: `2_EXPRESSION/BRIDGES.md`
- Circularities: `2_EXPRESSION/CIRCULARITIES.md`
- Theory position: `3_STATUS/THEORY_POSITION.md`
- Roadmap: `3_STATUS/ROADMAP.md`
