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
| Chain-7 | Composition monoid infinite (irreversibility) | FORCED | DEF-AX, Chain-6 |
| Chain-8 | ℕ (natural numbers) | FORCED | Chain-7 |
| CR-1 | Finite local valence (Φ < ∞) | FORCED | DEF-UAC |
| CR-2 | Finite generators | FORCED | CR-1 |
| CR-3 | Non-polynomial growth (Φ > 0) | FORCED | DEF-UAC |
| CR-4 | Non-commutativity or branching | FORCED | CR-3 |
| CR-5 | Minimal: ≥ 2 non-commuting generators | FORCED | CR-3, CR-4 |
| CR-6 | Finite presentation | FORCED | CR-1, CR-5 |
| CR-7 | Automorphism structure emerges | FORCED | CR-6 |
| Chain-9 | ℤ (iteration comparison) | FORCED | Chain-8, Chain-7, DEF-UAC |
| Chain-10 | ℚ (commensurability) | FORCED | Chain-9, CR-5, DEF-UAC |
| Chain-11 | ℝ (limit closure) | FORCED | Chain-10, DEF-UAC |
| Chain-12 | ℂ (automorphism closure) | FORCED | Chain-11, CR-7, DEF-UAC |
| DD-Unitarity | U(n) dynamics | FORCED | Chain-12, DEF-UAC |
| DD-Time | t ∈ ℝ (history parameter) | FORCED | DD-Unitarity, DEF-UAC |

**Chain-7 Resolution (GAP-4 closed):** Irreversibility follows from DEF-AX. If Δⁿ = id, then distinctions created between X and Δⁿ(X) would be erased, implying local Ø. Since Ø is impossible, {id, Δ, Δ², ...} must be infinite. This is a structural argument (no process/time needed).

**Critical Regime (CR-1 to CR-7):** Structural constraints from 0 < Φ < ∞. See `1_DERIVATION/CRITICAL_REGIME.md`.

**Continuum Closure (GAP-2 closed):** ℤ, ℚ, ℝ are not added but uniquely forced by criticality:
- ℤ: Iteration comparison requires signed differences; finite structure would collapse Chain-7.
- ℚ: Multi-generator (CR-5) comparison requires ratios; discontinuous Φ violates criticality.
- ℝ: Cauchy limits must exist; incomplete structure has Φ → 0 or Φ → ∞ at limits.

**Complex Numbers (Chain-12):** ℂ is forced by automorphism closure:
- ℝ has only trivial automorphisms (id); processes indistinguishable by direction.
- CR-7 requires non-trivial automorphism structure for critical dynamics.
- ℂ is the unique commutative division algebra over ℝ with continuous U(1) action.
- Process orientation distinguishable via phase, without appealing to time (GAP-3).

**Unitarity (DD-Unitarity):** U(n) dynamics forced by criticality preservation:
- Polar decomposition: A = UP (U unitary, P positive-definite Hermitian)
- If P ≠ I: eigenvalue λ < 1 ⟹ Aⁿv → 0 (Φ → 0); λ > 1 ⟹ Aⁿv → ∞ (Φ → ∞)
- Both violate UAC; therefore P = I, A is unitary
- Consequence: Aut_crit(X) = U(n) — pure linear algebra, no physics postulates
- This is NOT a quantum axiom; it's preservation of distinguishability under iteration.

**Time (DD-Time, GAP-3 closed):** Continuous time ℝ forced by history completeness:
- History parameter T must be: ordered (T1), additive (T2), invertible (T3), dense (T4)
- ℤ fails: discrete jumps → distinguishability not dense → violates criticality
- ℚ fails: incomplete → histories "fall out" at irrational limits → violates closure
- ℝ is unique: connected, complete, ordered abelian group (classical theorem)
- Stone: continuous unitary groups are homomorphisms ℝ → U(n)
- This is NOT "time is continuous because we observe it"; it's structural necessity.

---

## Layer 2: Bridges (2_EXPRESSION/)

### Hypotheses (HYP)

| ID | Statement | Status | Depends On |
|----|-----------|--------|------------|
| ~~HYP-C1~~ | ~~Continuum emergence~~ | **SUPERSEDED** | Now Chain-9,10,11 |
| HYP-F1 | Fisher metric ≡ distinction geometry | HYP | Chain-11 |
| ~~HYP-F2~~ | ~~Time parameter emergence (ℕ → ℝ)~~ | **SUPERSEDED** | Now DD-Time |
| HYP-F3 | Fisher-Ricci geometric flow | HYP | HYP-F1, DD-Time |
| HYP-Q1 | Fisher → Schrödinger equation | HYP | HYP-F1, DD-Time |
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
| FORCED | 27 |
| DEF | 8 |
| HYP | 18 |
| DERIVED | 3 |
| CONJ | 3 |
| CIRC | 2 |
| PRED | 1 |

---

## Open Gaps

| Gap | Description | Blocking |
|-----|-------------|----------|
| ~~GAP-1~~ | ~~Φ functional undefined~~ | **CLOSED** — see UAC.md |
| ~~GAP-2~~ | ~~Continuum not derived~~ | **CLOSED** — Chain-9,10,11 |
| ~~GAP-3~~ | ~~Time (ℕ → ℝ) not derived~~ | **CLOSED** — DD-Time |
| ~~GAP-4~~ | ~~Chain-7 interpretation~~ | **CLOSED** — irreversibility from DEF-AX |
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
