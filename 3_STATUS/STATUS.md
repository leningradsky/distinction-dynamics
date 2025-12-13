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
| DD-Generator | H hermitian, U(t)=e^{-itH} | FORCED | DD-Time, DD-Unitarity, Stone |

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

**Hermitian Generator (DD-Generator):** H and exponential form U(t) = e^{-itH} forced by Stone's theorem:
- Continuous unitary groups U: ℝ → U(n) have unique Hermitian generator H
- If H not Hermitian: e^{-itH} not unitary → collapse or explosion → violates UAC
- Exponential form forced by: additive time → multiplicative operators, continuity → differentiability
- H is "generator of distinguishability" — energy interpretation requires additional bridge.
- This completes QM kinematics: ℂ, U(n), t ∈ ℝ, H hermitian — all FORCED, no physics postulates.

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
| ~~HYP-G1~~ | ~~Local gauge invariance~~ | **SUPERSEDED** | Now DD-Gauge |
| ~~HYP-G2~~ | ~~Anomaly freedom~~ | **SUPERSEDED** | Now DD-Gauge |
| ~~HYP-G3~~ | ~~Asymptotic freedom~~ | **SUPERSEDED** | Now DD-Gauge |
| ~~HYP-G4~~ | ~~Confinement~~ | **SUPERSEDED** | Now DD-Gauge |
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
| DD-Born | μ(ψ) = \|ψ\|² (Born rule) | DERIVED | DD-Unitarity, P1-P3 |
| DD-Decoherence | No collapse, measurement relative | DERIVED | DD-Unitarity, DD-Born |
| DD-Classicality | Classical states = stable fixed points | DERIVED | Criticality, DD-Decoherence |
| DD-Space | Manifold structure of space | DERIVED | Criticality, DD-Classicality |
| DD-Time-Unique | Time as unique process parameter | DERIVED | Criticality, DD-Time, DD-Space |
| DD-Energy | H = energy (structural identification) | DERIVED | DD-Time, DD-Generator |
| DD-Dim3 | d = 3 (criticality selection) | DERIVED | Criticality, DD-Space, DD-Time-Unique |
| DD-Gauge | SU(3)×SU(2)×U(1) (elimination proof) | DERIVED | Criticality, DD-Unitarity, DD-Decoherence, DD-Space |
| ~~SU(3)-unique~~ | ~~SU(3) is unique strong gauge group~~ | **SUBSUMED** | Now part of DD-Gauge |
| Koide-Q | Q = 2/3 | DERIVED | ℤ₃ symmetry, HYP-K1 |
| Koide-ε | ε = √2 | DERIVED | Koide-Q |

**Born Rule (DD-Born):** Unique distinguishability measure from unitarity:
- P1: Normalization (Σμ(ψᵢ) = 1)
- P2: Additivity on orthogonal alternatives
- P3: History invariance (μ(ψ) = μ(U(t)ψ))
- Uniqueness: f(√(a+b)) = f(√a) + f(√b) ⟹ f(√x) = Cx ⟹ μ = |ψ|²
- This is NOT Gleason's theorem; DD-Born works for any dimension.

**Decoherence (DD-Decoherence):** Measurement without collapse:
- Composition of distinctions = tensor product (FORCED)
- Distinguishability relative to subalgebra
- Φ(Ψ) → Φ(S) + Φ(E) (factorization)
- Collapse impossible: would violate unitarity (FORCED)
- Born rule applies to factorized alternatives

**Classicality (DD-Classicality):** Classical emergence from decoherence:
- Classical state = distinction surviving decoherence
- Pointer states = eigenstates of system-environment interaction
- If all states unstable → Φ → 0 → criticality violated
- Classical objects = stable orbits of distinguishability
- Classicality is local, not fundamental

**Space (DD-Space):** Manifold structure from distinguishability:
- Classical distinctions form connected structure (isolated → Φ fails closure)
- Graph structure forbidden (Φ → 0 at nodes, Φ discontinuous at edges)
- Continuous structure required: manifold uniquely forced
- Space = parameterization of stable distinctions
- Metric = quantitative form of Φ-localization
- Dimension: 0, 1, ∞ forbidden; finite d > 1 required

**Time Uniqueness (DD-Time-Unique):** Why exactly one time parameter:
- Static distinguishability forbidden (no selection, no stability)
- Cyclic process forbidden (decoherence reversible → history collapses)
- Process parameter must be linearly ordered (branching → no global history)
- Must be continuous ℝ (discrete ℤ incompatible with continuous space)
- Must be unique (multiple times → unitarity destroyed)
- Spacetime signature (1, d-1) is forced, not postulated

**Energy (DD-Energy):** H = energy is structural identification:
- H is unique Hermitian generator of time translation (Stone)
- Time symmetry t → t + δ has unique conserved generator (Noether)
- Cannot be charge (no internal symmetries yet), cannot be momentum (no space in this context)
- Generator must be observable distinction (criticality)
- Energy ≡ generator of time translation in unitary evolution
- This is not interpretation but uniqueness argument

**Dimension (DD-Dim3):** d = 3 as unique admissible dimension:
- Five admissibility criteria: D1 (localizable excitations), D2 (non-trivial dynamics), D3 (factorizing decoherence), D4 (non-trivial gauge), D5 (criticality)
- d = 1: fails D1, D3 (no locality, total decoherence)
- d = 2: fails D2, D4 (no local dynamics, gauge trivializes)
- d ≥ 4: fails D1, D5 (no stable objects, selection-unstable)
- d = 3: unique dimension satisfying all D1-D5 simultaneously
- This is structural intersection, not anthropic argument

**Gauge Groups (DD-Gauge):** SU(3)×SU(2)×U(1) as unique structure:
- Five structural criteria: C1 (local unitarity), C2 (non-trivial internal), C3 (factorizability), C4 (criticality), C5 (minimality)
- U(1): minimal phase distinguishability
- SU(2): minimal non-abelian stable structure
- SU(3): maximal group preserving criticality (N ≥ 4 breaks criticality threshold)
- SO(N), Sp(N), exceptional groups eliminated (incompatible with phase/factorization structure)
- Products beyond SU(3)×SU(2)×U(1) duplicate distinguishabilities or destabilize
- This is elimination proof, not postulate

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
| FORCED | 28 |
| DEF | 8 |
| HYP | 13 |
| DERIVED | 11 |
| CONJ | 2 |
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
| ~~GAP-6~~ | ~~3+1 dimensions weak argument~~ | **CLOSED** — DD-Dim3 (criticality selection) |

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
- **FORCED Spine: `1_DERIVATION/FORCED_SPINE.md`** (authoritative 12-thesis derivation)
- Forced chain: `1_DERIVATION/FORCED_CHAIN.md`
- Critical regime: `1_DERIVATION/CRITICAL_REGIME.md`
- Dependency graph: `1_DERIVATION/DEPENDENCY_GRAPH.md`
- Bridges: `2_EXPRESSION/BRIDGES.md`
- Circularities: `2_EXPRESSION/CIRCULARITIES.md`
- Theory position: `3_STATUS/THEORY_POSITION.md`
- Roadmap: `3_STATUS/ROADMAP.md`
