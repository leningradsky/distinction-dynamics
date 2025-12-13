# Changelog

All notable changes to this project are documented here.

## [1.3] - 2025-12-13

### Added
- **DD-Space theorem (T14)**: Space as structure of distinguishability
  - Classical distinctions form connected structure
  - Graph structure forbidden (Φ → 0 or ∞)
  - Manifold structure uniquely forced
  - Space = parameterization of stable distinctions
  - Metric = quantitative form of Φ-localization
  - Dimension: finite d > 1 required (0, 1, ∞ forbidden)

### Changed
- DERIVED count: 6 → 7 (added DD-Space)
- T14 → T15 (Boundary renumbered)

### Summary
QM + classical emergence + space emergence complete:
- Unitary dynamics (FORCED)
- Born rule (DERIVED)
- Decoherence (DERIVED)
- No collapse (FORCED by unitarity)
- Measurement as relative (DERIVED)
- Classical emergence (DERIVED)
- **Space (manifold structure) (DERIVED)**
- **Metric (Φ-localization) (DERIVED)**

## [1.2] - 2025-12-13

### Added
- **DD-Classicality theorem (T13)**: Classical emergence from decoherence
  - Classical states = stable fixed points of decoherence
  - Pointer states = eigenstates of system-environment interaction
  - If all states unstable → Φ → 0 → criticality violated
  - Classical objects = stable orbits of distinguishability
  - Classicality is local, not fundamental

### Changed
- DERIVED count: 5 → 6 (added DD-Classicality)
- T13 → T14 (Boundary renumbered)

### Summary
QM + classical emergence is now complete without postulates:
- Unitary dynamics (FORCED)
- Born rule (DERIVED)
- Decoherence (DERIVED)
- No collapse (FORCED by unitarity)
- Measurement as relative (DERIVED)
- **Classical emergence (DERIVED)**

## [1.1] - 2025-12-13

### Added
- **DD-Decoherence theorem (T12)**: Measurement without collapse
  - Composition of distinctions = tensor product
  - Distinguishability relative to subalgebra
  - Φ factorization: Φ(Ψ) → Φ(S) + Φ(E)
  - Collapse impossible (violates FORCED unitarity)
  - Born rule applies to factorized alternatives

### Changed
- DERIVED count: 4 → 5 (added DD-Decoherence)
- T12 → T13 (Boundary renumbered)

### Summary
Quantum mechanics is now complete without postulates:
- Unitary dynamics (FORCED)
- Born rule (DERIVED)
- Decoherence (DERIVED)
- No collapse (FORCED by unitarity)
- Measurement as relative (DERIVED)

## [1.0] - 2025-12-13

### Added
- **FORCED_SPINE.md**: Authoritative 12-thesis derivation (T0-T11)
- **DD-Born theorem**: Born rule μ = |ψ|² derived from unitarity + measure axioms
- Complete QM kinematics derivation without physics postulates

### Changed
- DERIVED count: 3 → 4 (added DD-Born)
- Structural boundary clearly marked: FORCED/DERIVED above, HYP/CONJ below

### Summary
The FORCED spine is complete:
- T0: Ø impossible (axiom)
- T1-T4: Distinction → Bool → self-application → ℕ
- T5-T6: Criticality → ℤ → ℚ → ℝ
- T7-T8: ℂ → U(n)
- T9-T10: ℝ-time → Hermitian H
- T11: Born rule (DERIVED)

Physics is not derived because it's not an axiom.
It's the only stable regime of history distinguishability.

## [0.9] - 2025-12-13

### Added
- DD-Generator Theorem: Hermitian generator H forced by Stone's theorem
- U(t) = e^{-itH} form uniquely determined by additive time → multiplicative operators
- Complete QM kinematics derivation: ℂ, U(n), t ∈ ℝ, H hermitian — all FORCED

### Changed
- FORCED count: 27 → 28
- H interpreted as "generator of distinguishability" (energy interpretation requires bridge)
- Stopping point for pure FORCED derivation clearly marked

### Note
This completes the FORCED derivation chain. All further structure (Born rule, energy interpretation, gauge groups, spacetime) requires HYP or further derivation.

## [0.8] - 2025-12-13

### Added
- DD-Time Theorem: ℝ uniquely forced as history parameter by criticality + unitarity
- Time parameter requirements: T1 (order), T2 (composition), T3 (invertibility), T4 (density)
- Proofs: ℤ fails (discrete jumps), ℚ fails (incomplete), ℝ unique (completeness theorem)

### Fixed
- GAP-3 closed: Continuous time ℝ now FORCED, not hypothetical
- HYP-F2 superseded by DD-Time

### Changed
- FORCED count: 26 → 27
- HYP count: 19 → 18
- All 4 major blocking gaps (GAP-1,2,3,4) now closed

## [0.7] - 2025-12-13

### Added
- DD-Unitarity Theorem: U(n) dynamics forced by criticality (not QM postulate)
- Unitarity Lemma: Non-unitary A has ‖Aⁿv‖ → 0 or ∞ (polar decomposition)
- Critical Dynamics Constraints: K1 (no collapse), K2 (no explosion), K3 (distinguishability)

### Changed
- Unitarity reframed as preservation of distinguishability, not probability

## [0.6] - 2025-12-13

### Added
- Chain-12: ℂ forced by automorphism closure (process distinguishability)
- Process Distinguishability Lemma: Orientation requires U(1) phase, not external time

### Changed
- Number system chain now complete: ℕ → ℤ → ℚ → ℝ → ℂ (all FORCED)
- GAP-3 (time) now has ℂ as prerequisite (phase before history)

## [0.5] - 2025-12-13

### Added
- Chain-9: ℤ forced by iteration comparison (signed differences for depth ordering)
- Chain-10: ℚ forced by commensurability (ratios for multi-generator comparison)
- Chain-11: ℝ forced by limit closure (Cauchy completeness for criticality)
- Continuum Lemma: Admissible structures closed under internal limits

### Fixed
- GAP-2 closed: Continuum (ℝ) now FORCED via criticality closure argument

## [0.4] - 2025-12-13

### Added
- GitHub infrastructure (.github/, docs/)
- CITATION.cff for proper citation
- CONTRIBUTING.md guidelines
- CODE_OF_CONDUCT.md
- Reviewer quickstart (60-minute path)
- docs/overview.md, reading_path.md, claims_and_status.md, falsifiability.md, faq.md

### Changed
- README.md: Complete rewrite with explicit "What this is / What this is NOT"
- Chain-7: Upgraded from FORCED* to FORCED (irreversibility argument)
- UAC.md: Added discrete formulation (ℕ suffices for classification)

### Fixed
- GAP-4 closed: Chain-7 now FORCED via irreversibility from Ø impossible
- GAP-1 closed: Φ defined as path entropy

## [0.3] - 2025-12-13

### Added
- 3_STATUS/ directory (STATUS.md, ROADMAP.md, THEORY_POSITION.md)
- 6_AUDITS/ directory (internal_audit.md, known_objections.md, failure_modes.md)
- CIRCULARITIES.md documenting CIRC-1 and CIRC-2

### Changed
- Complete label discipline (FORCED/DEF/HYP/CONJ/CIRC/PRED)
- Honest assessment of theory position

## [0.2] - 2025-12-12

### Added
- CRITICAL_REGIME.md with CR-1 to CR-7
- DEPENDENCY_GRAPH.md visualization

### Changed
- FORCED_CHAIN.md expanded with Bool and ℕ derivation

## [0.1] - 2025-12-12

### Added
- Initial spine structure (0_CORE/, 1_DERIVATION/, 2_EXPRESSION/)
- AXIOM.md, DEFINITIONS.md, UAC.md
- FORCED_CHAIN.md, BRIDGES.md
- Agda proofs (21 files)
- Python verification code (36 files)
- LaTeX documentation (31 chapters)
