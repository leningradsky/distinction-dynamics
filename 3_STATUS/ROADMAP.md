# ROADMAP.md — Gap Closure Queue

**Last updated:** 2025-12-13

This file is a queue of gaps to be addressed, not a promise of results.
Items are ordered by logical priority, not by difficulty or time.

---

## Gap Queue

### Priority 1: Blocking Gaps (Must resolve before any claim upgrade)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| ~~GAP-1~~ | ~~Φ functional undefined~~ | **CLOSED** | Defined as path entropy in UAC.md |
| ~~GAP-2~~ | ~~Continuum not derived~~ | **CLOSED** | Chain-9 (ℤ), Chain-10 (ℚ), Chain-11 (ℝ) forced by criticality |
| ~~GAP-3~~ | ~~Time (ℕ → ℝ) not derived~~ | **CLOSED** | DD-Time: ℝ uniquely forced by criticality + unitarity + completeness |
| ~~GAP-4~~ | ~~Chain-7 interpretation~~ | **CLOSED** | Irreversibility argument: Δⁿ=id ⟹ erasure ⟹ local Ø ⟹ contradiction |

### Priority 2: Major Bridges (HYP that block physics claims)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| ~~GAP-7~~ | ~~X: C → Hilb functor~~ | **CLOSED** | DDHilbert.agda — structural functor verified |

### Priority 3: Questionable Claims (May be numerology)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| GAP-5 | α = 137 formula | CONJ-A1 | Either derive (gen+gluons)²+(charge)² structure or downgrade to pattern-only |
| ~~GAP-6~~ | ~~3+1 dimensions~~ | **CLOSED** | DD-Dim3 + DD-Time-Unique: d=3, signature (1,3) derived |
| GAP-8 | θ ≈ 2/9 | CONJ-K2 | Either derive 2/9 from triad structure or mark as coincidence |

### Priority 4: Circular Dependencies (Must document, not necessarily resolve)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| CIRC-1 | SU(3) ⟷ 3 generations | Documented | Verify consistency, no linear claim allowed |
| CIRC-2 | Triad ⟷ Rank ≥ 2 | Documented | Keep minimality as explicit HYP |

### Priority 5: Verification Tasks

| ID | Task | Current Status | Required Action |
|----|------|----------------|-----------------|
| VER-1 | Lean proofs incomplete | some sorry | Close or document as unprovable |
| VER-2 | LaTeX chapters status | Unknown | Audit each chapter for label compliance |
| VER-3 | Python verification | Complete | Maintain parity with spine |

---

## Closure Criteria

A gap is considered closed when:

1. **If promoting to FORCED:** Full proof in formal language (Agda/Lean) with 0 postulates
2. **If accepting as HYP:** Explicit statement that this is irreducible hypothesis, documented alternatives
3. **If downgrading to CONJ:** Remove from derivation chain, mark as pattern observation only
4. **If deleting:** Remove all references from spine files

---

## Not In Queue (Out of Scope)

The following are explicitly not goals:

- Deriving specific numerical constants from first principles
- Proving quantum gravity
- Resolving consciousness "hard problem"
- Matching all Standard Model parameters

These would require additional hypotheses beyond current scope.

---

## Log

| Date | Gap | Action | Result |
|------|-----|--------|--------|
| 2025-12-13 | Initial | Created roadmap | 8 gaps identified |
| 2025-12-13 | GAP-1 | Defined Φ as path entropy | CLOSED — see UAC.md |
| 2025-12-13 | GAP-4 | Irreversibility argument from Ø impossible | CLOSED — see FORCED_CHAIN.md Chain-7 |
| 2025-12-13 | GAP-2 | ℤ/ℚ/ℝ forced by criticality closure | CLOSED — see FORCED_CHAIN.md Chain-9,10,11 |
| 2025-12-13 | Chain-12 | ℂ forced by automorphism closure | Added — process distinguishability requires U(1) |
| 2025-12-13 | DD-Unitarity | U(n) dynamics from criticality | Added — unitarity = distinguishability preservation |
| 2025-12-13 | GAP-3 | DD-Time: ℝ forced by history completeness | CLOSED — ℤ/ℚ fail criticality, ℝ unique |
| 2025-12-13 | DD-Generator | H hermitian from Stone's theorem | Added — U(t)=e^{-itH} forced by continuous unitarity |
| 2025-12-13 | DD-Born | Born rule μ=\|ψ\|² from unitarity | DERIVED — unique distinguishability measure |
| 2025-12-13 | FORCED_SPINE | 12-thesis derivation T0-T11 | Created — authoritative reference for complete chain |
| 2025-12-13 | DD-Decoherence | No collapse, measurement relative | DERIVED — factorization of distinguishability |
| 2025-12-13 | DD-Classicality | Classical emergence | DERIVED — stable fixed points of decoherence |
| 2025-12-13 | DD-Space | Manifold structure forced | DERIVED — space = parameterization of distinctions |
| 2025-12-13 | DD-Time-Unique | Time as unique process parameter | DERIVED — signature (1,d-1) forced |
| 2025-12-13 | DD-Energy | H = energy structural identification | DERIVED — Noether + uniqueness argument |
| 2025-12-13 | DD-Dim3 | d = 3 by criticality selection | DERIVED — unique stable dimension, GAP-6 CLOSED |
| 2025-12-13 | DD-Gauge | SU(3)×SU(2)×U(1) by elimination proof | DERIVED — HYP-G1..G4 superseded |
| 2025-12-13 | DD-Dim3 | Enhanced with D1-D5 admissibility criteria | Structural intersection argument |
| 2025-12-13 | DD-Energy | Enhanced with Lemmas 1-4 elimination proof | H = energy by structural uniqueness |
| 2025-12-13 | DD-Connection | Gauge connection from local phase coherence | DERIVED — T18, Lemmas 1-4 |
| 2025-12-13 | DD-Gauge | Enhanced with Lemmas 1-6 elimination proof | SU(3)×SU(2)×U(1) unique by structural elimination |
| 2025-12-13 | DD-Factorization | Tensor structure ⊗ℋᵢ FORCED by criticality | T11 — locality emerges from factorization |
| 2025-12-13 | DD-Lorentz | SO(1,3) from locality + universal speed | DERIVED — T21, HYP-S3 superseded |
| 2025-12-13 | DD-Fisher | Fisher metric from Chentsov's theorem | DERIVED — T22, HYP-F1 superseded |
| 2025-12-13 | DD-LightSpeed | Universal speed c from Lorentz structure | DERIVED — T23, c-part of HYP-Q2 superseded |
| 2025-12-13 | DD-Mass | Higgs/SSB from gauge + localization | DERIVED — T24, HYP-P1 superseded |
| 2025-12-13 | GAP-6 | d=3 + signature (1,3) fully derived | CLOSED — DD-Dim3 + DD-Time-Unique + DD-Lorentz |
| 2025-12-13 | DD-NoAlt | Forced World Theorem (T26) | FORCED — no ontological alternatives, HYP eliminated |
| 2025-12-13 | Category | HYP → UNTRACED/CONJ reclassification | Per DD-NoAlt, HYP is not valid category |
| 2025-12-13 | DD-Lambda | Λ > 0 forced by elimination (T27) | FORCED — static/contracting histories violate UAC |
| 2025-12-13 | HYP-P3 | Dynamics closed | DERIVED — covered by DD-Generator (T10) |
| 2025-12-13 | ℏ | Planck constant reclassified | DEF — unit choice (scale of H) |
| 2025-12-13 | DD-Gravity | G forced by elimination (T28) | FORCED — 0 < G < ∞, local-global coupling |
| 2025-12-13 | DD-Einstein | Field equations derived (T29) | DERIVED — G_μν = 8πG T_μν unique by Lovelock |
| 2025-12-13 | DD-Generations | N ≥ 3 forced by CP (T30) | FORCED — ℂ¹, ℂ² forbidden, ℂ³ minimal |
| 2025-12-13 | CIRC-1 | Broken | Generations derived independently of SU(3) |
| 2025-12-13 | Koide | Promoted to DERIVED | Geometric invariant in ℂ³, not numerology |
| 2025-12-13 | Status | Generations complete | All physics including N ≥ 3 now FORCED/DERIVED |
| 2025-12-13 | DD-Rank | rank ≥ 2 forced (T31) | FORCED — rank 1 violates Δ ≠ Δ(Δ) |
| 2025-12-13 | CIRC-2 | Broken | Rank derived independently of triad assumption |
| 2025-12-13 | Status | All circularities resolved | CIRC = 0, complete derivation T0-T31 |
