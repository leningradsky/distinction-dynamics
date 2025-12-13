# ROADMAP.md — Gap Closure Queue

**Last updated:** 2025-12-13

This file is a queue of gaps to be addressed, not a promise of results.
Items are ordered by logical priority, not by difficulty or time.

---

## Gap Queue

### Priority 1: Blocking Gaps (Must resolve before any claim upgrade)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| GAP-1 | Φ functional undefined | DEF-Φ reserved | Either specify Φ : A → ℝ concretely or remove from spine |
| GAP-4 | Chain-7 interpretation | FORCED* | Either prove unfolding is forced or downgrade to HYP |

### Priority 2: Major Bridges (HYP that block physics claims)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| GAP-2 | Continuum not derived | HYP-C1 | Either derive from discrete structure or accept as irreducible HYP |
| GAP-3 | Time (ℕ → ℝ) not derived | HYP-F2 | Either derive or mark as permanent hypothesis |
| GAP-7 | X: C → Hilb functor unspecified | DEF in BRIDGES.md | Specify concretely or remove |

### Priority 3: Questionable Claims (May be numerology)

| ID | Gap | Current Status | Required Action |
|----|-----|----------------|-----------------|
| GAP-5 | α = 137 formula | CONJ-A1 | Either derive (gen+gluons)²+(charge)² structure or downgrade to pattern-only |
| GAP-6 | 3+1 dimensions | HYP-S1 → CONJ | Already downgraded; need explicit derivation or delete claim |
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
