# Universal Admissibility Criterion (UAC)

---

## Statement

- DEF **(UAC)**: A structure S is admissible iff 0 < Φ(S) < ∞.

Where Φ is the criticality functional defined below.

---

## Requirements on Φ

The following are structurally forced by UAC:

- FORCED **(P1; Invariance)**: Φ depends only on structure, not on representation.

- FORCED **(P2; Monotonicity)**: If S admits more composable paths/distinctions, Φ does not decrease.

- FORCED **(P3; Boundary sensitivity)**: Φ → 0 when distinctions collapse; Φ → ∞ when growth is uncontrolled.

- FORCED **(P4; Locality → globality)**: Φ aggregates from local transitions.

- FORCED **(P5; Dimensionlessness)**: Φ carries no units.

---

## Lemma: Uniqueness of Φ

**Statement:** Any Φ satisfying (P1–P5) is equivalent to exponential growth rate of distinguishable paths.

**Proof sketch:**

1. (P4) ⇒ Φ aggregates over path length
2. (P2) ⇒ growth is multiplicative under composition
3. (P5) ⇒ logarithm is required for dimensionlessness
4. (P3) ⇒ limit must distinguish 0 / finite / ∞

The unique form satisfying all constraints:

```
Φ = lim sup_{n→∞} (1/n) log P(n)
```

where P(n) = number of distinguishable paths of length n.

**Status:** FORCED (structural necessity, not choice)

---

## Canonical Definition

- DEF **(Φ; Path entropy)**: For a category/graph/distinction system S, let:

```
P_S(n) := number of distinguishable compositions of length n
```

Then:

```
Φ(S) := lim sup_{n→∞} (1/n) log P_S(n)
```

---

## Immediate Consequences

### Collapse (Φ = 0)

If path count is bounded:

```
P_S(n) = O(1) ⇒ Φ = 0
```

Structure collapses — violates UAC lower bound.

### Explosion (Φ = ∞)

If growth is superexponential:

```
P_S(n) ~ exp(n²) ⇒ Φ = ∞
```

Structure explodes — violates UAC upper bound.

### Critical regime (0 < Φ < ∞)

If growth is exponential:

```
P_S(n) ~ exp(h·n), 0 < h < ∞ ⇒ Φ = h
```

This is the admissible regime.

---

## Equivalences in Other Contexts

This definition of Φ is equivalent to known concepts:

| Context | Name |
|---------|------|
| Dynamical systems | Topological entropy |
| Graphs / automata | Growth rate |
| Groups | Exponential growth |
| Categories | Categorical entropy |
| Operators | log(spectral radius) |

These are the same mathematical object under different presentations.

---

## Status Summary

| ID | Statement | Status | Depends On |
|----|-----------|--------|------------|
| UAC | 0 < Φ < ∞ | DEF (criterion) | — |
| P1 | Invariance | FORCED | UAC |
| P2 | Monotonicity | FORCED | UAC |
| P3 | Boundary sensitivity | FORCED | UAC |
| P4 | Locality aggregation | FORCED | UAC |
| P5 | Dimensionlessness | FORCED | UAC |
| Φ-unique | Exponential form | FORCED | P1–P5 |
| Φ-def | Path entropy | DEF | Φ-unique |

---

## What This Does Not Derive

The following require additional structure:

- Which S describes the world (requires physics)
- Local generators of S (requires symmetry analysis)
- Spatial structure (requires topology)
- Gauge groups (requires representation theory)

These are bridges in `2_EXPRESSION/BRIDGES.md`.

---

## Reference

- Topological entropy: Adler, Konheim, McAndrew (1965)
- Categorical entropy: Dimitrov, Haiden, Katzarkov, Kontsevich (2014)
- Group growth: Grigorchuk, Milnor
