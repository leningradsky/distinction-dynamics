# Circular Dependencies

**Last updated:** 2025-12-13

This file documents all circular dependencies in the derivation.
Circles are not errors — they are mutual consistency requirements.
They must not be presented as linear derivations.

---

## CIRC-1: SU(3) ⟷ 3 Generations

### The Circle

```
SU(3) gauge group
       ↓
Anomaly cancellation requires N generations
       ↓
N = 3 for anomaly freedom with SU(3)
       ↓
3 generations assumed
       ↓
Triadic structure motivates SU(3)
       ↓
[returns to start]
```

### Direction A: 3 generations → SU(3)

**Statement:** Given 3 fermion generations, SU(3) is necessary for anomaly freedom.

**Status:** DERIVED (given HYP-G2)

**Justification:** Elimination proof — SU(2), SU(4), SU(5) fail anomaly constraints with 3 generations.

### Direction B: SU(3) → 3 generations

**Statement:** Given SU(3), 3 generations is "natural" (fundamental rep is 3-dimensional).

**Status:** HYP (not forced)

**Problem:** The fundamental representation dimension does not logically force 3 physical generations. It makes 3 "natural" but not necessary.

### Resolution

This is **mutual consistency**, not derivation:

- If you assume 3 generations, SU(3) follows (given anomaly requirement)
- If you assume SU(3), 3 is a natural number (but not forced)
- Together they form a self-consistent package

**Empirical support:** LEP measured N_ν = 2.984 ± 0.008

**What cannot be claimed:** "DD derives 3 generations from SU(3)" or "DD derives SU(3) from 3 generations" as independent facts.

---

## CIRC-2: Triad ⟷ Rank ≥ 2

### The Circle

```
Minimal structure assumption (Occam's Razor)
       ↓
What is the minimal self-observing structure?
       ↓
Dyad (2 elements) has rank 1
       ↓
Rank 1 insufficient for self-observation (claimed)
       ↓
Triad (3 elements) has rank 2
       ↓
Rank 2 sufficient (claimed)
       ↓
Triad is minimal structure with rank ≥ 2
       ↓
[but rank ≥ 2 requirement comes from triad analysis]
```

### Analysis

**Step 1:** Minimality is assumed (Occam's Razor) — **HYP**

**Step 2:** "Dyad insufficient for self-observation" — **HYP**
- Requires definition of "self-observation"
- Definition not in 0_CORE/
- This is an interpretive bridge

**Step 3:** "Rank 2 sufficient" — **FORCED given triad**
- If you have 3 elements, rank ≥ 2 follows mathematically

### Resolution

Proper statement:

> **HYP:** Assume minimality and self-observation requirement.
>
> **FORCED (given HYP):** The minimal structure satisfying self-observation has rank 2.

The circularity is in using rank 2 to motivate why we need triad, while triad gives us rank 2.

**What cannot be claimed:** "DD forces triad from pure logic."

**Honest statement:** "Given the hypothesis that self-observation requires rank ≥ 2, the minimal such structure is a triad."

---

## Summary Table

| ID | Circle | What's HYP | What's FORCED |
|----|--------|------------|---------------|
| CIRC-1 | SU(3) ⟷ generations | Generation count, anomaly requirement | Elimination given assumptions |
| CIRC-2 | Triad ⟷ rank | Minimality, self-observation definition | Rank 2 from triad structure |

---

## Rules for Presentation

1. **Never claim linear derivation** across a CIRC boundary
2. **Always state both directions** with their individual statuses
3. **Empirical support is not proof** — it's consistency check
4. **"Natural" ≠ "necessary"** — distinguish these clearly
5. **Document the package** — the value is in mutual consistency, not linear implication

---

## Reference

See also:
- `2_EXPRESSION/BRIDGES.md` §9 (full details)
- `3_STATUS/STATUS.md` (master status table)
