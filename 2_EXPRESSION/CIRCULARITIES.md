# Circular Dependencies

**Last updated:** 2025-12-13 (v2.4)

This file documents circular dependencies in the derivation.
Circles are not errors — they are mutual consistency requirements.
They must not be presented as linear derivations.

**Status:** CIRC-1 has been **BROKEN** by T30 (DD-Generations).

---

## ~~CIRC-1: SU(3) ⟷ 3 Generations~~ — BROKEN

### Status: RESOLVED by DD-Generations (T30)

**The circularity was:**
```
SU(3) gauge group ⟷ 3 fermion generations
```

**Resolution:** T30 (DD-Generations) derives N_gen ≥ 3 **independently** of SU(3):

1. **ℂ¹ forbidden:** CP violation eliminable by basis change
2. **ℂ² forbidden:** CP-phase removable by unitary transformation
3. **ℂ³ minimal:** First dimension with irremovable phase

This breaks the circle:
- N ≥ 3 is now FORCED from CP violation requirement (T30)
- SU(3) remains DERIVED from gauge constraints (T22)
- The two are independently established, not mutually assumed

**See:** [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) §Level 24 (T30)

**Empirical support:** LEP measured N_ν = 2.984 ± 0.008 ✓

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

| ID | Circle | Status | Resolution |
|----|--------|--------|------------|
| ~~CIRC-1~~ | SU(3) ⟷ generations | **BROKEN** | T30 derives N ≥ 3 independently |
| CIRC-2 | Triad ⟷ rank | Active | Minimality + self-observation |

**Remaining circularities:** 1 (CIRC-2 only)

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
