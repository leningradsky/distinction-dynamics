# Circular Dependencies

**Last updated:** 2025-12-13 (v2.5)

This file documents circular dependencies in the derivation.
Circles are not errors — they are mutual consistency requirements.
They must not be presented as linear derivations.

**Status:** ALL CIRCULARITIES RESOLVED
- CIRC-1 **BROKEN** by T30 (DD-Generations)
- CIRC-2 **BROKEN** by T31 (DD-Rank)

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

## ~~CIRC-2: Triad ⟷ Rank ≥ 2~~ — BROKEN

### Status: RESOLVED by DD-Rank (T31)

**The circularity was:**
```
Triad ⟷ Rank ≥ 2
```

**Resolution:** T31 (DD-Rank) derives rank ≥ 2 **independently** of triad:

1. **Rank 1 forbidden:** In dim = 1, every endomorphism Δ is λ·id
2. **Therefore Δ(Δ) = λ²·id ∝ Δ**
3. **By T3:** Δ ≠ Δ(Δ) (distinction non-triviality)
4. **Contradiction:** rank = 1 violates T3
5. **∴ rank ≥ 2 FORCED**

This breaks the circle:
- Rank ≥ 2 is FORCED from T3 (distinction non-triviality)
- Triad is minimal realization, not assumption
- No appeal to "self-observation" required

**See:** [FORCED_SPINE.md](../1_DERIVATION/FORCED_SPINE.md) §Level 25 (T31)

---

## Summary Table

| ID | Circle | Status | Resolution |
|----|--------|--------|------------|
| ~~CIRC-1~~ | SU(3) ⟷ generations | **BROKEN** | T30: N ≥ 3 from CP violation |
| ~~CIRC-2~~ | Triad ⟷ rank | **BROKEN** | T31: rank ≥ 2 from Δ ≠ Δ(Δ) |

**Remaining circularities:** 0

All circular dependencies have been resolved by independent derivations.

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
