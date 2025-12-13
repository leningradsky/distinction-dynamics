# Internal Audit

**Last updated:** 2025-12-13

Self-critical assessment of the repository. No rhetoric, no defense.

---

## Audit Summary

| Category | Assessment |
|----------|------------|
| Label discipline | A (complete) |
| Dependency tracking | A- (documented, some implicit) |
| Separation of layers | A (clear) |
| Circularity disclosure | A (documented) |
| Gap acknowledgment | A (explicit) |
| Overclaim prevention | B+ (some legacy in LaTeX) |
| Formal verification | B (Agda complete, Lean partial) |

---

## Structural Issues

### Issue 1: Chain-7 Status Ambiguity

**Location:** `1_DERIVATION/FORCED_CHAIN.md` Chain-7

**Problem:** Marked as FORCED* with caveat. The asterisk indicates interpretive choice (unfolding vs. fixed point). This is not clean.

**Risk:** Readers may treat FORCED* as FORCED and propagate the caveat error.

**Recommendation:** Either:
- Prove unfolding is forced (promote to FORCED)
- Acknowledge interpretation (downgrade to HYP)

### Issue 2: Φ Functional Undefined

**Location:** `0_CORE/DEFINITIONS.md` DEF-Φ

**Problem:** Φ is "reserved for later bridges" but never specified. Dead definition.

**Risk:** Suggests future derivation that may never happen.

**Recommendation:** Either specify or remove.

### Issue 3: LaTeX Chapters Unaudited

**Location:** `Part_I_*` through `Part_V_*`

**Problem:** 31 chapters written before systematic labeling. Unknown compliance with FORCED/HYP/CONJ discipline.

**Risk:** Contradictions between LaTeX and spine files.

**Recommendation:** Full audit of each chapter. Mark as "legacy" until audited.

### Issue 4: Python Code Verification Scope

**Location:** `code/` directory

**Problem:** 36 files verify various claims, but correspondence to spine is unclear.

**Risk:** Code may verify claims not in spine, or miss spine claims.

**Recommendation:** Create verification matrix mapping code to STATUS.md entries.

---

## Logical Issues

### Issue 5: Self-Observation Definition Missing

**Location:** CIRC-2 in `2_EXPRESSION/CIRCULARITIES.md`

**Problem:** "Self-observation" used to justify triad over dyad, but never formally defined in 0_CORE/.

**Risk:** Circular argument hidden in undefined term.

**Recommendation:** Either:
- Define "self-observation" formally in DEFINITIONS.md
- Mark dyad-insufficiency as HYP (interpretive)

### Issue 6: Continuum Bridge Underspecified

**Location:** HYP-C1 in `2_EXPRESSION/BRIDGES.md`

**Problem:** "Taking appropriate limits/completions" is vague. No concrete construction.

**Risk:** Appears derivation-like but is actually stipulation.

**Recommendation:** Either:
- Provide explicit construction (Cauchy completion, etc.)
- Acknowledge as axiom-level assumption

### Issue 7: α = 137 Formula

**Location:** CONJ-A1 in `2_EXPRESSION/BRIDGES.md`

**Problem:** Formula 11² + 4² = 137 has no derivation of why (gen+gluons)² + (charge)².

**Risk:** Numerology presented as pattern.

**Current status:** Marked CONJ. Correct.

**Recommendation:** Keep as CONJ, never promote without explicit derivation.

---

## Documentation Issues

### Issue 8: README Length

**Location:** `README.md`

**Problem:** 362 lines. Contains derivation details that belong in other files.

**Risk:** README becomes out of sync with STATUS.md.

**Recommendation:** Trim README to navigation + summary only. Move details to STATUS.md.

### Issue 9: Duplicate Information

**Problem:** CIRC-1 and CIRC-2 appear in both BRIDGES.md and CIRCULARITIES.md.

**Risk:** Divergence over time.

**Recommendation:** BRIDGES.md should reference CIRCULARITIES.md, not duplicate.

---

## Verification Issues

### Issue 10: Lean Proofs Incomplete

**Location:** `lean/` directory

**Problem:** Some `sorry` statements remain.

**Risk:** Claims appear proven but are not.

**Recommendation:** Either complete or document which theorems remain unproven.

### Issue 11: Agda vs. Spine Correspondence

**Location:** `agda/` vs `1_DERIVATION/`

**Problem:** Agda proves more than spine claims (e.g., Koide). Spine says Koide is DERIVED (given HYP), but Agda may prove without explicit HYP.

**Risk:** Agda proofs may contain hidden assumptions.

**Recommendation:** Audit Agda for hidden postulates/axioms beyond what's in 0_CORE/.

---

## Action Items

| Priority | Issue | Action |
|----------|-------|--------|
| 1 | Issue 1 | Resolve Chain-7 status |
| 1 | Issue 2 | Specify or remove Φ |
| 2 | Issue 5 | Define self-observation or mark HYP |
| 2 | Issue 6 | Specify continuum construction |
| 3 | Issue 3 | Audit LaTeX chapters |
| 3 | Issue 8 | Trim README |
| 3 | Issue 9 | Remove duplication |
| 4 | Issue 10 | Complete or document Lean |
| 4 | Issue 11 | Audit Agda assumptions |

---

## Audit Log

| Date | Auditor | Finding |
|------|---------|---------|
| 2025-12-13 | Internal | Initial audit, 11 issues identified |
