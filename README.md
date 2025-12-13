# Distinction Dynamics (DD)

> **Δ = Δ(Δ)** — Distinction distinguishes itself

**Version:** v0.4 (Post-Audit Stable Spine)

---

## What This Is

DD is a **constraint framework** that derives structural necessities from a single prohibition:

```
Ø is impossible
```

From this, DD forces:
- Binary structure (Bool)
- Natural numbers (ℕ)
- Critical regime constraints (finite generators, non-commutativity)

DD then explores **bridges** to physics through explicit hypotheses (HYP), showing that observed physics is *compatible* with distinction-based structure.

## What This Is NOT

- ❌ **Not a Theory of Everything** — DD does not derive all physics from one axiom
- ❌ **Not complete** — Continuum, time, and quantum mechanics require hypotheses
- ❌ **Not claiming derivation of constants** — Values like α=137 may be numerology
- ❌ **Not without assumptions** — ~20 HYP required for physics bridges

**Better characterization:**
> DD is a self-consistent framework showing that observed physics is compatible with an information-geometric triadic structure, with explicit labeling of what is forced vs assumed.

---

## Status Snapshot

| Label | Count | Meaning |
|-------|-------|---------|
| **FORCED** | 21 | Logically necessary from axiom |
| **DEF** | 8 | Definitions/conventions |
| **HYP** | 20 | Hypotheses requiring justification |
| **DERIVED** | 3 | Follows from HYP + FORCED |
| **CONJ** | 3 | Conjectures (may be numerology) |
| **CIRC** | 2 | Circular dependencies |
| **PRED** | 1 | Testable prediction |

**Master truth file:** [3_STATUS/STATUS.md](3_STATUS/STATUS.md)

**Open gaps:** GAP-2 (continuum), GAP-3 (time), GAP-5 (α=137), GAP-6 (3+1 dim)

**Closed gaps:** GAP-1 (Φ defined), GAP-4 (Chain-7 FORCED via irreversibility)

---

## Reviewer Quickstart (60 minutes)

**Path for critical review:**

| Time | File | Purpose |
|------|------|---------|
| 5 min | This README | Overview and scope |
| 10 min | [0_CORE/AXIOM.md](0_CORE/AXIOM.md) | The sole primitive |
| 15 min | [1_DERIVATION/FORCED_CHAIN.md](1_DERIVATION/FORCED_CHAIN.md) | What is actually FORCED |
| 10 min | [2_EXPRESSION/BRIDGES.md](2_EXPRESSION/BRIDGES.md) | HYP/CONJ bridges to physics |
| 10 min | [6_AUDITS/failure_modes.md](6_AUDITS/failure_modes.md) | How to break the theory |
| 10 min | [3_STATUS/STATUS.md](3_STATUS/STATUS.md) | Master truth file |

**Key questions for reviewers:**
1. Is Chain-7 (irreversibility → ℕ) valid?
2. Are the HYP bridges justified or ad hoc?
3. Is CONJ-A1 (α=137) numerology or structure?

---

## What Would Falsify This?

See [6_AUDITS/failure_modes.md](6_AUDITS/failure_modes.md) for complete list.

**Critical falsifications:**

| ID | Condition | Impact |
|----|-----------|--------|
| FAIL-1 | Contradiction in FORCED chain | Total collapse |
| FAIL-5 | Koide formula violated (Belle II) | ℤ₃ structure fails |
| FAIL-7 | w(z) = -1.000 ± 0.001 exactly | PRED-Λ3 ruled out |
| FAIL-8 | Fourth generation discovered | Anomaly argument fails |

**Most testable:** PRED-Λ3 (w(z) ≠ -1) — DESI, Euclid, Rubin Observatory within 5 years.

---

## Repository Structure

### Formal Spine

```
0_CORE/           ← Axiom + Definitions + UAC
├── AXIOM.md           "Ø is impossible"
├── DEFINITIONS.md     Σ, A, ≼, C, Φ
└── UAC.md             0 < Φ < ∞ criterion

1_DERIVATION/     ← FORCED consequences
├── FORCED_CHAIN.md    Chain-5..8, L1-L4, CR-1..7
├── CRITICAL_REGIME.md Structural constraints
└── DEPENDENCY_GRAPH.md Visual map

2_EXPRESSION/     ← Bridges to physics
├── BRIDGES.md         All HYP/CONJ/DERIVED
└── CIRCULARITIES.md   CIRC-1, CIRC-2

3_STATUS/         ← Truth tracking
├── STATUS.md          Master truth file
├── ROADMAP.md         Gap closure queue
└── THEORY_POSITION.md Post-audit statement

6_AUDITS/         ← Self-criticism
├── internal_audit.md   11 structural issues
├── known_objections.md 13 objections acknowledged
└── failure_modes.md    10 falsification conditions
```

### Formal Verification

| Directory | Status |
|-----------|--------|
| `agda/` | 21 files, 0 postulates |
| `lean/` | Partial (some `sorry`) |
| `proofs/` | Coq proofs |

### Auxiliary (Not Part of Spine)

| Directory | Note |
|-----------|------|
| `code/` | 36 Python verification scripts |
| `Part_I..V/` | **Unaudited legacy material** — not part of formal spine |
| `book/` | PDF compilation |

---

## FORCED Chain Summary

```
Ø impossible (DEF-AX)
    ↓
Σ, A, ≼, C (definitions)
    ↓
L1-L4: Category properties ← FORCED
    ↓
Chain-5: Bool ← FORCED
    ↓
Chain-6: Δ = Δ(Δ) ← FORCED (self-application)
    ↓
Chain-7: {Δⁿ} infinite ← FORCED (irreversibility from Ø impossible)
    ↓
Chain-8: ℕ ≅ {Δⁿ} ← FORCED (monoid isomorphism)
    ↓
UAC: 0 < Φ < ∞ (definition)
    ↓
CR-1..CR-7: Critical Regime ← FORCED
    ↓
════════════════════════════════
FORCED DERIVATION ENDS HERE
════════════════════════════════
    ↓
Physics bridges require HYP
See 2_EXPRESSION/BRIDGES.md
```

**Key insight:** The entire FORCED chain uses only ℕ. Continuum (ℝ) is needed only for physics bridges, not for the core derivation.

---

## Bridges to Physics (HYP)

| Bridge | Status | Depends On |
|--------|--------|------------|
| Continuum emergence | HYP-C1 | Not derived |
| Fisher metric | HYP-F1 | HYP-C1 |
| Time parameter | HYP-F2 | Not derived |
| Gauge invariance | HYP-G1 | HYP-S4 |
| Anomaly freedom | HYP-G2 | Empirical |
| Asymptotic freedom | HYP-G3 | Nobel 2004 |
| Confinement | HYP-G4 | Empirical |

**Derived results (given HYP):**
- SU(3) uniqueness (elimination proof)
- Koide Q = 2/3 (99.999% fit)
- ε = √2

**Conjectures (may be numerology):**
- 1/α = 11² + 4² = 137 (CONJ-A1)
- θ ≈ 2/9 (CONJ-K2)
- 3+1 dimensions (CONJ)

---

## Known Objections

See [6_AUDITS/known_objections.md](6_AUDITS/known_objections.md) for 13 acknowledged objections with responses.

**Sample:**
- "The axiom is trivial" → Response: It constrains structure uniquely
- "Too many hypotheses" → Response: Explicitly labeled, unlike hidden assumptions elsewhere
- "α=137 is numerology" → Response: Acknowledged as CONJ, not claimed as derivation

---

## Running Verification Code

```bash
# Verify core derivation
python code/dd_formal_derivation.py

# Full verification suite
python code/dd_full_verification.py
```

Note: Code is auxiliary verification, not part of formal spine.

---

## Citation

```bibtex
@misc{distinction-dynamics,
  author = {Shkursky, Andrey},
  title = {Distinction Dynamics: A Constraint Framework},
  year = {2025},
  version = {0.4},
  url = {https://github.com/leningradsky/distinction-dynamics}
}
```

---

## License

[MIT](LICENSE)

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

Key rule: All claims must be labeled (FORCED/DEF/HYP/CONJ/CIRC/PRED).

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| v0.4 | 2025-12-13 | GAP-1, GAP-4 closed; UAC discrete clarification |
| v0.3 | 2025-12-13 | Post-audit spine; explicit labeling |
| v0.2 | 2025-12-12 | Critical regime added |
| v0.1 | 2025-12-12 | Initial spine |
