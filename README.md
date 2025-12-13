# Distinction Dynamics (DD)

> **Δ = Δ(Δ)** — Distinction distinguishes itself

**Version:** v2.4 (T0-T30 Complete Derivation Chain)

---

## What This Is

DD is a **constraint framework** that derives structural necessities from a single prohibition:

```
Ø is impossible
```

From this, DD forces:
- Binary structure (Bool)
- Number systems: ℕ → ℤ → ℚ → ℝ → ℂ
- Critical regime constraints (finite generators, non-commutativity)
- Unitary dynamics U(n) — not a quantum postulate, but criticality preservation
- Continuous time parameter t ∈ ℝ — not assumed, but forced by history completeness
- Hermitian generator H with U(t) = e^{-itH} — Stone's theorem, forced by continuous unitarity
- Born rule μ = |ψ|² — unique distinguishability measure (DERIVED from unitarity)
- Decoherence without collapse — measurement as relative distinguishability (DERIVED)
- Classical emergence — stable fixed points of decoherence (DERIVED)
- Space (manifold structure) — parameterization of stable distinctions (DERIVED)
- Time uniqueness — exactly one process parameter, signature (1,d-1) (DERIVED)
- Energy — H structurally identified as time-conjugate observable (DERIVED)
- d = 3 — unique stable dimension by criticality selection (DERIVED)
- SU(3)×SU(2)×U(1) — unique gauge group by elimination proof (DERIVED)

**Key insight:** Physics is not derived because it's "true" — it's the only stable regime of history distinguishability. Per DD-NoAlt (T26), there are no ontological alternatives.

**Authoritative reference:** [FORCED_SPINE.md](1_DERIVATION/FORCED_SPINE.md) — complete derivation T0-T30.

## What This Is NOT

- ❌ **Not a Theory of Everything** — DD derives structure, not numerical values
- ❌ **Not claiming derivation of constants** — Values like α ≈ 1/137 remain CONJ
- ❌ **Not falsified by specific values** — DD constrains domains (BOUND), not exact numbers

**What DD claims:**
> DD derives that physics *must* have certain structural features (gauge symmetry, 3+1 dimensions, N ≥ 3 generations) — not because they're axioms, but because alternatives violate UAC.

---

## Status Snapshot

| Label | Count | Meaning |
|-------|-------|---------|
| **FORCED** | 33 | Logically necessary from axiom |
| **DEF** | 9 | Definitions/conventions |
| **DERIVED** | 18 | Follows from FORCED chain |
| **CONJ** | 3 | Conjectures (numerical patterns) |
| **CIRC** | 1 | Circular dependency (CIRC-2 only) |
| **PRED** | 1 | Testable prediction |
| ~~HYP~~ | 0 | **Eliminated** by DD-NoAlt (T26) |

**Master truth file:** [3_STATUS/STATUS.md](3_STATUS/STATUS.md)

**Open gaps:** GAP-5 (α ≈ 1/137), GAP-7 (functor), GAP-8 (Koide numerics)

**Closed gaps:** GAP-1 (Φ), GAP-2 (continuum), GAP-3 (time), GAP-4 (irreversibility), GAP-6 (d=3)

---

## Reviewer Quickstart (60 minutes)

**Path for critical review:**

| Time | File | Purpose |
|------|------|---------|
| 5 min | This README | Overview and scope |
| 10 min | [0_CORE/AXIOM.md](0_CORE/AXIOM.md) | The sole primitive |
| 20 min | [1_DERIVATION/FORCED_SPINE.md](1_DERIVATION/FORCED_SPINE.md) | **Complete derivation T0-T30** |
| 10 min | [2_EXPRESSION/BRIDGES.md](2_EXPRESSION/BRIDGES.md) | Numerical patterns (CONJ) |
| 5 min | [6_AUDITS/failure_modes.md](6_AUDITS/failure_modes.md) | How to break the theory |
| 10 min | [3_STATUS/STATUS.md](3_STATUS/STATUS.md) | Master truth file |

**Key questions for reviewers:**
1. Is T4 (irreversibility → ℕ) valid?
2. Is T26 (DD-NoAlt) legitimate elimination of alternatives?
3. Is CONJ-A1 (α ≈ 1/137) numerology or structure?

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
├── FORCED_SPINE.md    ★ T0-T30 complete derivation (authoritative)
├── FORCED_CHAIN.md    Legacy notation (Chain-5..8, L1-L4, CR-1..7)
└── CRITICAL_REGIME.md Structural constraints

2_EXPRESSION/     ← Numerical patterns
├── BRIDGES.md         CONJ claims (α, Koide angles)
└── CIRCULARITIES.md   CIRC-2 (Triad ⟷ Rank)

3_STATUS/         ← Truth tracking
├── STATUS.md          Master truth file
└── ROADMAP.md         Gap closure log

6_AUDITS/         ← Self-criticism
├── internal_audit.md   Structural issues
├── known_objections.md Objections acknowledged
└── failure_modes.md    Falsification conditions
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

## Derivation Summary (T0-T30)

```
T0: Ø impossible (axiom)
    ↓
T1-T3: Σ, A, ≼, C, Φ (definitions)
    ↓
T4: Irreversibility → ℕ (FORCED)
    ↓
T5-T7: ℤ → ℚ → ℝ (FORCED by completeness)
    ↓
T8-T13: Unitarity, Generators, Born rule, Decoherence (FORCED)
    ↓
T14-T17: Space, Time, Energy, d=3 (DERIVED)
    ↓
T18-T25: Gauge structure SU(3)×SU(2)×U(1) (DERIVED)
    ↓
T26: DD-NoAlt — no ontological alternatives (FORCED)
    ↓
T27-T28: Λ > 0, 0 < G < ∞ (FORCED)
    ↓
T29: Einstein equations G_μν = 8πG T_μν (DERIVED)
    ↓
T30: N_gen ≥ 3 fermion generations (FORCED)
    ↓
═══════════════════════════════════════════
  COMPLETE: Standard Model + GR structure
  All from "Ø is impossible"
═══════════════════════════════════════════
```

**See [FORCED_SPINE.md](1_DERIVATION/FORCED_SPINE.md) for complete proofs.**

---

## Remaining Conjectures (CONJ)

What is **not** derived — numerical patterns that may be coincidence:

| ID | Claim | Fit | Status |
|----|-------|-----|--------|
| CONJ-A1 | 1/α = 11² + 4² = 137 | 99.97% | May be numerology |
| CONJ-K2 | θ ≈ 2/9 (Koide angle) | ~99% | Geometric? |
| HYP-K3 | sin²θ_W = 3/8 | — | Numerical pattern |

**What IS derived (no longer hypotheses):**
- Continuum ℝ → T5-T7 (FORCED)
- Time parameter → T15 DD-Time (DERIVED)
- Gauge structure → T18-T25 DD-Gauge (DERIVED)
- Spacetime d=3+1 → T17 DD-Dim3 (DERIVED)
- Fermion generations N ≥ 3 → T30 DD-Generations (FORCED)
- Koide Q = 2/3 → geometric invariant in ℂ³ (DERIVED from T30)

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

Key rule: All claims must be labeled (FORCED/DEF/DERIVED/CONJ/CIRC/PRED).

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| v2.4 | 2025-12-13 | T30 DD-Generations; N ≥ 3 FORCED; Koide geometric; CIRC-1 broken |
| v2.3 | 2025-12-13 | T29 DD-Einstein; field equations DERIVED via Lovelock |
| v2.2 | 2025-12-13 | T28 DD-Gravity; 0 < G < ∞ FORCED |
| v2.1 | 2025-12-13 | T27 DD-Lambda; Λ > 0 FORCED |
| v2.0 | 2025-12-13 | T26 DD-NoAlt; HYP category eliminated; T0-T30 unified system |
| v1.7 | 2025-12-13 | DD-Gauge; SU(3)×SU(2)×U(1) DERIVED |
| v1.6 | 2025-12-13 | DD-Dim3; d = 3 DERIVED |
| v1.5 | 2025-12-13 | DD-Energy; H = energy DERIVED |
| v1.4 | 2025-12-13 | DD-Time-Unique; signature (1,d-1) DERIVED |
| v1.3 | 2025-12-13 | DD-Space; manifold structure DERIVED |
| v0.4 | 2025-12-13 | GAP-1, GAP-4 closed |
| v0.1 | 2025-12-12 | Initial spine |
