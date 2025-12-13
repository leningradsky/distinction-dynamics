# Contributing to Distinction Dynamics

Thank you for your interest in contributing.

## Ground Rules

### 1. Label Everything

Every claim must be labeled:
- **FORCED**: Logically necessary from axiom
- **DEF**: Definition or convention
- **HYP**: Hypothesis requiring justification
- **CONJ**: Conjecture (may be numerology)
- **CIRC**: Circular dependency
- **PRED**: Testable prediction
- **DERIVED**: Follows from HYP + FORCED

If you add a claim, you must label it.

### 2. Don't Strengthen Claims

Do not promote:
- HYP to FORCED without proof
- CONJ to DERIVED without derivation
- Any claim without explicit justification

### 3. Update STATUS.md

If you change claim status, update [3_STATUS/STATUS.md](3_STATUS/STATUS.md).

### 4. Use Relative Links

All internal links must be relative, not absolute.

## Types of Contributions

### Theory Issues

Found a gap or inconsistency? Use the [Theory Issue template](.github/ISSUE_TEMPLATE/theory_issue.md).

### Bug Reports

Found an error in code or documentation? Use the [Bug Report template](.github/ISSUE_TEMPLATE/bug_report.md).

### Questions

Have a question? Use the [Question template](.github/ISSUE_TEMPLATE/question.md).

### Pull Requests

1. Fork the repository
2. Create a branch (`git checkout -b feature/your-feature`)
3. Make changes following the rules above
4. Update STATUS.md if needed
5. Submit PR using the [PR template](.github/PULL_REQUEST_TEMPLATE.md)

## Commit Messages

Use prefixes:
- `docs:` — Documentation changes
- `theory:` — Theory/spine changes
- `proof:` — Formal proof changes
- `code:` — Python/verification code
- `github:` — GitHub infrastructure
- `chore:` — Maintenance

Examples:
```
docs: Update README with falsifiability section
theory: Close GAP-4 via irreversibility argument
proof: Add Agda proof for CR-5
```

## What We Need

### High Priority
- Review of Chain-7 irreversibility argument
- Analysis of HYP bridges (justified or ad hoc?)
- CONJ-A1 (α=137) investigation

### Medium Priority
- Lean proof completion (remove `sorry`)
- LaTeX chapter audit for label compliance
- Additional falsification tests

### Low Priority
- Code documentation
- Alternative formalizations

## Code of Conduct

See [CODE_OF_CONDUCT.md](.github/CODE_OF_CONDUCT.md).

## Questions?

Open an issue with the Question template.
