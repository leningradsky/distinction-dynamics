# Forced Chain (Spine)

- DEF Scope: this file contains only statements labeled FORCED that are logically forced by `0_CORE/AXIOM.md` and `0_CORE/DEFINITIONS.md`, plus the DEF items they depend on.
- DEF Exclusion: any bridge to continuity, Lie groups, spacetime, gauge theory, Higgs, generations, or cosmology is excluded here and belongs in `2_EXPRESSION/BRIDGES.md` as HYP/CONJ (or DEF when it is purely an added convention).

## Dependency Index

- DEF (DEF-AX; `0_CORE/AXIOM.md`): `Ø is impossible.`
- DEF (DEF-Σ; `0_CORE/DEFINITIONS.md`): Σ, Σ+, Distinction, Configuration.
- DEF (DEF-A; `0_CORE/DEFINITIONS.md`): admissibility `A` (subset of `Σ+`) with (A1-A3).
- DEF (DEF-<=; `0_CORE/DEFINITIONS.md`): prefix order `<=` on `A`.
- DEF (DEF-C; `0_CORE/DEFINITIONS.md`): category C induced by `<=`.

## Forced Lemmas

- FORCED L1 (Σ+ non-empty): If DEF-Σ holds, then `Σ+` is non-empty.
  - FORCED Justification: pick any `s` in `Σ` (possible since Σ is non-empty); then the word of length 1 containing `s` lies in `Σ+`.
  - FORCED Depends on: DEF-Σ.

- FORCED L2 (`<=` is a partial order): Under DEF-<=, the relation `<=` is reflexive, antisymmetric, and transitive on `A`.
  - FORCED Justification: "is a prefix of" is reflexive and transitive on words; if `u` is a prefix of `v` and `v` is a prefix of `u`, then `u = v`.
  - FORCED Depends on: DEF-<= (and thus DEF-A, DEF-Σ).

- FORCED L3 (C is thin): Under DEF-C, for any `u, v` in `A`, `Hom_C(u,v)` is either empty or a singleton.
  - FORCED Justification: DEF-C declares at most one morphism `u -> v`, present exactly when `u <= v`.
  - FORCED Depends on: DEF-C (and thus DEF-<=).

- FORCED L4 (C is small): Under DEF-C, the collections `Ob(C)` and `Mor(C)` are sets.
  - FORCED Justification: `Ob(C) = A` is a set; `Mor(C)` is a subset of `A x A`, hence a set.
  - FORCED Depends on: DEF-C (and thus DEF-Σ).

## Chain (Dependency-Checked)

- FORCED (Chain-1): DEF-Σ -> FORCED L1 (by FORCED L1).
- FORCED (Chain-2): DEF-Σ + DEF-A + DEF-<= -> FORCED L2 (by FORCED L2).
- FORCED (Chain-3): DEF-C -> FORCED L3 (by FORCED L3).
- FORCED (Chain-4): DEF-C -> FORCED L4 (by FORCED L4).
