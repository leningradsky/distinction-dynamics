# Definitions

- DEF Σ (alphabet): a non-empty finite set of primitive marks.
- DEF Σ+ (non-empty words): the set of finite words over Σ of length >= 1.
- DEF Distinction: an element of Σ.
- DEF Configuration: an element of Σ+.

- DEF A (admissibility): a subset `A` of `Σ+` such that:
  - DEF (A1) `A` is non-empty.
  - DEF (A2) Prefix-closure: if `w` is in `A` and `u` is a non-empty prefix of `w`, then `u` is in `A`.
  - DEF (A3) Decidability: membership `w` in `A` is decidable for each `w` in `Σ+`.

- DEF `<=` (extension order): for `u, v` in `A`, define `u <= v` iff `u` is a prefix of `v`.

- DEF C (category of admissible extensions): objects are elements of `A`; there is a unique morphism `u -> v` iff `u <= v`; identities are the reflexive morphisms; composition is inherited from transitivity of `<=`.

- DEF Φ (criticality functional): path entropy of the distinction structure.
  - DEF Let P_S(n) := number of distinguishable compositions of length n in structure S.
  - DEF Φ(S) := lim sup_{n→∞} (1/n) log P_S(n)
  - FORCED Φ is the unique functional satisfying invariance, monotonicity, boundary sensitivity, locality, and dimensionlessness (see `0_CORE/UAC.md` for proof).
  - DEF (UAC): S is admissible iff 0 < Φ(S) < ∞.
