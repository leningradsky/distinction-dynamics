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

- DEF Φ (criticality functional): a function symbol reserved for later bridges (e.g. `Φ : A -> R`); it is not used in `1_DERIVATION`.
