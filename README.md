# Distinction Dynamics (Repository Spine)

- DEF Scope: this repository is organized into a minimal formal spine plus optional bridges to continuous mathematics and physics.
- DEF Label discipline: every claim is tagged as one of `FORCED`, `DEF`, `HYP`, `CONJ`.
  - DEF `FORCED` = logically forced by prior definitions/lemmas.
  - DEF `DEF` = explicit convention/definition (added structure).
  - DEF `HYP` = bridge that uses empirical physics or an extra identification not forced by the spine.
  - DEF `CONJ` = proposed claim not presently proved in the spine.

## Repository Layers

- DEF `0_CORE/`: primitive prohibition and minimal formal primitives.
  - DEF `0_CORE/AXIOM.md`: the primitive prohibition `Ø is impossible.`
  - DEF `0_CORE/DEFINITIONS.md`: Σ, Σ+, admissibility `A`, prefix order `<=`, category `C`, reserved `Φ`.
- DEF `1_DERIVATION/`: the dependency-checked forced chain.
  - DEF `1_DERIVATION/FORCED_CHAIN.md`: FORCED consequences of the CORE definitions, with explicit dependencies.
- DEF `2_EXPRESSION/`: all non-forced bridges (discrete→continuous; math→physics).
  - DEF `2_EXPRESSION/BRIDGES.md`: explicit bridge mechanisms and physics identifications (tagged HYP/CONJ).

## What Is FORCED Today

- FORCED The current forced content is exactly the FORCED items in `1_DERIVATION/FORCED_CHAIN.md`.
- FORCED No claim about continuity, Lie groups, spacetime, gauge groups, Higgs, generations, cosmology, or numerical constants is FORCED by the current spine.

## What Is DEF Today

- DEF The modeling primitives in `0_CORE/DEFINITIONS.md` (Σ, Σ⁺, `A`, `≼`, `C`, reserved `Φ`) are conventions for building a minimal formal environment compatible with the prohibition in `0_CORE/AXIOM.md`.
- DEF Any use of continuity / Lie groups requires an explicit bridge mechanism; the spine does not assume one.

## What Is HYP/CONJ Today

- HYP All discrete->continuous and math->physics identifications live in `2_EXPRESSION/BRIDGES.md`.
- DEF The repository contains additional exploratory artifacts (LaTeX chapters, Python scripts, Agda, Lean, Coq) that may state stronger claims; they are not imported into the FORCED spine unless re-stated with explicit dependencies and proofs.

## Open (Spine-Blocking) Items

- DEF Specify a concrete `Φ` and a selection rule (or remove `Φ` until needed) without importing physics.
- DEF Specify a concrete bridge mechanism (e.g. `X : C -> Hilb`) and prove any promoted consequences inside `1_DERIVATION`.
- DEF Audit existing non-spine artifacts for hidden assumptions and re-home claims as DEF/HYP/CONJ until they are FORCED.
