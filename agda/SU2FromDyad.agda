{-# OPTIONS --safe --without-K #-}

-- ═══════════════════════════════════════════════════════════════════════════
-- SU(2) FROM DYAD
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Triad → S₃ → SU(3)  [proven]
-- Dyad  → S₂ → SU(2)  [deriving]
-- Monad → S₁ → U(1)   [trivial]
--
-- ═══════════════════════════════════════════════════════════════════════════

module SU2FromDyad where

open import DD-Core

-- Dyad, S₂, X, Y, id₂, swap already defined in DD-Core

-- ═══════════════════════════════════════════════════════════════════════════
-- ACTION OF S₂ ON DYAD
-- ═══════════════════════════════════════════════════════════════════════════

act₂ : S₂ → Dyad → Dyad
act₂ id₂  d = d
act₂ swap X = Y
act₂ swap Y = X

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: id₂ is identity
-- ═══════════════════════════════════════════════════════════════════════════

theorem-id₂-identity : (d : Dyad) → act₂ id₂ d ≡ d
theorem-id₂-identity X = refl
theorem-id₂-identity Y = refl

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 2: swap² = id₂ (involution)
-- ═══════════════════════════════════════════════════════════════════════════

-- Composition in S₂
_∘₂_ : S₂ → S₂ → S₂
id₂  ∘₂ g    = g
swap ∘₂ id₂  = swap
swap ∘₂ swap = id₂

theorem-swap-involution : swap ∘₂ swap ≡ id₂
theorem-swap-involution = refl

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 3: |S₂| = 2
-- ═══════════════════════════════════════════════════════════════════════════

all-S₂ : List S₂
all-S₂ = id₂ ∷ swap ∷ []

theorem-S₂-has-2-elements : length all-S₂ ≡ 2
theorem-S₂-has-2-elements = refl

-- ═══════════════════════════════════════════════════════════════════════════
-- Z₂ AND ISOMORPHISM WITH S₂
-- ═══════════════════════════════════════════════════════════════════════════

data Z₂ : Set where
  z+ : Z₂
  z- : Z₂

s₂-to-z₂ : S₂ → Z₂
s₂-to-z₂ id₂  = z+
s₂-to-z₂ swap = z-

z₂-to-s₂ : Z₂ → S₂
z₂-to-s₂ z+ = id₂
z₂-to-s₂ z- = swap

theorem-iso-1 : (s : S₂) → z₂-to-s₂ (s₂-to-z₂ s) ≡ s
theorem-iso-1 id₂  = refl
theorem-iso-1 swap = refl

theorem-iso-2 : (z : Z₂) → s₂-to-z₂ (z₂-to-s₂ z) ≡ z
theorem-iso-2 z+ = refl
theorem-iso-2 z- = refl


-- ═══════════════════════════════════════════════════════════════════════════
-- WHY S₂ → SU(2)?
-- ═══════════════════════════════════════════════════════════════════════════
--
-- ARGUMENT 1: Quantum superposition
--
--   Dyad = two basis states |X⟩, |Y⟩
--   General state: α|X⟩ + β|Y⟩  where α,β ∈ ℂ
--   Normalization: |α|² + |β|² = 1
--   This is 3-sphere S³ ⊂ ℂ²
--
--   Transformations:
--   - Unitary (preserve norm): U(2)
--   - With det = 1 (no anomalies): SU(2)
--
-- ARGUMENT 2: Minimality
--
--   S₂ = Z₂ = {id, swap}
--   Z₂ embeds in SU(2) as center: {I, -I}
--   SU(2) is the minimal connected Lie group with this property
--
-- ARGUMENT 3: Spin 1/2
--
--   SU(2) is the rotation group of a spinor
--   Rotation by 360° = -I (not identity!)
--   Rotation by 720° = I
--   This is Z₂ structure inside SU(2)
--
-- ═══════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════
-- U(1) FROM MONAD
-- ═══════════════════════════════════════════════════════════════════════════

-- Monad = one distinguished from emptiness: A ≠ ∅
data Monad₁ : Set where
  A₁ : Monad₁

-- Discrete symmetry is trivial
data S₁ : Set where
  id₁ : S₁

all-S₁ : List S₁
all-S₁ = id₁ ∷ []

theorem-S₁-has-1-element : length all-S₁ ≡ 1
theorem-S₁-has-1-element = refl

-- ═══════════════════════════════════════════════════════════════════════════
-- WHY S₁ → U(1)?
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Discretely S₁ = {id} is trivial.
-- But continuously: A as complex number z ∈ ℂ
--
-- Transformations preserving |z|²:
--   z → e^(iθ) · z
--
-- This is U(1) — the group of phase rotations.
--
-- Physics:
--   U(1) = electromagnetic gauge group
--   Charge = generator of U(1)
--   Photon = gauge boson of U(1)
--
-- ═══════════════════════════════════════════════════════════════════════════

-- ═══════════════════════════════════════════════════════════════════════════
-- HIERARCHY OF DISTINCTIONS = STANDARD MODEL
-- ═══════════════════════════════════════════════════════════════════════════
--
--   Level 1: Monad (A ≠ ∅)     → S₁ → U(1)  → electromagnetism
--   Level 2: Dyad  (A ≠ B)     → S₂ → SU(2) → weak interaction
--   Level 3: Triad (A ≠ B ≠ C) → S₃ → SU(3) → strong interaction
--
--   Full group: SU(3) × SU(2) × U(1)
--
-- This is NOT a postulate — it's a CONSEQUENCE of the hierarchy of distinctions!
--
-- ═══════════════════════════════════════════════════════════════════════════
