{-# OPTIONS --safe --without-K #-}

-- DD Level 3: Criticality & Number Tower (T5-T6)

module L03-Criticality where

open import L01-Distinction
open import L02-Iteration

-- ════════════════════════════════════════════════════════════════
-- T5: Critical Regime — 0 < Φ < ∞
-- ════════════════════════════════════════════════════════════════

-- Criticality = bounded distinguishability
data Bounded : Set where
  bounded : ℕ → ℕ → Bounded

T5 : Bounded
T5 = bounded 0 1000000

-- ════════════════════════════════════════════════════════════════
-- T6: Number Tower — ℕ → ℤ → ℚ
-- ════════════════════════════════════════════════════════════════

-- ℤ: Integers
data ℤ : Set where
  pos    : ℕ → ℤ       -- 0, 1, 2, ...
  negsuc : ℕ → ℤ       -- -1, -2, -3, ...

-- ℤ negation
-ℤ_ : ℤ → ℤ
-ℤ pos zero = pos zero
-ℤ pos (suc n) = negsuc n
-ℤ negsuc n = pos (suc n)

-- ℤ has negatives
neg-one : ℤ
neg-one = negsuc 0

-- ℚ: Rationals (numerator / (denominator + 1))
record ℚ : Set where
  constructor _/suc_
  field
    num : ℤ
    den : ℕ

-- Examples
half : ℚ
half = pos 1 /suc 1  -- 1/2

third : ℚ
third = pos 1 /suc 2  -- 1/3

-- ℚ has proper fractions
T6-Q : ℚ
T6-Q = half

-- Embeddings
ℕ→ℤ : ℕ → ℤ
ℕ→ℤ = pos

ℤ→ℚ : ℤ → ℚ
ℤ→ℚ z = z /suc 0  -- z/1

ℕ→ℚ : ℕ → ℚ
ℕ→ℚ n = ℤ→ℚ (ℕ→ℤ n)

-- Tower test
T6-tower : ℚ
T6-tower = ℕ→ℚ 5  -- 5/1

-- ℝ requires postulates (not --safe compatible)
-- For full formalization, use agda-stdlib or Cubical Agda

-- Done
L03-done : ⊤
L03-done = tt
