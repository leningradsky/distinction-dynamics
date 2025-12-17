{-# OPTIONS --safe --without-K #-}

-- DD Level 1: Distinction (T0-T3) — Minimal Working Version

module L01-Distinction where

-- Empty type (T0: Ø impossible)
data ⊥ : Set where

-- Unit
data ⊤ : Set where
  tt : ⊤

-- Negation
¬_ : Set → Set
¬ A = A → ⊥

-- Equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

-- T0: No proof of ⊥
T0 : ¬ ⊥
T0 ()

-- T1: Distinction exists (Bool)
data Bool : Set where
  true false : Bool

true≢false : ¬ (true ≡ false)
true≢false ()

T1 : Bool
T1 = true  -- witness

-- T2: Binary structure
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

T2 : ∀ b → (b ≡ true) ⊎ (b ≡ false)
T2 true = inl refl
T2 false = inr refl

-- T3: Self-reference (codes are distinguishable)
data U : Set where
  BOOL : U
  UNIT : U

BOOL≢UNIT : ¬ (BOOL ≡ UNIT)
BOOL≢UNIT ()

T3 : U  -- U contains multiple codes
T3 = BOOL

-- Done
L01-done : ⊤
L01-done = tt
