{-# OPTIONS --safe --without-K #-}

-- DD Level 2: Iteration (T4) — ℕ and irreversibility

module L02-Iteration where

open import L01-Distinction

-- Natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- Monoid laws
+-identity-l : ∀ n → zero + n ≡ n
+-identity-l n = refl

+-identity-r : ∀ n → n + zero ≡ n
+-identity-r zero = refl
+-identity-r (suc n) = cong suc (+-identity-r n)
  where
  cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

-- T4: Irreversibility — suc n ≢ n
suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

T4 : ∀ n → ¬ (suc n ≡ n)
T4 zero ()
T4 (suc n) eq = T4 n (suc-injective eq)

-- No maximum
no-max : ∀ n → ¬ (suc n ≡ n)
no-max = T4

-- Done
L02-done : ⊤
L02-done = tt
