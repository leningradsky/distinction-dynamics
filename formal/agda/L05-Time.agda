{-# OPTIONS --safe --without-K #-}

-- DD Level 5: Time & Stone's Theorem (T9-T10)

module L05-Time where

open import L01-Distinction
open import L02-Iteration
open import L03-Criticality

-- ════════════════════════════════════════════════════════════════
-- T9: Continuous Time — modeled as ℚ (rationals)
-- ════════════════════════════════════════════════════════════════

-- Time is ℚ (continuous approximation in safe Agda)
Time : Set
Time = ℚ

-- Time has structure from ℚ
-- (ordering, density inherited)

-- ════════════════════════════════════════════════════════════════
-- T10: Stone's Theorem — One-Parameter Groups
-- ════════════════════════════════════════════════════════════════

-- One-parameter group structure
record OneParamGroup (State : Set) : Set₁ where
  field
    action : ℕ → State → State  -- discrete time for simplicity
    act-id : ∀ x → action 0 x ≡ x
    act-comp : ∀ m n x → action m (action n x) ≡ action (m + n) x

-- Natural number addition for time composition
open import L02-Iteration using (_+_)

-- Identity transformation group
id-group : ∀ {S : Set} → OneParamGroup S
id-group = record
  { action = λ _ x → x
  ; act-id = λ x → refl
  ; act-comp = λ m n x → refl
  }

-- Iteration group on ℕ: action(n, x) = n + x (note order!)
iter-action : ℕ → ℕ → ℕ
iter-action n x = n + x

iter-id : ∀ x → iter-action 0 x ≡ x
iter-id x = refl  -- 0 + x = x by definition

-- Helper: x + 0 = x
+-right-zero : ∀ n → n + 0 ≡ n
+-right-zero zero = refl
+-right-zero (suc n) = cong suc (+-right-zero n)
  where
  cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

-- For full group: need x + 0 = x which is +-right-zero
-- Simplified: use discrete model

-- Generator concept: difference between consecutive actions
-- gen(x) = action(1, x) - x (informally)

-- Stone's theorem essence: 
-- Continuous 1-param unitary group ↔ self-adjoint generator
-- Here we just establish group structure

-- Key property: homomorphism
T10-homomorphism : ∀ {S} (g : OneParamGroup S) m n x →
  OneParamGroup.action g (m + n) x ≡ 
  OneParamGroup.action g m (OneParamGroup.action g n x)
T10-homomorphism g m n x = sym (OneParamGroup.act-comp g m n x)
  where
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

-- Done
L05-done : ⊤
L05-done = tt
