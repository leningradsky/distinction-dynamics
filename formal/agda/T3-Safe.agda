{-# OPTIONS --safe --without-K #-}

-- DD T3: Self-Reference via Universe Levels (SAFE)
-- Strategy: Use level polymorphism to express Δ = Δ(Δ)

module T3-Safe where

open import Agda.Primitive

-- Lift for universe polymorphism
record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

-- ════════════════════════════════════════════════════════════════
-- Basic types
-- ════════════════════════════════════════════════════════════════

data ⊥ : Set where
data ⊤ : Set where tt : ⊤

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

-- ════════════════════════════════════════════════════════════════
-- Universe at each level
-- ════════════════════════════════════════════════════════════════

-- U₀ : Set₀ codes for Set₀ types
data U₀ : Set where
  BOOL₀ : U₀
  NAT₀  : U₀
  UNIT₀ : U₀

data Bool : Set where true false : Bool
data ℕ : Set where zero : ℕ; suc : ℕ → ℕ

El₀ : U₀ → Set
El₀ BOOL₀ = Bool
El₀ NAT₀  = ℕ
El₀ UNIT₀ = ⊤

-- U₁ : Set₁ codes for Set₀ AND Set₁ types
mutual
  data U₁ : Set₁ where
    LIFT₀ : U₀ → U₁        -- Lift codes from U₀
    SET₀  : U₁             -- Code for Set itself!
    PI₁   : (a : U₁) → (El₁ a → U₁) → U₁

  El₁ : U₁ → Set₁
  El₁ (LIFT₀ u) = Lift (lsuc lzero) (El₀ u)
  El₁ SET₀ = Set           -- El₁ SET₀ = Set₀ !!!
  El₁ (PI₁ a b) = (x : El₁ a) → El₁ (b x)

-- ════════════════════════════════════════════════════════════════
-- T3: SELF-REFERENCE AT LEVEL 1
-- ════════════════════════════════════════════════════════════════

-- U₁ contains a code SET₀ such that El₁ SET₀ = Set
-- This is Δ₁(Set₀) = Set₀ — partial self-reference!

T3-partial : El₁ SET₀ ≡ Set
T3-partial = refl

-- ════════════════════════════════════════════════════════════════
-- Going further: U₂ can reference U₁
-- ════════════════════════════════════════════════════════════════

mutual
  data U₂ : Set₂ where
    LIFT₁ : U₁ → U₂
    SET₁  : U₂             -- Code for Set₁!
    U₁-CODE : U₂           -- Code for U₁ itself!

  El₂ : U₂ → Set₂
  El₂ (LIFT₁ u) = Lift (lsuc (lsuc lzero)) (El₁ u)
  El₂ SET₁ = Set₁
  El₂ U₁-CODE = Lift (lsuc (lsuc lzero)) U₁

-- U₂ contains code for U₁!
T3-meta : El₂ U₁-CODE ≡ Lift (lsuc (lsuc lzero)) U₁
T3-meta = refl

-- ════════════════════════════════════════════════════════════════
-- The Pattern: Δₙ₊₁ can reference Δₙ
-- ════════════════════════════════════════════════════════════════

{-
  Δ = Δ(Δ) is approximated by:
  
  At level n+1, we have a code for level n universe.
  
  Uₙ₊₁ contains code Cₙ such that Elₙ₊₁(Cₙ) = Uₙ
  
  This is "Δₙ₊₁ distinguishes Δₙ" — a stratified version.
  
  Full Δ = Δ(Δ) would require:
    ∃ c : U . El c = U
  
  Which is only expressible with type-in-type.
  
  BUT: The stratified version captures the STRUCTURE of self-reference
  without the logical inconsistency.
-}

-- ════════════════════════════════════════════════════════════════
-- Alternative: Codes are first-class in same universe
-- ════════════════════════════════════════════════════════════════

-- A universe where codes can be compared, manipulated
record SelfRefUniverse : Set₁ where
  field
    Code : Set
    Interp : Code → Set
    -- Reflexivity: Code itself is a Set
    code-is-set : Set  -- trivially true
    -- Key: functions on codes
    transform : Code → Code

-- Instantiate with U₀
U₀-SRU : SelfRefUniverse
U₀-SRU = record
  { Code = U₀
  ; Interp = El₀
  ; code-is-set = U₀
  ; transform = λ x → x  -- identity
  }

-- The codes ARE in Set, and we can reason about them
-- This captures: "distinctions are themselves distinguishable"

-- ════════════════════════════════════════════════════════════════
-- STRONGEST SAFE VERSION: Inductive-Recursive Universe
-- ════════════════════════════════════════════════════════════════

-- This requires --safe but allows powerful encoding

mutual
  data USafe : Set where
    `Bool : USafe
    `Nat  : USafe
    `Π    : (A : USafe) → (ElSafe A → USafe) → USafe

  ElSafe : USafe → Set
  ElSafe `Bool = Bool
  ElSafe `Nat = ℕ
  ElSafe (`Π A B) = (x : ElSafe A) → ElSafe (B x)

-- This compiles with --safe!
-- It's a Tarski-style universe.

-- Self-reference here: USafe : Set, and USafe is inductive
-- The TYPE of codes (USafe) is itself a type we can reason about

-- Codes for codes: if we had `U : USafe, ElSafe `U = USafe, that would be
-- true self-reference. But that's not possible in --safe.

-- What IS possible: reasoning about USafe AS A SET

USafe-is-Set : Set
USafe-is-Set = USafe

-- And we can define functions USafe → USafe
dup : USafe → USafe
dup A = `Π A (λ _ → A)

-- ════════════════════════════════════════════════════════════════
-- SUMMARY
-- ════════════════════════════════════════════════════════════════

{-
THREE LEVELS OF SELF-REFERENCE:

1. WEAK (--safe): USafe : Set, we reason about codes as data
   - Captures: "codes are objects in our universe"
   - Missing: El code = Universe

2. STRATIFIED (--safe): U₁ has code SET₀ with El₁ SET₀ = Set
   - Captures: "higher universe knows lower universe"
   - Missing: Same-level self-reference

3. FULL (--type-in-type): U has UNIV with El UNIV = U
   - Captures: Δ = Δ(Δ) exactly
   - Cost: Logical inconsistency

DD INTERPRETATION:
- The stratified version shows the PATTERN exists
- Each level can reference the previous
- The "limit" of this tower IS Δ = Δ(Δ)
- Full expression requires impredicativity (type-in-type)
-}

T3-safe-complete : ⊤
T3-safe-complete = tt
