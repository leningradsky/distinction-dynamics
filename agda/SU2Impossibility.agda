{-# OPTIONS --safe --without-K #-}

{-
  S₃ ⊄ SU(2): FORMAL PROOF
  =========================

  Strategy: count elements of order 2

  Key theorem: SU(2) has exactly ONE element of order 2 (namely -I)
  But S₃ has THREE elements of order 2 (s₁, s₂, s₃)
  Injective homomorphism preserves order
  Therefore no injective φ: S₃ → SU(2) exists

  This proof does NOT require full ADE classification!
-}

module SU2Impossibility where

------------------------------------------------------------------------
-- Basic definitions
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

------------------------------------------------------------------------
-- S₃: symmetric group on 3 elements
------------------------------------------------------------------------

data S₃ : Set where
  e   : S₃    -- identity
  r   : S₃    -- (ABC) 3-cycle
  r²  : S₃    -- (ACB) 3-cycle
  s₁  : S₃    -- (AB) transposition
  s₂  : S₃    -- (BC) transposition
  s₃  : S₃    -- (AC) transposition

-- Group operation
_∘_ : S₃ → S₃ → S₃
e  ∘ g  = g
r  ∘ e  = r
r  ∘ r  = r²
r  ∘ r² = e
r  ∘ s₁ = s₃
r  ∘ s₂ = s₁
r  ∘ s₃ = s₂
r² ∘ e  = r²
r² ∘ r  = e
r² ∘ r² = r
r² ∘ s₁ = s₂
r² ∘ s₂ = s₃
r² ∘ s₃ = s₁
s₁ ∘ e  = s₁
s₁ ∘ r  = s₂
s₁ ∘ r² = s₃
s₁ ∘ s₁ = e
s₁ ∘ s₂ = r²
s₁ ∘ s₃ = r
s₂ ∘ e  = s₂
s₂ ∘ r  = s₃
s₂ ∘ r² = s₁
s₂ ∘ s₁ = r
s₂ ∘ s₂ = e
s₂ ∘ s₃ = r²
s₃ ∘ e  = s₃
s₃ ∘ r  = s₁
s₃ ∘ r² = s₂
s₃ ∘ s₁ = r²
s₃ ∘ s₂ = r
s₃ ∘ s₃ = e

------------------------------------------------------------------------
-- Elements of order 2 in S₃
------------------------------------------------------------------------

-- Definition: g has order 2 iff g ∘ g = e and g ≠ e
record HasOrder2 (g : S₃) : Set where
  field
    squares-to-e : g ∘ g ≡ e
    not-identity : g ≡ e → ⊥

-- s₁ has order 2
s₁-order-2 : HasOrder2 s₁
s₁-order-2 = record 
  { squares-to-e = refl 
  ; not-identity = λ () 
  }

-- s₂ has order 2
s₂-order-2 : HasOrder2 s₂
s₂-order-2 = record 
  { squares-to-e = refl 
  ; not-identity = λ () 
  }

-- s₃ has order 2
s₃-order-2 : HasOrder2 s₃
s₃-order-2 = record 
  { squares-to-e = refl 
  ; not-identity = λ () 
  }

-- These three are distinct
s₁≢s₂ : s₁ ≡ s₂ → ⊥
s₁≢s₂ ()

s₂≢s₃ : s₂ ≡ s₃ → ⊥
s₂≢s₃ ()

s₁≢s₃ : s₁ ≡ s₃ → ⊥
s₁≢s₃ ()

------------------------------------------------------------------------
-- Abstract group with exactly one element of order 2
------------------------------------------------------------------------

-- We model SU(2) abstractly by its key property:
-- it has exactly one element of order 2

record HasUniqueOrder2 (G : Set) (_·_ : G → G → G) (ε : G) : Set₁ where
  field
    -- There exists an element of order 2
    neg-one : G
    neg-one-sq : neg-one · neg-one ≡ ε
    neg-one-ne : neg-one ≡ ε → ⊥
    
    -- It is unique: any element of order 2 equals neg-one
    unique : (x : G) → x · x ≡ ε → (x ≡ ε → ⊥) → x ≡ neg-one

------------------------------------------------------------------------
-- MAIN THEOREM: No injective homomorphism S₃ → G 
-- if G has unique element of order 2
------------------------------------------------------------------------

-- Homomorphism preserves group operation
record Homomorphism (G : Set) (_·_ : G → G → G) (ε : G) : Set where
  field
    φ : S₃ → G
    preserves-op : (g h : S₃) → φ (g ∘ h) ≡ φ g · φ h
    preserves-id : φ e ≡ ε

-- Injective means different inputs give different outputs
Injective : {A B : Set} → (A → B) → Set
Injective {A} f = (x y : A) → f x ≡ f y → x ≡ y

-- Key lemma: homomorphism preserves "order 2" property
module _ {G : Set} {_·_ : G → G → G} {ε : G} 
         (H : Homomorphism G _·_ ε) where
  
  open Homomorphism H
  
  -- If g² = e in S₃, then φ(g)² = ε in G
  preserves-square : (g : S₃) → g ∘ g ≡ e → φ g · φ g ≡ ε
  preserves-square g p = trans (sym (preserves-op g g)) 
                               (trans (cong φ p) preserves-id)

------------------------------------------------------------------------
-- THE IMPOSSIBILITY THEOREM
------------------------------------------------------------------------

-- If G has unique order-2 element, no injective hom S₃ → G exists
no-injection : {G : Set} {_·_ : G → G → G} {ε : G} →
               HasUniqueOrder2 G _·_ ε →
               (H : Homomorphism G _·_ ε) →
               Injective (Homomorphism.φ H) →
               ⊥
no-injection {G} {_·_} {ε} unique-ord2 H inj = s₁≢s₂ s₁≡s₂
  where
    open Homomorphism H
    open HasUniqueOrder2 unique-ord2
    
    -- φ(s₁) has order 2 in G
    φs₁-sq : φ s₁ · φ s₁ ≡ ε
    φs₁-sq = preserves-square H s₁ refl
    
    φs₁-ne : φ s₁ ≡ ε → ⊥
    φs₁-ne p = HasOrder2.not-identity s₁-order-2 (inj s₁ e (trans p (sym preserves-id)))
    
    -- Therefore φ(s₁) = neg-one
    φs₁≡neg : φ s₁ ≡ neg-one
    φs₁≡neg = unique (φ s₁) φs₁-sq φs₁-ne
    
    -- Similarly for s₂
    φs₂-sq : φ s₂ · φ s₂ ≡ ε
    φs₂-sq = preserves-square H s₂ refl
    
    φs₂-ne : φ s₂ ≡ ε → ⊥
    φs₂-ne p = HasOrder2.not-identity s₂-order-2 (inj s₂ e (trans p (sym preserves-id)))
    
    φs₂≡neg : φ s₂ ≡ neg-one
    φs₂≡neg = unique (φ s₂) φs₂-sq φs₂-ne
    
    -- So φ(s₁) = φ(s₂)
    φs₁≡φs₂ : φ s₁ ≡ φ s₂
    φs₁≡φs₂ = trans φs₁≡neg (sym φs₂≡neg)
    
    -- By injectivity, s₁ = s₂
    s₁≡s₂ : s₁ ≡ s₂
    s₁≡s₂ = inj s₁ s₂ φs₁≡φs₂
    
    -- But s₁ ≢ s₂ — contradiction!

------------------------------------------------------------------------
-- APPLICATION TO SU(2)
------------------------------------------------------------------------

{-
  THEOREM: SU(2) has exactly one element of order 2.
  
  Proof (mathematical, external to Agda):
  
  Let A ∈ SU(2) with A² = I.
  Then eigenvalues of A satisfy λ² = 1, so λ ∈ {+1, -1}.
  Since det(A) = 1, we have λ₁ · λ₂ = 1.
  
  Case 1: λ₁ = λ₂ = 1. Then A = I (order 1, not 2).
  Case 2: λ₁ = λ₂ = -1. Then A = -I (order 2).
  Case 3: λ₁ = 1, λ₂ = -1. Then det = -1 ≠ 1. Impossible.
  
  Therefore the only element of order 2 in SU(2) is -I.
  
  This is a standard result in Lie group theory.
  We make it a MODULE PARAMETER rather than postulate.
-}

-- Parametric version: works for ANY group with this property
module SU2-Application 
  (SU2 : Set) 
  (_·SU2_ : SU2 → SU2 → SU2) 
  (I-SU2 : SU2)
  (SU2-has-unique-order2 : HasUniqueOrder2 SU2 _·SU2_ I-SU2) 
  where

  ------------------------------------------------------------------------
  -- FINAL THEOREM: S₃ does not embed into SU(2)
  ------------------------------------------------------------------------

  S₃-not-in-SU2 : (H : Homomorphism SU2 _·SU2_ I-SU2) →
                  Injective (Homomorphism.φ H) →
                  ⊥
  S₃-not-in-SU2 = no-injection SU2-has-unique-order2

------------------------------------------------------------------------
-- WHAT THIS MEANS
------------------------------------------------------------------------

{-
  We have proven (with --safe --without-K):
  
  1. S₃ has three distinct elements of order 2: s₁, s₂, s₃
     [PROVEN CONSTRUCTIVELY]
  
  2. For ANY group G with exactly one element of order 2,
     there is no injective homomorphism S₃ → G
     [PROVEN CONSTRUCTIVELY - this is the key theorem!]
  
  3. SU(2) has exactly one element of order 2
     [EXTERNAL MATHEMATICAL FACT - module parameter]
  
  4. Therefore S₃ ⊄ SU(2)
     [FOLLOWS FROM 2 + 3]
  
  The structure:
  - Main theorem (no-injection) is FULLY PROVEN in Agda
  - Application to SU(2) requires ONE external fact
  - That fact is standard linear algebra (eigenvalue argument)
  
  This is much cleaner than the ADE classification approach!
-}

------------------------------------------------------------------------
-- COMPARISON WITH PREVIOUS APPROACH
------------------------------------------------------------------------

{-
  OLD (in SU3Proven.agda):
    - Listed finite subgroups of SU(2) as data type
    - Said "S₃ not in list"
    - But list completeness was not proven!
    - IMPLICIT assumptions everywhere
  
  NEW (this file):
    - Single property: unique order-2 element
    - This property is SUFFICIENT to exclude S₃
    - Proof is FULLY CONSTRUCTIVE given the property
    - External dependency is EXPLICIT (module parameter)
    
  The improvement: we reduced the external dependency from
  "full ADE classification" to "SU(2) has one order-2 element"
  
  To fully formalize in Agda would require:
  - Define SU(2) as 2×2 unitary matrices with det=1
  - Define eigenvalues and prove spectral theorem
  - Show det=1 constrains eigenvalue products
  - Conclude only ±I has real eigenvalues, only -I has order 2
  
  This is ~500 lines of linear algebra, but DOABLE.
-}
