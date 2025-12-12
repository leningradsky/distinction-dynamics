{-# OPTIONS --no-positivity-check --type-in-type #-}

module DDWithStdlib where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Function using (_∘_) renaming (id to idfun)
open import Relation.Nullary using (¬_; Dec; yes; no)

-- ============================================
-- PART 1: Reflexive universe
-- ============================================

mutual
  data U : Set where
    UNIT EMPTY UNIV NAT BOOL : U
    PI SIGMA : (a : U) → (El a → U) → U

  El : U → Set
  El UNIT = ⊤
  El EMPTY = ⊥
  El UNIV = U
  El NAT = ℕ
  El BOOL = Bool
  El (PI a b) = (x : El a) → El (b x)
  El (SIGMA a b) = Σ (El a) λ x → El (b x)

-- ============================================
-- PART 2: Three distinct codes
-- ============================================

UNIT≢EMPTY : UNIT ≡ EMPTY → ⊥
UNIT≢EMPTY ()

UNIT≢UNIV : UNIT ≡ UNIV → ⊥
UNIT≢UNIV ()

EMPTY≢UNIV : EMPTY ≡ UNIV → ⊥
EMPTY≢UNIV ()

-- ============================================
-- PART 3: Triad
-- ============================================

data Three : Set where A B C : Three

Three-eq : (x y : Three) → Dec (x ≡ y)
Three-eq A A = yes refl
Three-eq A B = no (λ ())
Three-eq A C = no (λ ())
Three-eq B A = no (λ ())
Three-eq B B = yes refl
Three-eq B C = no (λ ())
Three-eq C A = no (λ ())
Three-eq C B = no (λ ())
Three-eq C C = yes refl

record Triad : Set where
  field
    obj : Three → U
    AB : obj A ≡ obj B → ⊥
    BC : obj B ≡ obj C → ⊥
    CA : obj C ≡ obj A → ⊥

canonicalTriad : Triad
canonicalTriad = record
  { obj = λ { A → UNIT ; B → EMPTY ; C → UNIV }
  ; AB = UNIT≢EMPTY
  ; BC = EMPTY≢UNIV
  ; CA = λ p → UNIT≢UNIV (sym p)
  }

-- ============================================
-- PART 4: Category D
-- ============================================

record Category : Set₁ where
  field
    Obj : Set
    Hom : Obj → Obj → Set
    identity : ∀ {a} → Hom a a
    _∘c_ : ∀ {a b c} → Hom b c → Hom a b → Hom a c
    id-left : ∀ {a b} (f : Hom a b) → identity ∘c f ≡ f
    id-right : ∀ {a b} (f : Hom a b) → f ∘c identity ≡ f
    assoc : ∀ {a b c d} (f : Hom c d) (g : Hom b c) (h : Hom a b)
          → (f ∘c g) ∘c h ≡ f ∘c (g ∘c h)

D : Category
D = record
  { Obj = U
  ; Hom = λ a b → El a → El b
  ; identity = idfun
  ; _∘c_ = λ g f x → g (f x)
  ; id-left = λ f → refl
  ; id-right = λ f → refl
  ; assoc = λ f g h → refl
  }

-- ============================================
-- PART 5: Contravariant functor
-- ============================================

ConsciousnessF₀ : U → U
ConsciousnessF₀ a = PI a (λ _ → UNIV)

ConsciousnessF₁ : ∀ {a b} → (El a → El b) → (El (ConsciousnessF₀ b) → El (ConsciousnessF₀ a))
ConsciousnessF₁ f g = g ∘ f

Consciousness-id : ∀ {a} (g : El (ConsciousnessF₀ a)) → ConsciousnessF₁ idfun g ≡ g
Consciousness-id g = refl

Consciousness-∘ : ∀ {a b c} (f : El a → El b) (h : El b → El c) (g : El (ConsciousnessF₀ c))
                → ConsciousnessF₁ (h ∘ f) g ≡ ConsciousnessF₁ f (ConsciousnessF₁ h g)
Consciousness-∘ f h g = refl

-- ============================================
-- PART 6: Group S₃
-- ============================================

data Perm3 : Set where
  e r r² s₁ s₂ s₃ : Perm3

apply : Perm3 → Three → Three
apply e x = x
apply r A = B
apply r B = C
apply r C = A
apply r² A = C
apply r² B = A
apply r² C = B
apply s₁ A = B
apply s₁ B = A
apply s₁ C = C
apply s₂ A = A
apply s₂ B = C
apply s₂ C = B
apply s₃ A = C
apply s₃ B = B
apply s₃ C = A

_·_ : Perm3 → Perm3 → Perm3
e · q = q
r · e = r
r · r = r²
r · r² = e
r · s₁ = s₃
r · s₂ = s₁
r · s₃ = s₂
r² · e = r²
r² · r = e
r² · r² = r
r² · s₁ = s₂
r² · s₂ = s₃
r² · s₃ = s₁
s₁ · e = s₁
s₁ · r = s₂
s₁ · r² = s₃
s₁ · s₁ = e
s₁ · s₂ = r
s₁ · s₃ = r²
s₂ · e = s₂
s₂ · r = s₃
s₂ · r² = s₁
s₂ · s₁ = r²
s₂ · s₂ = e
s₂ · s₃ = r
s₃ · e = s₃
s₃ · r = s₁
s₃ · r² = s₂
s₃ · s₁ = r
s₃ · s₂ = r²
s₃ · s₃ = e

inv : Perm3 → Perm3
inv e = e
inv r = r²
inv r² = r
inv s₁ = s₁
inv s₂ = s₂
inv s₃ = s₃

e-left : ∀ p → e · p ≡ p
e-left _ = refl

e-right : ∀ p → p · e ≡ p
e-right e = refl
e-right r = refl
e-right r² = refl
e-right s₁ = refl
e-right s₂ = refl
e-right s₃ = refl

inv-left : ∀ p → inv p · p ≡ e
inv-left e = refl
inv-left r = refl
inv-left r² = refl
inv-left s₁ = refl
inv-left s₂ = refl
inv-left s₃ = refl

inv-right : ∀ p → p · inv p ≡ e
inv-right e = refl
inv-right r = refl
inv-right r² = refl
inv-right s₁ = refl
inv-right s₂ = refl
inv-right s₃ = refl

r³≡e : (r · r) · r ≡ e
r³≡e = refl

s₁²≡e : s₁ · s₁ ≡ e
s₁²≡e = refl

-- ============================================
-- PART 7: apply is a homomorphism
-- ============================================

-- apply (p · q) x ≡ apply p (apply q x)
apply-homo : ∀ p q x → apply (p · q) x ≡ apply p (apply q x)
apply-homo e q x = refl
apply-homo r e x = refl
apply-homo r r A = refl
apply-homo r r B = refl
apply-homo r r C = refl
apply-homo r r² A = refl
apply-homo r r² B = refl
apply-homo r r² C = refl
apply-homo r s₁ A = refl
apply-homo r s₁ B = refl
apply-homo r s₁ C = refl
apply-homo r s₂ A = refl
apply-homo r s₂ B = refl
apply-homo r s₂ C = refl
apply-homo r s₃ A = refl
apply-homo r s₃ B = refl
apply-homo r s₃ C = refl
apply-homo r² e x = refl
apply-homo r² r A = refl
apply-homo r² r B = refl
apply-homo r² r C = refl
apply-homo r² r² A = refl
apply-homo r² r² B = refl
apply-homo r² r² C = refl
apply-homo r² s₁ A = refl
apply-homo r² s₁ B = refl
apply-homo r² s₁ C = refl
apply-homo r² s₂ A = refl
apply-homo r² s₂ B = refl
apply-homo r² s₂ C = refl
apply-homo r² s₃ A = refl
apply-homo r² s₃ B = refl
apply-homo r² s₃ C = refl
apply-homo s₁ e x = refl
apply-homo s₁ r A = refl
apply-homo s₁ r B = refl
apply-homo s₁ r C = refl
apply-homo s₁ r² A = refl
apply-homo s₁ r² B = refl
apply-homo s₁ r² C = refl
apply-homo s₁ s₁ A = refl
apply-homo s₁ s₁ B = refl
apply-homo s₁ s₁ C = refl
apply-homo s₁ s₂ A = refl
apply-homo s₁ s₂ B = refl
apply-homo s₁ s₂ C = refl
apply-homo s₁ s₃ A = refl
apply-homo s₁ s₃ B = refl
apply-homo s₁ s₃ C = refl
apply-homo s₂ e x = refl
apply-homo s₂ r A = refl
apply-homo s₂ r B = refl
apply-homo s₂ r C = refl
apply-homo s₂ r² A = refl
apply-homo s₂ r² B = refl
apply-homo s₂ r² C = refl
apply-homo s₂ s₁ A = refl
apply-homo s₂ s₁ B = refl
apply-homo s₂ s₁ C = refl
apply-homo s₂ s₂ A = refl
apply-homo s₂ s₂ B = refl
apply-homo s₂ s₂ C = refl
apply-homo s₂ s₃ A = refl
apply-homo s₂ s₃ B = refl
apply-homo s₂ s₃ C = refl
apply-homo s₃ e x = refl
apply-homo s₃ r A = refl
apply-homo s₃ r B = refl
apply-homo s₃ r C = refl
apply-homo s₃ r² A = refl
apply-homo s₃ r² B = refl
apply-homo s₃ r² C = refl
apply-homo s₃ s₁ A = refl
apply-homo s₃ s₁ B = refl
apply-homo s₃ s₁ C = refl
apply-homo s₃ s₂ A = refl
apply-homo s₃ s₂ B = refl
apply-homo s₃ s₂ C = refl
apply-homo s₃ s₃ A = refl
apply-homo s₃ s₃ B = refl
apply-homo s₃ s₃ C = refl

-- apply e = id
apply-e : ∀ x → apply e x ≡ x
apply-e x = refl

-- ============================================
-- PART 8: Fibonacci
-- ============================================

fib : ℕ → ℕ
fib zero = zero
fib (suc zero) = suc zero
fib (suc (suc n)) = fib (suc n) + fib n

fib0 : fib 0 ≡ 0
fib0 = refl

fib1 : fib 1 ≡ 1
fib1 = refl

fib5 : fib 5 ≡ 5
fib5 = refl

fib10 : fib 10 ≡ 55
fib10 = refl

-- ============================================
-- PART 9: Metric on Three
-- ============================================

dist3 : Three → Three → ℕ
dist3 A A = 0
dist3 B B = 0
dist3 C C = 0
dist3 _ _ = 1

dist3-refl : ∀ x → dist3 x x ≡ 0
dist3-refl A = refl
dist3-refl B = refl
dist3-refl C = refl

dist3-sym : ∀ x y → dist3 x y ≡ dist3 y x
dist3-sym A A = refl
dist3-sym A B = refl
dist3-sym A C = refl
dist3-sym B A = refl
dist3-sym B B = refl
dist3-sym B C = refl
dist3-sym C A = refl
dist3-sym C B = refl
dist3-sym C C = refl

dist3-triangle : ∀ x y z → dist3 x z ≤ dist3 x y + dist3 y z
dist3-triangle A A A = z≤n
dist3-triangle A A B = s≤s z≤n
dist3-triangle A A C = s≤s z≤n
dist3-triangle A B A = z≤n
dist3-triangle A B B = s≤s z≤n
dist3-triangle A B C = s≤s z≤n
dist3-triangle A C A = z≤n
dist3-triangle A C B = s≤s z≤n
dist3-triangle A C C = s≤s z≤n
dist3-triangle B A A = s≤s z≤n
dist3-triangle B A B = z≤n
dist3-triangle B A C = s≤s z≤n
dist3-triangle B B A = s≤s z≤n
dist3-triangle B B B = z≤n
dist3-triangle B B C = s≤s z≤n
dist3-triangle B C A = s≤s z≤n
dist3-triangle B C B = z≤n
dist3-triangle B C C = s≤s z≤n
dist3-triangle C A A = s≤s z≤n
dist3-triangle C A B = s≤s z≤n
dist3-triangle C A C = z≤n
dist3-triangle C B A = s≤s z≤n
dist3-triangle C B B = s≤s z≤n
dist3-triangle C B C = z≤n
dist3-triangle C C A = s≤s z≤n
dist3-triangle C C B = s≤s z≤n
dist3-triangle C C C = z≤n

-- ============================================
-- PART 10: S₃ are isometries
-- ============================================

isometry : ∀ p x y → dist3 (apply p x) (apply p y) ≡ dist3 x y
isometry e x y = refl
isometry r A A = refl
isometry r A B = refl
isometry r A C = refl
isometry r B A = refl
isometry r B B = refl
isometry r B C = refl
isometry r C A = refl
isometry r C B = refl
isometry r C C = refl
isometry r² A A = refl
isometry r² A B = refl
isometry r² A C = refl
isometry r² B A = refl
isometry r² B B = refl
isometry r² B C = refl
isometry r² C A = refl
isometry r² C B = refl
isometry r² C C = refl
isometry s₁ A A = refl
isometry s₁ A B = refl
isometry s₁ A C = refl
isometry s₁ B A = refl
isometry s₁ B B = refl
isometry s₁ B C = refl
isometry s₁ C A = refl
isometry s₁ C B = refl
isometry s₁ C C = refl
isometry s₂ A A = refl
isometry s₂ A B = refl
isometry s₂ A C = refl
isometry s₂ B A = refl
isometry s₂ B B = refl
isometry s₂ B C = refl
isometry s₂ C A = refl
isometry s₂ C B = refl
isometry s₂ C C = refl
isometry s₃ A A = refl
isometry s₃ A B = refl
isometry s₃ A C = refl
isometry s₃ B A = refl
isometry s₃ B B = refl
isometry s₃ B C = refl
isometry s₃ C A = refl
isometry s₃ C B = refl
isometry s₃ C C = refl

-- ============================================
-- PART 11: Self-similarity
-- ============================================

univ-in-univ : El UNIV
univ-in-univ = UNIV

self-application : El UNIV ≡ U
self-application = refl

-- Code containing itself
self-code : Σ U (λ c → El c ≡ U)
self-code = UNIV , refl

-- ============================================
-- PART 12: Triad morphisms
-- ============================================

record TriadMorphism (T₁ T₂ : Triad) : Set where
  field
    map : Three → Three
    preserve : ∀ x y → Triad.obj T₁ x ≡ Triad.obj T₁ y → Triad.obj T₂ (map x) ≡ Triad.obj T₂ (map y)

id-triad : ∀ T → TriadMorphism T T
id-triad T = record
  { map = idfun
  ; preserve = λ x y p → p
  }

-- ============================================
-- PART 13: Orbits and stabilizers
-- ============================================

-- Stabilizer of point x: permutations that fix x
Stab : Three → Perm3 → Set
Stab x p = apply p x ≡ x

-- e stabilizes everything
stab-e : ∀ x → Stab x e
stab-e x = refl

-- s₁ stabilizes C
stab-s₁-C : Stab C s₁
stab-s₁-C = refl

-- s₂ stabilizes A
stab-s₂-A : Stab A s₂
stab-s₂-A = refl

-- s₃ stabilizes B
stab-s₃-B : Stab B s₃
stab-s₃-B = refl

-- Orbit: all points reachable from x
-- S₃ acts transitively on Three: any point can reach any other
orbit-AB : apply r A ≡ B
orbit-AB = refl

orbit-AC : apply r² A ≡ C
orbit-AC = refl

orbit-BA : apply r² B ≡ A
orbit-BA = refl

orbit-BC : apply r B ≡ C
orbit-BC = refl

orbit-CA : apply r C ≡ A
orbit-CA = refl

orbit-CB : apply r² C ≡ B
orbit-CB = refl

-- ============================================
-- RESULT: 13 PARTS
-- ============================================
