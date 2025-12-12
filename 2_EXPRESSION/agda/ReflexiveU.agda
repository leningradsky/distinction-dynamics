{-# OPTIONS --guardedness --no-positivity-check #-}

module ReflexiveU where

-- ============================================
-- Reflexive universe: U with El U = U
-- ============================================

mutual
  data U : Set where
    UNIT : U
    PI : (a : U) → (El a → U) → U
    SIGMA : (a : U) → (El a → U) → U
    -- Reflexivity:
    UNIV : U

  El : U → Set
  El UNIT = UnitT where data UnitT : Set where tt : UnitT
  El (PI a b) = (x : El a) → El (b x)
  El (SIGMA a b) = SigmaT (El a) (λ x → El (b x))
    where
      data SigmaT (A : Set) (B : A → Set) : Set where
        _,_ : (fst : A) → B fst → SigmaT A B
  El UNIV = U  -- ← Key point!

-- ============================================
-- Tests
-- ============================================

-- El UNIV = U, i.e. U : Set and El UNIV : Set, and they are equal
test1 : El UNIV
test1 = UNIT  -- UNIT : U = El UNIV

test2 : El UNIV
test2 = UNIV  -- UNIV : U = El UNIV

-- We can build types "inside" U:
-- Type of functions from U to U
UtoU : U
UtoU = PI UNIV (λ _ → UNIV)

-- Its interpretation:
UtoU-type : Set
UtoU-type = El UtoU  -- = U → U

-- Example function U → U
idU : El UtoU
idU x = x

-- ============================================
-- Now: Dist as code in U
-- ============================================

-- Dist = U → U → U (relations with codes in U)
DistCode : U
DistCode = PI UNIV (λ _ → PI UNIV (λ _ → UNIV))

DistType : Set
DistType = El DistCode  -- = U → U → U

-- Example "distinction":
trivialDist : DistType
trivialDist _ _ = UNIT  -- Any two codes are "the same"

-- More interesting:
eqDist : DistType
eqDist a b = PI (PI a (λ _ → b)) (λ _ → PI (PI b (λ _ → a)) (λ _ → UNIT))
-- This encodes: (a → b) → (b → a) → Unit
-- Roughly: "a and b are isomorphic" as a condition of indistinguishability

-- ============================================
-- Self-application!
-- ============================================

-- DistCode : U, so we can apply trivialDist to DistCode
-- trivialDist : U → U → U
-- DistCode : U
-- So trivialDist DistCode DistCode : U

distDistDist : U
distDistDist = trivialDist DistCode DistCode

-- This is literally: "distinction between Dist and Dist"
-- The result is a code in U

-- ============================================
-- Deeper self-application
-- ============================================

-- Can we build d : DistType such that
-- d applied to its own code gives something meaningful?

-- Idea: d = λ a b → PI (PI a (λ _ → b)) (λ _ → PI (PI b (λ _ → a)) (λ _ → UNIT))
-- Then d DistCode DistCode = ...complex expression...

selfRefDist : U
selfRefDist = eqDist DistCode DistCode
-- This is: PI (PI DistCode (λ _ → DistCode)) (λ _ → PI (PI DistCode (λ _ → DistCode)) (λ _ → UNIT))
-- That is: (DistType → DistType) → (DistType → DistType) → Unit
-- Roughly: "if DistType is isomorphic to itself, then Unit"

-- ============================================
-- Key result
-- ============================================

-- We have:
-- 1. U : Set
-- 2. El : U → Set
-- 3. El UNIV = U
-- 4. DistCode : U with El DistCode = U → U → U
-- 5. We can apply DistCode to itself: distOfDist DistCode DistCode : U

-- This is close to Δ = Δ(Δ), but not quite an isomorphism.
-- It's more like: "Δ contains code for (Δ → Δ → Δ)"

-- ============================================
-- CONSISTENCY TEST
-- ============================================

-- Let's try to derive Empty (empty type)
-- If we succeed — the system is inconsistent

data Empty : Set where
  -- no constructors

-- Add code for Empty to an extended universe:
mutual
  data U2 : Set where
    UNIT2 : U2
    EMPTY2 : U2
    PI2 : (a : U2) → (El2 a → U2) → U2
    UNIV2 : U2

  El2 : U2 → Set
  El2 UNIT2 = Unit2 where data Unit2 : Set where tt : Unit2
  El2 EMPTY2 = Empty
  El2 (PI2 a b) = (x : El2 a) → El2 (b x)
  El2 UNIV2 = U2

-- Negation:
Not2 : U2 → U2
Not2 a = PI2 a (λ _ → EMPTY2)

-- Attempt at Russell's paradox:
-- Russell = { x | x ∉ x }
-- In types: R such that R ≅ (R → Empty)

-- Can we build this?
-- We need: code : U2 such that El2 code = (El2 code → Empty)
-- This would require: code = PI2 code (λ _ → EMPTY2)
-- But code appears in the definition of code — this is not valid recursion

-- Attempt through diagonalization:
-- diag a = PI2 a (λ f → Not2 (f f))
-- Problem: f : El2 a, but f f requires f : El2 a → U2
-- This doesn't typecheck!
-- Diagonalization is blocked by the type system

-- ============================================
-- Why this is (probably) safe
-- ============================================

-- U2 : Set — codes
-- El2 : U2 → Set — interpretation
-- El2 UNIV2 = U2 — reflexivity
--
-- Key difference from Type : Type:
-- We do NOT have Set : Set
-- We have: U2 : Set, and El2 UNIV2 = U2
-- These are different things!
--
-- The paradox requires: R : Set with R = (R → Empty)
-- We have: code : U2 with El2 code = (El2 code → Empty)
-- But El2 code : Set, while code : U2 — different levels

-- ============================================
-- Conclusion
-- ============================================

-- Built reflexive universe U with El UNIV = U
-- This allows self-application of codes
-- It's not clear whether this leads to contradiction
-- --no-positivity-check disables the check that usually prevents this
-- Deeper analysis or formal consistency proof is needed
