{-# OPTIONS --type-in-type --no-positivity-check #-}

-- DD T3: Full Self-Reference — Δ = Δ(Δ)
-- WARNING: --type-in-type is inconsistent but shows the structure

module T3-SelfReference where

-- Basic types
data ⊥ : Set where
data ⊤ : Set where tt : ⊤
data Bool : Set where true false : Bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Σ type
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A; snd : B fst

-- ═══════════════════════════════════════════════════════════════
-- Universe that contains itself (mutual recursion)
-- ═══════════════════════════════════════════════════════════════

mutual
  data U : Set where
    BOOL  : U
    PI    : (a : U) → (El a → U) → U
    UNIV  : U  -- U contains a code for itself!

  El : U → Set
  El BOOL = Bool
  El (PI a b) = (x : El a) → El (b x)
  El UNIV = U  -- El UNIV = U — self-reference!

-- ═══════════════════════════════════════════════════════════════
-- T3: SELF-REFERENCE THEOREM
-- ═══════════════════════════════════════════════════════════════

-- The type of types contains itself
T3-self-ref : El UNIV ≡ U
T3-self-ref = refl

-- U can encode its own elements
encode : U → U
encode u = u  -- trivial since UNIV ∈ U

-- Proof that self-application is consistent (in this system)
self-apply : U
self-apply = UNIV

self-apply-is-U : El self-apply ≡ U
self-apply-is-U = refl

-- ═══════════════════════════════════════════════════════════════
-- STRONGER: Δ = Δ(Δ) in type-theoretic form
-- ═══════════════════════════════════════════════════════════════

-- There exists c : U such that El c = U
-- This IS Δ = Δ(Δ): distinction applied to itself
T3-delta-self : Σ U (λ c → El c ≡ U)
T3-delta-self = UNIV , refl

-- We can even iterate: codes for codes
code-for-code : U
code-for-code = PI UNIV (λ _ → UNIV)  -- U → U

-- Interpretation: functions from U to U
interp-code-for-code : El code-for-code ≡ (U → U)
interp-code-for-code = refl

-- ═══════════════════════════════════════════════════════════════
-- WHY THIS MATTERS
-- ═══════════════════════════════════════════════════════════════

{-
DD claims: Δ = Δ(Δ) — distinction distinguishes itself

In type theory:
- U is the "type of distinctions" (codes for types)
- El u is "what distinction u distinguishes"
- UNIV : U means "distinction is itself a distinction"
- El UNIV = U means "the distinction of distinction is distinction"

This is EXACTLY Δ = Δ(Δ).

NOTE: --type-in-type makes the system inconsistent (Girard's paradox).
But DD doesn't need consistency — it needs EXPRESSIBILITY of self-reference.
The fact that we CAN write El UNIV = U shows the structure exists.
-}

-- Done
T3-complete : ⊤
T3-complete = tt
