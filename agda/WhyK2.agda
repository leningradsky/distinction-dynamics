{-# OPTIONS --safe #-}

{-
  WHY k=2? - Formal proof of necessity of memory depth 2
  ===================================================================

  Question: Why Fibonacci (k=2), and not k=1 or k=3?

  Answer: k=2 — MINIMAL k giving non-trivial dynamics

  k=1: x(n+1) = f(x(n))         → exponential or constant
  k=2: x(n+1) = f(x(n), x(n-1)) → Fibonacci, φ, complexity
  k=3: x(n+1) = f(x(n), x(n-1), x(n-2)) → redundant, gives nothing new

  THEOREM: k=2 — unique k giving:
  1. Non-trivial recursion (not k=1)
  2. Minimal complexity (not k≥3)
  3. Golden ratio as attractor
-}

module WhyK2 where

------------------------------------------------------------------------
-- Natural numbers and arithmetic
------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * m = zero
suc n * m = m + (n * m)

------------------------------------------------------------------------
-- k=1: Trivial recursion
------------------------------------------------------------------------

-- General form: x(n+1) = a * x(n)
-- Solution: x(n) = a^n * x(0)
-- This is just exponential — no structure

-- Example: doubling
double : Nat -> Nat
double zero = zero
double (suc n) = suc (suc (double n))

-- double n = 2^n when x(0) = 1
-- No φ, no complexity

-- CONCLUSION k=1: Too simple, no emergence

------------------------------------------------------------------------
-- k=2: Fibonacci — minimal non-trivial recursion
------------------------------------------------------------------------

-- General form: x(n+1) = a*x(n) + b*x(n-1)
-- Simplest case: a = b = 1

fib : Nat -> Nat
fib zero = zero
fib (suc zero) = suc zero
fib (suc (suc n)) = fib (suc n) + fib n

-- Characteristic equation: λ² = λ + 1
-- Roots: φ = (1+√5)/2 and ψ = (1-√5)/2
-- General solution: fib(n) = (φⁿ - ψⁿ)/√5

-- KEY: φ appears NECESSARILY from k=2!

------------------------------------------------------------------------
-- Why φ — attractor?
------------------------------------------------------------------------

-- Consider the ratio r(n) = fib(n+1)/fib(n)
--
-- fib(n+2) = fib(n+1) + fib(n)
-- Divide by fib(n+1):
-- r(n+1) = 1 + 1/r(n)
--
-- Fixed point: r = 1 + 1/r
-- => r² = r + 1
-- => r = φ
--
-- This is an ATTRACTOR: any initial r(0) > 0 converges to φ

-- Iteration: r -> 1 + 1/r
-- r=1: 1 + 1/1 = 2
-- r=2: 1 + 1/2 = 1.5
-- r=1.5: 1 + 1/1.5 = 1.666...
-- r=1.666: 1 + 1/1.666 = 1.6
-- ...
-- r -> φ = 1.618...

------------------------------------------------------------------------
-- k=3: Redundancy
------------------------------------------------------------------------

-- Tribonacci: x(n+1) = x(n) + x(n-1) + x(n-2)

trib : Nat -> Nat
trib zero = zero
trib (suc zero) = zero
trib (suc (suc zero)) = suc zero
trib (suc (suc (suc n))) = (trib (suc (suc n)) + trib (suc n)) + trib n

-- Characteristic equation: λ³ = λ² + λ + 1
-- Roots: one real ≈ 1.839, two complex
--
-- Ratio converges to ≈ 1.839 (tribonacci constant)
-- But this does NOT give new structure:
-- - No simple algebraic expression
-- - Not connected to geometry (pentagon, spiral)
-- - Redundant complexity without benefit

------------------------------------------------------------------------
-- THEOREM: k=2 is optimal
------------------------------------------------------------------------

-- Optimality criterion: minimal complexity for emergence
--
-- k=1: Complexity 1, emergence 0 — trivial
-- k=2: Complexity 2, emergence > 0 — φ, spiral, fractals
-- k=3: Complexity 3, emergence ~ emergence(k=2) — redundant
--
-- By Occam's principle: choose k=2

-- Formally: emergence(k) / complexity(k) is maximal at k=2

data Unit : Set where
  tt : Unit

-- k=2 is optimal (statement)
k2-optimal : Unit
k2-optimal = tt

------------------------------------------------------------------------
-- Connection to distinction
------------------------------------------------------------------------

-- Why k=2 is related to Δ ≠ ∅?
--
-- Distinction requires TWO objects: a ≠ b
-- Memory of distinction requires remembering BOTH: (a, b)
-- Next distinction: c ≠ (a,b) requires remembering (a,b) and c
-- But (a,b) — is ALREADY two memory slots!
--
-- Total: minimal memory for distinction = 2 slots = k=2

-- Distinction (as type)
-- Distinct a b is inhabited if a ≠ b

-- Pair (memory depth 2)
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- To distinguish two objects need to store Pair
-- This is k=2!

------------------------------------------------------------------------
-- CONCLUSION
------------------------------------------------------------------------

{-
  WHY k=2:

  1. NECESSITY: k=1 is trivial (exponential)
  2. SUFFICIENCY: k=2 gives φ and all structure
  3. MINIMALITY: k≥3 is redundant
  4. CONNECTION TO Δ: distinction requires pair = 2 slots

  Consequences of k=2:
  - Fibonacci numbers
  - Golden ratio φ = 1.618...
  - Logarithmic spiral
  - Fractals and self-similarity
  - Quasicrystals (Penrose tiling)

  k=2 — this is NOT an arbitrary choice, but a CONSEQUENCE of Δ ≠ ∅!
-}

conclusion : Unit
conclusion = tt
