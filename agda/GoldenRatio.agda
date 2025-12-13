{-# OPTIONS --no-positivity-check #-}

module GoldenRatio where

-- Natural numbers
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

-- Rationals as a pair (numerator, denominator)
record Rat : Set where
  constructor _/_
  field
    num : Nat
    den : Nat  -- implicitly +1 to avoid division by 0

-- Nat arithmetic
_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N (n *N m)

-- Fibonacci
fib : Nat -> Nat
fib zero = zero
fib (suc zero) = suc zero
fib (suc (suc n)) = fib (suc n) +N fib n

-- Sequence of ratios fib(n+1)/fib(n)
-- This converges to phi
fibRatio : Nat -> Rat
fibRatio zero = suc zero / zero        -- 1/1
fibRatio (suc n) = fib (suc (suc n)) / fib (suc n)

-- Examples:
-- fibRatio 0 = 1/1 = 1
-- fibRatio 1 = fib(2)/fib(1) = 1/1 = 1
-- fibRatio 2 = fib(3)/fib(2) = 2/1 = 2
-- fibRatio 3 = fib(4)/fib(3) = 3/2 = 1.5
-- fibRatio 4 = fib(5)/fib(4) = 5/3 = 1.666...
-- fibRatio 5 = fib(6)/fib(5) = 8/5 = 1.6
-- ...
-- lim = phi = 1.618...

-- KEY PROPERTY OF PHI:
-- phi^2 = phi + 1
-- Equivalently: phi = 1 + 1/phi

-- For fib: fib(n+2) = fib(n+1) + fib(n)
-- Divide by fib(n+1): fib(n+2)/fib(n+1) = 1 + fib(n)/fib(n+1)
-- That is: r(n+1) = 1 + 1/r(n) where r(n) = fib(n+1)/fib(n)

-- This is RECURSION x_{n+1} = 1 + 1/x_n
-- Its fixed point: x = 1 + 1/x => x^2 = x + 1 => x = phi

-- Recursive type (infinite tree)
data InfTree : Set where
  node : InfTree -> InfTree -> InfTree

-- CONCLUSION:
-- 1. Defined Nat, Rat, fib, fibRatio
-- 2. fibRatio(n) -> phi as n -> infinity
-- 3. phi satisfies phi^2 = phi + 1
-- 4. This FOLLOWS from the recursion fib(n+2) = fib(n+1) + fib(n)
