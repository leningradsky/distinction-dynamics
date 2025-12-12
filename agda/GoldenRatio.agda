{-# OPTIONS --no-positivity-check #-}

module GoldenRatio where

-- Натуральные числа
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

-- Рациональные как пара (числитель, знаменатель)
record Rat : Set where
  constructor _/_
  field
    num : Nat
    den : Nat  -- неявно +1, чтобы избежать деления на 0

-- Арифметика Nat
_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N (n *N m)

-- Фибоначчи
fib : Nat -> Nat
fib zero = zero
fib (suc zero) = suc zero
fib (suc (suc n)) = fib (suc n) +N fib n

-- Последовательность отношений fib(n+1)/fib(n)
-- Это сходится к phi
fibRatio : Nat -> Rat
fibRatio zero = suc zero / zero        -- 1/1 
fibRatio (suc n) = fib (suc (suc n)) / fib (suc n)

-- Примеры:
-- fibRatio 0 = 1/1 = 1
-- fibRatio 1 = fib(2)/fib(1) = 1/1 = 1
-- fibRatio 2 = fib(3)/fib(2) = 2/1 = 2
-- fibRatio 3 = fib(4)/fib(3) = 3/2 = 1.5
-- fibRatio 4 = fib(5)/fib(4) = 5/3 = 1.666...
-- fibRatio 5 = fib(6)/fib(5) = 8/5 = 1.6
-- ...
-- lim = phi = 1.618...

-- КЛЮЧЕВОЕ СВОЙСТВО PHI:
-- phi^2 = phi + 1
-- Эквивалентно: phi = 1 + 1/phi

-- Для fib: fib(n+2) = fib(n+1) + fib(n)
-- Делим на fib(n+1): fib(n+2)/fib(n+1) = 1 + fib(n)/fib(n+1)
-- То есть: r(n+1) = 1 + 1/r(n) где r(n) = fib(n+1)/fib(n)

-- Это РЕКУРСИЯ x_{n+1} = 1 + 1/x_n
-- Её фиксированная точка: x = 1 + 1/x => x^2 = x + 1 => x = phi

-- Рекурсивный тип (бесконечное дерево)
data InfTree : Set where
  node : InfTree -> InfTree -> InfTree

-- ИТОГ:
-- 1. Определили Nat, Rat, fib, fibRatio
-- 2. fibRatio(n) -> phi при n -> infinity
-- 3. phi удовлетворяет phi^2 = phi + 1
-- 4. Это СЛЕДУЕТ из рекурсии fib(n+2) = fib(n+1) + fib(n)
