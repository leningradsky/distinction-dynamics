{-# OPTIONS --no-positivity-check --type-in-type #-}

module DDComplete where

data Empty : Set where
data Unit : Set where tt : Unit

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field fst : A; snd : B fst
open Sigma

Not : Set -> Set
Not A = A -> Empty

Distinct : {U : Set} -> U -> U -> Set
Distinct a b = Not (a == b)

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

mutual
  data U : Set where
    UNIT EMPTY UNIV NAT : U
    PI SIGMA : (a : U) -> (El a -> U) -> U
    
  El : U -> Set
  El UNIT = Unit
  El EMPTY = Empty
  El UNIV = U
  El NAT = Nat
  El (PI a b) = (x : El a) -> El (b x)
  El (SIGMA a b) = Sigma (El a) (\x -> El (b x))

-- THEOREM 1: Three distinct codes (PROVEN)
UNIT-neq-EMPTY : Distinct UNIT EMPTY
UNIT-neq-EMPTY ()

UNIT-neq-UNIV : Distinct UNIT UNIV
UNIT-neq-UNIV ()

EMPTY-neq-UNIV : Distinct EMPTY UNIV
EMPTY-neq-UNIV ()

-- Triad
data Three : Set where A B C : Three

sym : {A : Set} {x y : A} -> x == y -> y == x
sym refl = refl

record Triad : Set where
  field
    obj : Three -> U
    AB : Distinct (obj A) (obj B)
    BC : Distinct (obj B) (obj C)
    CA : Distinct (obj C) (obj A)

canonicalTriad : Triad
canonicalTriad = record
  { obj = \{ A -> UNIT ; B -> EMPTY ; C -> UNIV }
  ; AB = UNIT-neq-EMPTY
  ; BC = EMPTY-neq-UNIV
  ; CA = \p -> UNIT-neq-UNIV (sym p)
  }

-- Category D
record Category : Set1 where
  field
    Obj : Set
    Hom : Obj -> Obj -> Set
    id : {a : Obj} -> Hom a a
    compose : {a b c : Obj} -> Hom b c -> Hom a b -> Hom a c

D : Category
D = record
  { Obj = U
  ; Hom = \a b -> El a -> El b
  ; id = \x -> x
  ; compose = \g f x -> g (f x)
  }

-- Contravariance of consciousness (PROVEN)
ConsciousnessF0 : U -> U
ConsciousnessF0 a = PI a (\_ -> UNIV)

ConsciousnessF1 : {a b : U} -> (El a -> El b) -> (El (ConsciousnessF0 b) -> El (ConsciousnessF0 a))
ConsciousnessF1 f g = \x -> g (f x)

-- Permutations S3
data Perm3 : Set where
  e r r2 s1 s2 s3 : Perm3

apply : Perm3 -> Three -> Three
apply e x = x
apply r A = B
apply r B = C
apply r C = A
apply r2 A = C
apply r2 B = A
apply r2 C = B
apply s1 A = B
apply s1 B = A
apply s1 C = C
apply s2 A = A
apply s2 B = C
apply s2 C = B
apply s3 A = C
apply s3 B = B
apply s3 C = A

-- Distinction code lives in UNIV (PROVEN)
EqCode : U -> U -> U
EqCode UNIT UNIT = UNIT
EqCode EMPTY EMPTY = UNIT
EqCode UNIV UNIV = UNIT
EqCode NAT NAT = UNIT
EqCode _ _ = EMPTY

DistinctCode : U -> U -> U
DistinctCode a b = PI (EqCode a b) (\_ -> EMPTY)

distinctUE : El (DistinctCode UNIT EMPTY)
distinctUE ()

distinctUU : El (DistinctCode UNIT UNIV)
distinctUU ()

-- Arithmetic
_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

fib : Nat -> Nat
fib zero = zero
fib (suc zero) = suc zero
fib (suc (suc n)) = fib (suc n) + fib n
