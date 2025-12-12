{-# OPTIONS --no-positivity-check --type-in-type #-}

module ThirdNecessity where

data Empty : Set where
data Unit : Set where tt : Unit

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

Not : Set -> Set
Not A = A -> Empty

record Sigma (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field fst : A; snd : B fst

mutual
  data U : Set where
    UNIT EMPTY UNIV : U
    PI SIGMA : (a : U) -> (El a -> U) -> U

  El : U -> Set
  El UNIT = Unit
  El EMPTY = Empty
  El UNIV = U
  El (PI a b) = (x : El a) -> El (b x)
  El (SIGMA a b) = Sigma (El a) (\x -> El (b x))

Distinct : U -> U -> Set
Distinct a b = Not (a == b)

EqCode : U -> U -> U
EqCode UNIT UNIT = UNIT
EqCode EMPTY EMPTY = UNIT
EqCode UNIV UNIV = UNIT
EqCode _ _ = EMPTY

 DistinctCode : U -> U -> U
 DistinctCode a b = PI (EqCode a b) (\_ -> EMPTY)

data Three : Set where A B C : Three

record ClosedTriad : Set where
  field
    codeA codeB codeC : U
    AB-witness : El (DistinctCode codeA codeB)
    BC-witness : El (DistinctCode codeB codeC)
    CA-witness : El (DistinctCode codeC codeA)

absurd : {A : Set} -> Empty -> A
absurd ()

exampleTriad : ClosedTriad
exampleTriad = record
  { codeA = UNIT
  ; codeB = EMPTY
  ; codeC = UNIV
  ; AB-witness = absurd
  ; BC-witness = absurd
  ; CA-witness = absurd
  }

-- THEOREM: Distinction lives in UNIV
distinctLivesInU : (a b : U) -> U
distinctLivesInU a b = DistinctCode a b

-- Witnesses at the type level
unitNeqEmpty : Distinct UNIT EMPTY
unitNeqEmpty ()

emptyNeqUniv : Distinct EMPTY UNIV
emptyNeqUniv ()

univNeqUnit : Distinct UNIV UNIT
univNeqUnit ()

-- CONCLUSION: UNIV - universal carrier of distinctions
-- For ANY pair (a, b) : U x U
-- the code of their distinction DistinctCode a b : U
-- lives in El UNIV = U
