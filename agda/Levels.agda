{-# OPTIONS --safe --without-K #-}

{-
  LEVELS - Иерархия уровней
  ==========================
  
  От физики до рефлексии.
  Dimension + Asymmetry = Resource (закон сохранения)
-}

module Levels where

open import Base

------------------------------------------------------------------------
-- УРОВНИ
------------------------------------------------------------------------

data Level : Set where
  physical   : Level   -- L0: частицы, поля
  chemical   : Level   -- L1: атомы, молекулы
  biological : Level   -- L2: клетки, организмы
  neural     : Level   -- L3: нервная система
  conscious  : Level   -- L4: сознание, Я
  reflexive  : Level   -- L5: рефлексия, DD

------------------------------------------------------------------------
-- DIMENSION (измерения свободы)
------------------------------------------------------------------------

dim : Level -> Nat
dim physical = 0
dim chemical = 1
dim biological = 2
dim neural = 3
dim conscious = 4
dim reflexive = 5

------------------------------------------------------------------------
-- ASYMMETRY (отделённость)
------------------------------------------------------------------------

asym : Level -> Nat
asym physical = 5
asym chemical = 4
asym biological = 3
asym neural = 2
asym conscious = 1
asym reflexive = 0

------------------------------------------------------------------------
-- RESOURCE (константа)
------------------------------------------------------------------------

Resource : Nat
Resource = 5

------------------------------------------------------------------------
-- ЗАКОН СОХРАНЕНИЯ
------------------------------------------------------------------------

-- dim l + asym l = Resource

conservation : (l : Level) -> dim l +N asym l == Resource
conservation physical = refl
conservation chemical = refl
conservation biological = refl
conservation neural = refl
conservation conscious = refl
conservation reflexive = refl

------------------------------------------------------------------------
-- ПОРЯДОК УРОВНЕЙ
------------------------------------------------------------------------

data _<L_ : Level -> Level -> Set where
  p<c : physical <L chemical
  c<b : chemical <L biological
  b<n : biological <L neural
  n<o : neural <L conscious
  o<r : conscious <L reflexive

-- Следующий уровень
next : Level -> Maybe Level
next physical = just chemical
next chemical = just biological
next biological = just neural
next neural = just conscious
next conscious = just reflexive
next reflexive = nothing

-- Предыдущий уровень
prev : Level -> Maybe Level
prev physical = nothing
prev chemical = just physical
prev biological = just chemical
prev neural = just biological
prev conscious = just neural
prev reflexive = just conscious

------------------------------------------------------------------------
-- ТОПОЛОГИЯ УРОВНЯ
------------------------------------------------------------------------

data Topology : Set where
  hierarchy : Topology   -- уровни друг над другом
  network   : Topology   -- взаимопроникновение

topology : Level -> Topology
topology physical = hierarchy
topology chemical = hierarchy
topology biological = hierarchy
topology neural = hierarchy
topology conscious = hierarchy
topology reflexive = network   -- asym = 0 -> сеть

------------------------------------------------------------------------
-- ИЗМЕРЕНИЯ ОБРАБОТКИ
------------------------------------------------------------------------

data ProcessDim : Set where
  what     : ProcessDim   -- ЧТО обрабатывать
  how      : ProcessDim   -- КАК обрабатывать
  when-chg : ProcessDim   -- КОГДА менять как
  why-chg  : ProcessDim   -- ПОЧЕМУ менять
  meta-why : ProcessDim   -- менять принцип почему

-- Какие измерения доступны на уровне
has-what : Level -> Bool
has-what physical = false
has-what _ = true

has-how : Level -> Bool
has-how physical = false
has-how chemical = false
has-how _ = true

has-when : Level -> Bool
has-when physical = false
has-when chemical = false
has-when biological = false
has-when _ = true

has-why : Level -> Bool
has-why physical = false
has-why chemical = false
has-why biological = false
has-why neural = false
has-why _ = true

has-meta : Level -> Bool
has-meta reflexive = true
has-meta _ = false
