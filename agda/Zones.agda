{-# OPTIONS --safe --without-K #-}

{-
  ZONES - Топологические зоны
  ============================
  
  Interior / Boundary / Exterior
  
  Фундаментальная структура любого замыкания.
-}

module Zones where

open import Base

------------------------------------------------------------------------
-- ТРИ ЗОНЫ
------------------------------------------------------------------------

data Zone : Set where
  interior : Zone   -- замкнутое, стабильное
  boundary : Zone   -- направленное, трансформирующее
  exterior : Zone   -- открытое, взаимодействующее

------------------------------------------------------------------------
-- НАПРАВЛЕНИЕ (для boundary)
------------------------------------------------------------------------

data Direction : Set where
  inward  : Direction   -- внутрь
  outward : Direction   -- наружу

opposite : Direction -> Direction
opposite inward = outward
opposite outward = inward

-- Направления различны
inward/=outward : inward == outward -> Void
inward/=outward ()

------------------------------------------------------------------------
-- ПОРЯДОК ЗОН (по открытости)
------------------------------------------------------------------------

data _<Z_ : Zone -> Zone -> Set where
  i<b : interior <Z boundary
  b<e : boundary <Z exterior
  i<e : interior <Z exterior

------------------------------------------------------------------------
-- ПЕРЕХОДЫ МЕЖДУ ЗОНАМИ
------------------------------------------------------------------------

-- Переход возможен только через boundary
data Transition : Zone -> Zone -> Set where
  enter : Transition exterior boundary   -- снаружи на границу
  cross : Transition boundary interior   -- с границы внутрь
  exit  : Transition interior boundary   -- изнутри на границу
  leave : Transition boundary exterior   -- с границы наружу

-- Нет прямого перехода interior <-> exterior
no-direct : Transition interior exterior -> Void
no-direct ()

no-direct' : Transition exterior interior -> Void
no-direct' ()

------------------------------------------------------------------------
-- КОНФАЙНМЕНТ
------------------------------------------------------------------------

-- Interior не может напрямую выйти наружу
Confinement : Set
Confinement = Transition interior exterior -> Void

confinement : Confinement
confinement ()

------------------------------------------------------------------------
-- ФИЗИЧЕСКАЯ ИНТЕРПРЕТАЦИЯ
------------------------------------------------------------------------

data Interaction : Set where
  strong : Interaction   -- SU(3)
  weak   : Interaction   -- SU(2)
  em     : Interaction   -- U(1)

interaction-zone : Interaction -> Zone
interaction-zone strong = interior
interaction-zone weak = boundary
interaction-zone em = exterior

-- Свойства

LongRange : Interaction -> Set
LongRange i = interaction-zone i == exterior

ShortRange : Interaction -> Set
ShortRange i = (interaction-zone i == interior) + (interaction-zone i == boundary)

em-long : LongRange em
em-long = refl

strong-short : ShortRange strong
strong-short = inl refl

weak-short : ShortRange weak
weak-short = inr refl

------------------------------------------------------------------------
-- СТРУКТУРА С ЗОНАМИ
------------------------------------------------------------------------

record ZonedStructure : Set₁ where
  field
    Content : Set
    int-content : Content
    bnd-direction : Direction
    ext-content : Content
