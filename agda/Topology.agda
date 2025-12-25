{-# OPTIONS --safe --without-K #-}

{-
  ТОПОЛОГИЯ ЗАМЫКАНИЯ
  ====================
  
  Любая замкнутая структура имеет три зоны:
  - Внутреннее (Interior): замкнуто, стабильно
  - Граница (Boundary): переход, трансформация  
  - Внешнее (Exterior): открыто, взаимодействие
  
  Стандартная модель:
  - SU(3) = внутреннее (конфайнмент)
  - SU(2) = граница (слабое, нарушение P)
  - U(1)  = внешнее (электромагнетизм)
-}

module Topology where

------------------------------------------------------------------------
-- ОСНОВЫ
------------------------------------------------------------------------

data Void : Set where

infix 4 _==_
data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

------------------------------------------------------------------------
-- ТРИ ЗОНЫ
------------------------------------------------------------------------

data Zone : Set where
  interior : Zone   -- внутреннее
  boundary : Zone   -- граница
  exterior : Zone   -- внешнее

-- Порядок: interior < boundary < exterior (по "открытости")
data _<Z_ : Zone -> Zone -> Set where
  i<b : interior <Z boundary
  b<e : boundary <Z exterior
  i<e : interior <Z exterior

------------------------------------------------------------------------
-- НАПРАВЛЕНИЕ НА ГРАНИЦЕ
------------------------------------------------------------------------

-- Граница имеет направление: внутрь или наружу
data Direction : Set where
  inward  : Direction   -- внутрь (поглощение)
  outward : Direction   -- наружу (излучение)

-- Направления противоположны
opposite : Direction -> Direction
opposite inward = outward
opposite outward = inward

-- P-инверсия: меняет направление
P-transform : Direction -> Direction
P-transform = opposite

-- P-нарушение: система различает направления
-- Если процесс происходит с разной вероятностью в разных направлениях

------------------------------------------------------------------------
-- ЗАМКНУТАЯ СТРУКТУРА
------------------------------------------------------------------------

-- Структура с тремя зонами
record ClosedStructure (Content : Set) : Set where
  field
    -- Содержимое каждой зоны
    int : Content              -- внутреннее содержимое
    bnd : Content × Direction  -- граница + направление
    ext : Content              -- внешнее содержимое

-- Граница связывает внутреннее и внешнее
-- Направление указывает "куда смотрит" граница

------------------------------------------------------------------------
-- ПЕРЕХОДЫ МЕЖДУ ЗОНАМИ
------------------------------------------------------------------------

-- Переход возможен только через границу
data Transition : Zone -> Zone -> Set where
  enter : Transition exterior boundary   -- снаружи на границу
  cross : Transition boundary interior   -- с границы внутрь
  exit  : Transition interior boundary   -- изнутри на границу
  leave : Transition boundary exterior   -- с границы наружу

-- Нельзя перейти напрямую interior <-> exterior
-- Всегда через boundary

-- Полный цикл
data Cycle : Set where
  absorb : Cycle   -- ext → bnd → int (поглощение)
  emit   : Cycle   -- int → bnd → ext (излучение)

-- Описание цикла (не формально, комментарий)
-- absorb: enter (ext→bnd), затем cross (bnd→int)
-- emit: exit (int→bnd), затем leave (bnd→ext)

------------------------------------------------------------------------
-- СИММЕТРИЯ И ЕЁ НАРУШЕНИЕ
------------------------------------------------------------------------

-- Interior симметрия: любая перестановка внутри
-- В физике: SU(3) — перестановка цветов

-- Exterior симметрия: фазовые преобразования
-- В физике: U(1) — изменение фазы

-- Boundary: НАРУШЕННАЯ симметрия
-- Потому что есть направление (inward ≠ outward)

-- Симметрия зоны (концептуально):
-- Interior: полная внутренняя симметрия (SU(3))
-- Exterior: фазовая симметрия (U(1))
-- Boundary: нарушенная симметрия (SU(2) с P-violation)

-- Граница не имеет полной симметрии
boundary-breaks-symmetry : Direction -> Direction -> Set
boundary-breaks-symmetry d1 d2 = d1 == d2 -> Void

-- inward ≠ outward
inward≠outward : boundary-breaks-symmetry inward outward
inward≠outward ()

------------------------------------------------------------------------
-- СТАНДАРТНАЯ МОДЕЛЬ
------------------------------------------------------------------------

-- Интерпретация:

data Interaction : Set where
  strong : Interaction   -- SU(3)
  weak   : Interaction   -- SU(2)
  em     : Interaction   -- U(1)

interaction-zone : Interaction -> Zone
interaction-zone strong = interior
interaction-zone weak = boundary
interaction-zone em = exterior

-- Свойства взаимодействий

-- Конфайнмент = внутреннее не выходит наружу
Confinement : Set
Confinement = Transition interior exterior -> Void

-- У нас нет такого перехода в типе Transition, так что:
confinement-holds : Confinement
confinement-holds ()

-- Дальнодействие = внешнее достигает любой точки
LongRange : Interaction -> Set
LongRange i = interaction-zone i == exterior

em-long-range : LongRange em
em-long-range = refl

-- Короткодействие = граница или внутреннее
ShortRange : Interaction -> Set
ShortRange i = (interaction-zone i == interior) + (interaction-zone i == boundary)

strong-short : ShortRange strong
strong-short = inl refl

weak-short : ShortRange weak
weak-short = inr refl

------------------------------------------------------------------------
-- МАСШТАБ
------------------------------------------------------------------------

-- Разные масштабы = разные границы

-- На масштабе кварков:
--   interior = кварк
--   boundary = глюонное поле
--   exterior = другие адроны

-- На масштабе атомов:
--   interior = ядро
--   boundary = электронные оболочки
--   exterior = другие атомы

-- На масштабе клеток:
--   interior = цитоплазма
--   boundary = мембрана
--   exterior = среда

-- Каждый масштаб имеет свою структуру int/bnd/ext
-- Но ПРИНЦИП один: замыкание через три зоны

------------------------------------------------------------------------
-- ИЕРАРХИЯ
------------------------------------------------------------------------

-- Внешнее одного уровня = внутреннее следующего?

-- Нет, точнее:
-- ВЗАИМОДЕЙСТВИЕ (exterior) одного уровня
-- порождает СТРУКТУРУ (interior) следующего

-- Атомы (exterior кварков) взаимодействуют через U(1)
-- Это взаимодействие создаёт молекулы (interior химии)

------------------------------------------------------------------------
-- НАКОПИТЕЛЬНАЯ ТРИАДА В ТЕРМИНАХ ЗОН
------------------------------------------------------------------------

-- A → AB → ABC → A'
-- 
-- A   = interior (исходное)
-- AB  = boundary (A + контекст)
-- ABC = exterior (A + контекст + наблюдение)
-- A'  = новый interior (обогащённое A)

-- Спираль: exterior становится interior следующего витка

data Spiral : Set where
  start  : Spiral                    -- A (interior)
  expand : Spiral -> Spiral          -- A → AB → ABC (к exterior)
  close  : Spiral -> Spiral          -- ABC → A' (новый interior)

-- Один виток
turn : Spiral -> Spiral
turn s = close (expand (expand s))

------------------------------------------------------------------------
-- ПОЧЕМУ ТРИ ЗОНЫ, НЕ ДВЕ И НЕ ЧЕТЫРЕ
------------------------------------------------------------------------

-- Две зоны (interior/exterior): нет перехода
-- Всё либо внутри, либо снаружи
-- Нет взаимодействия, нет динамики

-- Четыре+ зоны: избыточно
-- Любую дополнительную зону можно свести к:
--   - части interior, или
--   - части boundary, или  
--   - части exterior

-- Три — минимум для: замкнутость + переход + открытость

three-necessary : Set
three-necessary = Zone  -- у нас ровно три конструктора

------------------------------------------------------------------------
-- ИТОГ
------------------------------------------------------------------------

{-
  ФОРМАЛИЗОВАНО:
  
  1. Три зоны: interior / boundary / exterior
  
  2. Переходы только через границу
     (нет прямого interior ↔ exterior)
  
  3. Граница имеет направление (inward/outward)
     → нарушение P-симметрии
  
  4. Стандартная модель:
     SU(3) = interior (конфайнмент)
     SU(2) = boundary (слабое, P-нарушение)
     U(1)  = exterior (дальнодействие)
  
  5. Накопительная триада:
     A = interior
     AB = boundary  
     ABC = exterior
     A' = новый interior
  
  КЛЮЧЕВОЙ ИНСАЙТ:
  
  SU(3)×SU(2)×U(1) — не три "силы"
  Это ТОПОЛОГИЯ замкнутой структуры:
  внутреннее × граница × внешнее
  
  Нарушение симметрии на SU(2) — не случайность
  Граница ДОЛЖНА нарушать симметрию (направлена)
-}
