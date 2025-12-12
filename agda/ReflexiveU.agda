{-# OPTIONS --guardedness --no-positivity-check #-}

module ReflexiveU where

-- ============================================
-- Рефлексивная вселенная: U с El U = U
-- ============================================

mutual
  data U : Set where
    UNIT : U
    PI : (a : U) → (El a → U) → U
    SIGMA : (a : U) → (El a → U) → U
    -- Рефлексия:
    UNIV : U

  El : U → Set
  El UNIT = UnitT where data UnitT : Set where tt : UnitT
  El (PI a b) = (x : El a) → El (b x)
  El (SIGMA a b) = SigmaT (El a) (λ x → El (b x))
    where
      data SigmaT (A : Set) (B : A → Set) : Set where
        _,_ : (fst : A) → B fst → SigmaT A B
  El UNIV = U  -- ← Ключевой момент!

-- ============================================
-- Проверки
-- ============================================

-- El UNIV = U, то есть U : Set и El UNIV : Set, и они равны
test1 : El UNIV
test1 = UNIT  -- UNIT : U = El UNIV

test2 : El UNIV
test2 = UNIV  -- UNIV : U = El UNIV

-- Можем строить типы "внутри" U:
-- Тип функций из U в U
UtoU : U
UtoU = PI UNIV (λ _ → UNIV)

-- Его интерпретация:
UtoU-type : Set
UtoU-type = El UtoU  -- = U → U

-- Пример функции U → U
idU : El UtoU
idU x = x

-- ============================================
-- Теперь: Dist как код в U
-- ============================================

-- Dist = U → U → U (отношения с кодами в U)
DistCode : U
DistCode = PI UNIV (λ _ → PI UNIV (λ _ → UNIV))

DistType : Set
DistType = El DistCode  -- = U → U → U

-- Пример "различения":
trivialDist : DistType
trivialDist _ _ = UNIT  -- Любые два кода "одинаковы"

-- Более интересно:
eqDist : DistType  
eqDist a b = PI (PI a (λ _ → b)) (λ _ → PI (PI b (λ _ → a)) (λ _ → UNIT))
-- Это кодирует: (a → b) → (b → a) → Unit
-- Грубо: "a и b изоморфны" как условие неразличимости

-- ============================================
-- Самоприменение!
-- ============================================

-- DistCode : U, так что можем применить trivialDist к DistCode
-- trivialDist : U → U → U
-- DistCode : U
-- Значит trivialDist DistCode DistCode : U

distDistDist : U
distDistDist = trivialDist DistCode DistCode

-- Это буквально: "различение между Dist и Dist"
-- Результат — код в U

-- ============================================
-- Более глубокое самоприменение
-- ============================================

-- Можем ли мы построить d : DistType такой, что
-- d применённый к своему собственному коду даёт что-то осмысленное?

-- Идея: d = λ a b → PI (PI a (λ _ → b)) (λ _ → PI (PI b (λ _ → a)) (λ _ → UNIT))
-- Тогда d DistCode DistCode = ...сложное выражение...

selfRefDist : U
selfRefDist = eqDist DistCode DistCode
-- Это: PI (PI DistCode (λ _ → DistCode)) (λ _ → PI (PI DistCode (λ _ → DistCode)) (λ _ → UNIT))
-- То есть: (DistType → DistType) → (DistType → DistType) → Unit
-- Грубо: "если DistType изоморфен себе, то Unit"

-- ============================================
-- Ключевой результат
-- ============================================

-- У нас есть:
-- 1. U : Set
-- 2. El : U → Set
-- 3. El UNIV = U
-- 4. DistCode : U с El DistCode = U → U → U
-- 5. Можем применять DistCode к себе: distOfDist DistCode DistCode : U

-- Это близко к Δ = Δ(Δ), но не совсем изоморфизм.
-- Это скорее: "Δ содержит код для (Δ → Δ → Δ)"

-- ============================================
-- ТЕСТ КОНСИСТЕНТНОСТИ
-- ============================================

-- Попробуем вывести Empty (пустой тип)
-- Если получится — система противоречива

data Empty : Set where
  -- нет конструкторов

-- Добавим код для Empty в расширенную вселенную:
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

-- Отрицание:
Not2 : U2 → U2
Not2 a = PI2 a (λ _ → EMPTY2)

-- Попытка парадокса Рассела:
-- Russell = { x | x ∉ x }
-- В типах: R такой что R ≅ (R → Empty)

-- Можем ли мы это построить?
-- Нужно: code : U2 такой что El2 code = (El2 code → Empty)
-- Это потребовало бы: code = PI2 code (λ _ → EMPTY2)
-- Но code появляется в определении code — это не валидная рекурсия

-- Попытка через диагонализацию:
-- diag a = PI2 a (λ f → Not2 (f f))
-- Проблема: f : El2 a, но f f требует f : El2 a → U2
-- Это не типизируется!
-- Диагонализация заблокирована типовой системой

-- ============================================
-- Почему это (вероятно) безопасно
-- ============================================

-- U2 : Set — коды
-- El2 : U2 → Set — интерпретация
-- El2 UNIV2 = U2 — рефлексия
--
-- Ключевое отличие от Type : Type:
-- У нас НЕТ Set : Set
-- У нас есть: U2 : Set, и El2 UNIV2 = U2
-- Это разные вещи!
--
-- Парадокс требует: R : Set с R = (R → Empty)
-- У нас: code : U2 с El2 code = (El2 code → Empty)
-- Но El2 code : Set, а code : U2 — разные уровни

-- ============================================
-- Итог
-- ============================================

-- Построили рефлексивную вселенную U с El UNIV = U
-- Это позволяет самоприменение кодов
-- Не ясно, ведёт ли это к противоречию
-- --no-positivity-check отключает проверку, которая обычно это предотвращает
-- Нужен более глубокий анализ или формальное доказательство консистентности
