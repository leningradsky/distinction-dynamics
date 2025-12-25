# DD Agda Formalization

**Distinction Dynamics — формальная верификация**

## Статус

✅ Все файлы компилируются с `--safe --without-K`
✅ 0 постулатов

## Структура

### Базовые модули

| Файл | Описание |
|------|----------|
| `Base.agda` | Базовые типы: Nat, Bool, ==, Void, +, ×, List, Maybe |
| `Axiom.agda` | Единственная аксиома: Δ≠∅ |
| `Triad.agda` | Триада, накопление, спираль |
| `Zones.agda` | Топология: Interior/Boundary/Exterior |
| `Levels.agda` | Уровни L0-L5, dim + asym = const |

### Основные доказательства

| Файл | Описание |
|------|----------|
| `Conservation.agda` | **Закон сохранения: D + A = R** |
| `Topology.agda` | I/B/E, направленность, P-нарушение |
| `Dimensions.agda` | Измерения свободы, асимметрия |
| `Balance.agda` | C + O = R на уровне зон |
| `Unity.agda` | Связь всех компонентов |

### Физика

| Файл | Описание |
|------|----------|
| `DD-Core.agda` | Минимальное ядро DD |
| `SU3Necessity.agda` | SU(3) необходима для триады |
| `SU3Proven.agda` | S₃ → SU(3) |
| `SU2FromDyad.agda` | SU(2) из диады |
| `SU2Impossibility.agda` | SU(2) недостаточна для триады |
| `StandardModelFromDD.agda` | SM из DD |
| `ThreeGenerations.agda` | Три поколения фермионов |
| `FundamentalConstants.agda` | α, Koide, Weinberg |

### Дополнительно

| Файл | Описание |
|------|----------|
| `DDComplete.agda` | Рефлексивная вселенная |
| `DDUniverse.agda` | Полная цепочка DD → SM |
| `DistCategory.agda` | Категория различений |
| `GoldenRatio.agda` | Фибоначчи и φ |
| `ReflexiveU.agda` | Рефлексивная вселенная |
| `ProcessAwareness.agda` | Уровни и застывание |
| `LevelsFromAccum.agda` | Уровни из накопления |
| `TriadAccum.agda` | Триада как накопление |
| `AccumTriad.agda` | A → AB → ABC → A' |

## Главные теоремы

### 1. Закон сохранения

```
conservation : (l : Level) -> dim l + asym l == Resource
```

**Dimension + Asymmetry = Constant** на всех уровнях.

### 2. Необходимость триады

```
two-not-closed : Dyad -> Dyad -> (Dyad -> Dyad -> Dyad) -> Void
```

Двойка не замыкается. Минимум три.

### 3. SU(3) необходима

```
SU2-too-small : order r == 3 -> order swap <= 2 -> ...
```

SU(2) не содержит элементов порядка 3.

### 4. Конфайнмент

```
confinement : Transition interior exterior -> Void
```

Нет прямого перехода interior → exterior.

### 5. P-нарушение

```
inward/=outward : inward == outward -> Void
```

Граница направлена. Это источник P-нарушения.

## Единая картина

```
Δ≠∅
  ↓
Накопление (A → AB → ABC)
  ↓
Замыкание (триада)
  ↓
Топология (I / B / E)
  ↓
Направленность B (асимметрия)
  ↓
Баланс (C + O = R)
  ↓
Уровни (+1 измерение каждый)
  ↓
Сохранение (D + A = const)
  ↓
Рефлексия (A → 0, сеть)
```

## Физическая интерпретация

```
SU(3) = Interior (конфайнмент)
SU(2) = Boundary (P-нарушение)
U(1)  = Exterior (дальнодействие)

3D пространство = Closure (стабильность)
1D время = Openness (эволюция)
```

## Запуск

```bash
# Один файл
agda --safe --without-K Base.agda

# Все файлы
./check_all.bat
```

## Зависимости

- Agda 2.6+
- Без внешних библиотек (кроме DDWithStdlib.agda)
