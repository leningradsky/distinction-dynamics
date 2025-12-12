# Полная установка Agda + stdlib для DD

## Вариант 1: Через Chocolatey (рекомендуется)

```powershell
# Установить Chocolatey (если нет): https://chocolatey.org/install
# Затем в PowerShell (Admin):

choco install ghc cabal git -y
cabal update
cabal install Agda
```

## Вариант 2: Через GHCup

```powershell
# Скачать: https://www.haskell.org/ghcup/
# Установить GHC и Cabal
# Затем:

cabal update
cabal install Agda
```

## После установки Agda

Запустить скрипт:

```powershell
cd E:\claudecode\DD_v2
powershell -ExecutionPolicy Bypass -File install-agda-stdlib.ps1
```

Или вручную:

```powershell
# 1. Клонировать stdlib
cd E:\claudecode\DD_v2
git clone --depth 1 --branch v1.7.3 https://github.com/agda/agda-stdlib.git

# 2. Настроить
mkdir $env:USERPROFILE\.agda -Force
"E:\claudecode\DD_v2\agda-stdlib\standard-library.agda-lib" | Out-File $env:USERPROFILE\.agda\libraries
"standard-library" | Out-File $env:USERPROFILE\.agda\defaults

# 3. Проверить
cd E:\claudecode\DD_v2\agda
agda DDWithStdlib.agda
```

## Проверка

После установки все эти файлы должны компилироваться:

```
E:\claudecode\DD_v2\agda\
├── DDComplete.agda      ✓
├── DDWithStdlib.agda    ✓ (требует stdlib)
├── ThirdNecessity.agda  ✓
├── GoldenRatio.agda     ✓
├── DistCategory.agda    ✓
```

## Troubleshooting

### "agda не найдена"
- Добавить в PATH: `%APPDATA%\cabal\bin`
- Перезапустить терминал

### "standard-library not found"
- Проверить что файл `E:\claudecode\DD_v2\agda-stdlib\standard-library.agda-lib` существует
- Проверить содержимое `%USERPROFILE%\.agda\libraries`

### "type-in-type" warning
- Это нормально, мы используем `--type-in-type` намеренно для рефлексии
