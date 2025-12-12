# Установка agda-stdlib для DD
# Запустить: powershell -ExecutionPolicy Bypass -File install-agda-stdlib.ps1

Write-Host "========================================"
Write-Host "Установка agda-stdlib для DD"
Write-Host "========================================"

# Шаг 1: Проверка git
Write-Host "`nШаг 1: Проверка git..."
$gitExists = Get-Command git -ErrorAction SilentlyContinue
if (-not $gitExists) {
    Write-Host "ERROR: Git не найден. Установите git: https://git-scm.com/download/win" -ForegroundColor Red
    exit 1
}
Write-Host "Git найден: OK" -ForegroundColor Green

# Шаг 2: Проверка Agda
Write-Host "`nШаг 2: Проверка Agda..."
$agdaExists = Get-Command agda -ErrorAction SilentlyContinue
if (-not $agdaExists) {
    Write-Host "ERROR: Agda не найдена." -ForegroundColor Red
    Write-Host "Установите через: cabal install Agda" -ForegroundColor Yellow
    Write-Host "Или: choco install agda" -ForegroundColor Yellow
    exit 1
}
$agdaVersion = agda --version
Write-Host "Agda найдена: $agdaVersion" -ForegroundColor Green

# Шаг 3: Создание директорий
Write-Host "`nШаг 3: Создание директорий..."
$agdaDir = "$env:USERPROFILE\.agda"
$stdlibDir = "E:\claudecode\DD_v2\agda-stdlib"

if (-not (Test-Path $agdaDir)) {
    New-Item -ItemType Directory -Path $agdaDir | Out-Null
    Write-Host "Создана: $agdaDir"
}

# Шаг 4: Клонирование agda-stdlib
Write-Host "`nШаг 4: Клонирование agda-stdlib..."
if (Test-Path $stdlibDir) {
    Write-Host "agda-stdlib уже существует, пропускаем..." -ForegroundColor Yellow
} else {
    Set-Location "E:\claudecode\DD_v2"
    git clone --depth 1 --branch v1.7.3 https://github.com/agda/agda-stdlib.git agda-stdlib
    if ($LASTEXITCODE -ne 0) {
        Write-Host "ERROR: Не удалось клонировать agda-stdlib" -ForegroundColor Red
        exit 1
    }
    Write-Host "agda-stdlib клонирован: OK" -ForegroundColor Green
}

# Шаг 5: Настройка Agda
Write-Host "`nШаг 5: Настройка Agda..."
$libPath = "$stdlibDir\standard-library.agda-lib"
Set-Content -Path "$agdaDir\libraries" -Value $libPath
Set-Content -Path "$agdaDir\defaults" -Value "standard-library"
Write-Host "Настройка: OK" -ForegroundColor Green

# Шаг 6: Проверка
Write-Host "`nШаг 6: Проверка компиляции..."
Set-Location "E:\claudecode\DD_v2\agda"

Write-Host "Компиляция DDComplete.agda..."
agda DDComplete.agda
if ($LASTEXITCODE -eq 0) {
    Write-Host "DDComplete.agda: OK" -ForegroundColor Green
}

Write-Host "Компиляция DDWithStdlib.agda..."
agda DDWithStdlib.agda
if ($LASTEXITCODE -eq 0) {
    Write-Host "DDWithStdlib.agda: OK" -ForegroundColor Green
}

Write-Host "`n========================================"
Write-Host "Установка завершена!" -ForegroundColor Green
Write-Host "========================================"
