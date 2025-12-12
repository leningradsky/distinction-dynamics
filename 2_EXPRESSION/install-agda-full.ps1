# Установка Agda + stdlib (Windows)
# Запустить: powershell -ExecutionPolicy Bypass -File install-agda-full.ps1

Write-Host "========================================"
Write-Host "Полная установка Agda для DD"
Write-Host "========================================"

# Проверка прав администратора
$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)

# Шаг 1: Проверка/установка Chocolatey
Write-Host "`nШаг 1: Проверка Chocolatey..."
$chocoExists = Get-Command choco -ErrorAction SilentlyContinue
if (-not $chocoExists) {
    if (-not $isAdmin) {
        Write-Host "ERROR: Для установки Chocolatey нужны права администратора" -ForegroundColor Red
        Write-Host "Запустите PowerShell от имени администратора" -ForegroundColor Yellow
        exit 1
    }
    Write-Host "Установка Chocolatey..."
    Set-ExecutionPolicy Bypass -Scope Process -Force
    [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072
    iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))
    $env:Path = [System.Environment]::GetEnvironmentVariable("Path","Machine") + ";" + [System.Environment]::GetEnvironmentVariable("Path","User")
}
Write-Host "Chocolatey: OK" -ForegroundColor Green

# Шаг 2: Установка GHC и Cabal
Write-Host "`nШаг 2: Установка GHC и Cabal..."
$ghcExists = Get-Command ghc -ErrorAction SilentlyContinue
if (-not $ghcExists) {
    if (-not $isAdmin) {
        Write-Host "ERROR: Для установки GHC нужны права администратора" -ForegroundColor Red
        exit 1
    }
    choco install ghc cabal -y
    $env:Path = [System.Environment]::GetEnvironmentVariable("Path","Machine") + ";" + [System.Environment]::GetEnvironmentVariable("Path","User")
}
Write-Host "GHC: OK" -ForegroundColor Green

# Шаг 3: Установка Agda
Write-Host "`nШаг 3: Установка Agda (это займёт 10-30 минут)..."
$agdaExists = Get-Command agda -ErrorAction SilentlyContinue
if (-not $agdaExists) {
    Write-Host "Обновление cabal..."
    cabal update
    Write-Host "Компиляция Agda (будет долго, не закрывайте окно)..."
    cabal install Agda --overwrite-policy=always
    
    # Добавить в PATH
    $cabalBin = "$env:APPDATA\cabal\bin"
    $currentPath = [Environment]::GetEnvironmentVariable("Path", "User")
    if ($currentPath -notlike "*$cabalBin*") {
        [Environment]::SetEnvironmentVariable("Path", "$currentPath;$cabalBin", "User")
        $env:Path = "$env:Path;$cabalBin"
    }
}

# Перепроверка
$env:Path = [System.Environment]::GetEnvironmentVariable("Path","Machine") + ";" + [System.Environment]::GetEnvironmentVariable("Path","User")
$agdaExists = Get-Command agda -ErrorAction SilentlyContinue
if ($agdaExists) {
    $ver = agda --version
    Write-Host "Agda установлена: $ver" -ForegroundColor Green
} else {
    Write-Host "ERROR: Agda не найдена после установки" -ForegroundColor Red
    Write-Host "Попробуйте перезапустить терминал и выполнить:" -ForegroundColor Yellow
    Write-Host "  agda --version" -ForegroundColor Yellow
    exit 1
}

# Шаг 4: Установка agda-stdlib
Write-Host "`nШаг 4: Установка agda-stdlib..."
$stdlibDir = "E:\claudecode\DD_v2\agda-stdlib"
if (-not (Test-Path $stdlibDir)) {
    Set-Location "E:\claudecode\DD_v2"
    git clone --depth 1 --branch v1.7.3 https://github.com/agda/agda-stdlib.git agda-stdlib
}
Write-Host "agda-stdlib: OK" -ForegroundColor Green

# Шаг 5: Настройка
Write-Host "`nШаг 5: Настройка..."
$agdaDir = "$env:USERPROFILE\.agda"
if (-not (Test-Path $agdaDir)) {
    New-Item -ItemType Directory -Path $agdaDir | Out-Null
}
"$stdlibDir\standard-library.agda-lib" | Out-File -FilePath "$agdaDir\libraries" -Encoding utf8
"standard-library" | Out-File -FilePath "$agdaDir\defaults" -Encoding utf8
Write-Host "Настройка: OK" -ForegroundColor Green

# Шаг 6: Проверка
Write-Host "`nШаг 6: Проверка..."
Set-Location "E:\claudecode\DD_v2\agda"
agda DDComplete.agda 2>&1 | Out-Null
if ($LASTEXITCODE -eq 0) {
    Write-Host "DDComplete.agda: OK" -ForegroundColor Green
} else {
    Write-Host "DDComplete.agda: FAILED" -ForegroundColor Red
}

Write-Host "`n========================================"
Write-Host "Установка завершена!" -ForegroundColor Green
Write-Host "========================================"
Write-Host "`nПерезапустите терминал для применения PATH"
