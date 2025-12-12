@echo off
echo ============================================
echo Distinction Dynamics - Lean 4 Build
echo ============================================
echo.

where lake >nul 2>&1
if %ERRORLEVEL% NEQ 0 (
    echo ERROR: Lean/Lake not found!
    echo.
    echo Please install elan first:
    echo   curl.exe -O --location https://elan.lean-lang.org/elan-init.ps1
    echo   powershell -ExecutionPolicy Bypass -f elan-init.ps1
    echo.
    echo Then restart your terminal and run this script again.
    pause
    exit /b 1
)

echo [1/3] Updating dependencies...
lake update

echo.
echo [2/3] Building DD library...
lake build

echo.
echo [3/3] Type-checking main module...
lake env lean DD.lean

echo.
echo ============================================
echo Build complete!
echo ============================================
pause
