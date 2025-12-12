@echo off
echo Building Distinction Dynamics...
echo.

cd /d "%~dp0"

pdflatex -interaction=nonstopmode distinction_dynamics.tex
pdflatex -interaction=nonstopmode distinction_dynamics.tex

echo.
echo ============================================
if exist distinction_dynamics.pdf (
    echo SUCCESS: distinction_dynamics.pdf created
    echo.
    start "" "distinction_dynamics.pdf"
) else (
    echo ERROR: PDF not created. Check distinction_dynamics.log
)
echo ============================================
pause
