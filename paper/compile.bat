@echo off
echo Compiling DD paper...
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
echo.
echo Done. Check main.pdf
pause
