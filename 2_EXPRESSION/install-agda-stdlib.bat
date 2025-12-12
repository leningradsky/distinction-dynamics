@echo off
echo ========================================
echo Установка agda-stdlib для DD
echo ========================================

echo.
echo Шаг 1: Создание директории...
if not exist "%USERPROFILE%\.agda" mkdir "%USERPROFILE%\.agda"
if not exist "E:\claudecode\DD_v2\agda-stdlib" mkdir "E:\claudecode\DD_v2\agda-stdlib"

echo.
echo Шаг 2: Скачивание agda-stdlib...
echo (Требуется git)
cd /d E:\claudecode\DD_v2
git clone --depth 1 --branch v1.7.3 https://github.com/agda/agda-stdlib.git agda-stdlib

echo.
echo Шаг 3: Настройка Agda...
echo E:\claudecode\DD_v2\agda-stdlib\standard-library.agda-lib > "%USERPROFILE%\.agda\libraries"
echo standard-library > "%USERPROFILE%\.agda\defaults"

echo.
echo Шаг 4: Проверка...
cd /d E:\claudecode\DD_v2\agda
agda DDWithStdlib.agda

echo.
echo ========================================
echo Готово!
echo ========================================
pause
