@echo off
chcp 65001
cd /d E:\claudecode\DD_v2\agda

echo === DD AGDA VERIFICATION ===
echo.

set PASS=0
set FAIL=0

echo [1/16] DDComplete.agda...
agda --include-path=. DDComplete.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [2/16] DDWithStdlib.agda...
agda --include-path=. --include-path=..\agda-stdlib\src DDWithStdlib.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [3/16] ThirdNecessity.agda...
agda --include-path=. ThirdNecessity.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [4/16] GoldenRatio.agda...
agda --include-path=. GoldenRatio.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [5/16] DistCategory.agda...
agda --include-path=. DistCategory.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [6/16] SU3Necessity.agda...
agda --include-path=. SU3Necessity.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [7/16] FundamentalConstants.agda...
agda --include-path=. FundamentalConstants.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [8/16] StandardModelFromDD.agda...
agda --include-path=. StandardModelFromDD.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [9/16] DDUniverse.agda...
agda --include-path=. DDUniverse.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [10/16] DDUniverseASCII.agda...
agda --include-path=. DDUniverseASCII.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [11/16] DD-Core.agda...
agda --include-path=. DD-Core.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [12/16] DDAxiomatic.agda...
agda --include-path=. DDAxiomatic.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [13/16] SU2FromDyad.agda...
agda --include-path=. SU2FromDyad.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [14/16] ThreeGenerations.agda...
agda --include-path=. ThreeGenerations.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [15/16] WhyK2.agda...
agda --include-path=. WhyK2.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [16/17] ReflexiveU.agda...
agda --include-path=. ReflexiveU.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo [17/17] DD-Main.agda...
agda --include-path=. DD-Main.agda 2>&1 | findstr /i "error"
if %ERRORLEVEL%==1 (echo PASS & set /a PASS+=1) else (echo FAIL & set /a FAIL+=1)

echo.
echo === RESULTS ===
echo PASS: %PASS%
echo FAIL: %FAIL%
