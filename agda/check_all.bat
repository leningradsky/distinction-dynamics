@echo off
cd /d C:\Users\123\Documents\GitHub\distinction-dynamics\agda

echo ========================================
echo DD Agda Verification
echo ========================================

set AGDA=C:\Users\123\.local\bin\agda.exe
set FLAGS=--safe --without-K --include-path=.

echo.
echo === Base Modules ===

echo Checking Base.agda...
%AGDA% %FLAGS% Base.agda
if %ERRORLEVEL%==0 (echo PASS: Base.agda) else (echo FAIL: Base.agda & goto :error)

echo Checking Axiom.agda...
%AGDA% %FLAGS% Axiom.agda
if %ERRORLEVEL%==0 (echo PASS: Axiom.agda) else (echo FAIL: Axiom.agda & goto :error)

echo Checking Triad.agda...
%AGDA% %FLAGS% Triad.agda
if %ERRORLEVEL%==0 (echo PASS: Triad.agda) else (echo FAIL: Triad.agda & goto :error)

echo Checking Zones.agda...
%AGDA% %FLAGS% Zones.agda
if %ERRORLEVEL%==0 (echo PASS: Zones.agda) else (echo FAIL: Zones.agda & goto :error)

echo Checking Levels.agda...
%AGDA% %FLAGS% Levels.agda
if %ERRORLEVEL%==0 (echo PASS: Levels.agda) else (echo FAIL: Levels.agda & goto :error)

echo.
echo === Core Proofs ===

echo Checking Conservation.agda...
%AGDA% %FLAGS% Conservation.agda
if %ERRORLEVEL%==0 (echo PASS: Conservation.agda) else (echo FAIL: Conservation.agda & goto :error)

echo Checking Topology.agda...
%AGDA% %FLAGS% Topology.agda
if %ERRORLEVEL%==0 (echo PASS: Topology.agda) else (echo FAIL: Topology.agda & goto :error)

echo Checking Dimensions.agda...
%AGDA% %FLAGS% Dimensions.agda
if %ERRORLEVEL%==0 (echo PASS: Dimensions.agda) else (echo FAIL: Dimensions.agda & goto :error)

echo Checking Balance.agda...
%AGDA% %FLAGS% Balance.agda
if %ERRORLEVEL%==0 (echo PASS: Balance.agda) else (echo FAIL: Balance.agda & goto :error)

echo Checking Unity.agda...
%AGDA% %FLAGS% Unity.agda
if %ERRORLEVEL%==0 (echo PASS: Unity.agda) else (echo FAIL: Unity.agda & goto :error)

echo.
echo === Physics ===

echo Checking DD-Core.agda...
%AGDA% %FLAGS% DD-Core.agda
if %ERRORLEVEL%==0 (echo PASS: DD-Core.agda) else (echo FAIL: DD-Core.agda & goto :error)

echo Checking SU3Necessity.agda...
%AGDA% %FLAGS% SU3Necessity.agda
if %ERRORLEVEL%==0 (echo PASS: SU3Necessity.agda) else (echo FAIL: SU3Necessity.agda & goto :error)

echo Checking SU2Impossibility.agda...
%AGDA% %FLAGS% SU2Impossibility.agda
if %ERRORLEVEL%==0 (echo PASS: SU2Impossibility.agda) else (echo FAIL: SU2Impossibility.agda & goto :error)

echo Checking StandardModelFromDD.agda...
%AGDA% %FLAGS% StandardModelFromDD.agda
if %ERRORLEVEL%==0 (echo PASS: StandardModelFromDD.agda) else (echo FAIL: StandardModelFromDD.agda & goto :error)

echo.
echo === Additional ===

echo Checking DDComplete.agda (unsafe)...
%AGDA% --without-K --include-path=. DDComplete.agda
if %ERRORLEVEL%==0 (echo PASS: DDComplete.agda) else (echo FAIL: DDComplete.agda & goto :error)

echo Checking ProcessAwareness.agda...
%AGDA% %FLAGS% ProcessAwareness.agda
if %ERRORLEVEL%==0 (echo PASS: ProcessAwareness.agda) else (echo FAIL: ProcessAwareness.agda & goto :error)

echo Checking LevelsFromAccum.agda...
%AGDA% %FLAGS% LevelsFromAccum.agda
if %ERRORLEVEL%==0 (echo PASS: LevelsFromAccum.agda) else (echo FAIL: LevelsFromAccum.agda & goto :error)

echo Checking TriadAccum.agda...
%AGDA% %FLAGS% TriadAccum.agda
if %ERRORLEVEL%==0 (echo PASS: TriadAccum.agda) else (echo FAIL: TriadAccum.agda & goto :error)

echo Checking AccumTriad.agda...
%AGDA% %FLAGS% AccumTriad.agda
if %ERRORLEVEL%==0 (echo PASS: AccumTriad.agda) else (echo FAIL: AccumTriad.agda & goto :error)

echo.
echo ========================================
echo ALL CHECKS PASSED
echo ========================================
goto :end

:error
echo.
echo ========================================
echo VERIFICATION FAILED
echo ========================================

:end
