@echo off
chcp 65001 >nul
cd /d C:\Users\123\Documents\GitHub\distinction-dynamics\agda

set AGDA=C:\Users\123\.local\bin\agda.exe
set SAFE=--safe --without-K -i .
set UNSAFE=--without-K -i .

echo ========================================
echo DD FULL VERIFICATION
echo ========================================

echo.
echo === SAFE FILES (--safe --without-K) ===

for %%f in (
    Base.agda
    Axiom.agda
    Triad.agda
    Zones.agda
    Levels.agda
    Conservation.agda
    Topology.agda
    Dimensions.agda
    Balance.agda
    Unity.agda
    DD-Core.agda
    SU3Necessity.agda
    SU3Proven.agda
    SU2Impossibility.agda
    SU2FromDyad.agda
    StandardModelFromDD.agda
    SMProven.agda
    ThreeGenerations.agda
    FundamentalConstants.agda
    WhyK2.agda
    ProcessAwareness.agda
    LevelsFromAccum.agda
    TriadAccum.agda
    AccumTriad.agda
    DDLevel-1.agda
    Physics.agda
    Reflexive.agda
    Resource.agda
    Spiral.agda
    Symmetry.agda
) do (
    %AGDA% %SAFE% %%f >nul 2>&1
    if errorlevel 1 (echo FAIL: %%f) else (echo PASS: %%f)
)

echo.
echo === UNSAFE FILES (--without-K only) ===

for %%f in (
    ThirdNecessity.agda
    GoldenRatio.agda
    DistCategory.agda
    DD-Main.agda
    DD-Strict.agda
    DDComplete.agda
    DDUniverse.agda
    DDUniverseASCII.agda
    DDUniverseProven.agda
    DDAxiomatic.agda
    ReflexiveU.agda
) do (
    %AGDA% %UNSAFE% %%f >nul 2>&1
    if errorlevel 1 (echo FAIL: %%f) else (echo PASS: %%f)
)

echo.
echo === REQUIRES STDLIB ===

for %%f in (
    DDWithStdlib.agda
) do (
    %AGDA% %UNSAFE% -l standard-library %%f >nul 2>&1
    if errorlevel 1 (echo FAIL: %%f) else (echo PASS: %%f)
)

echo.
echo ========================================
echo VERIFICATION COMPLETE
echo ========================================
