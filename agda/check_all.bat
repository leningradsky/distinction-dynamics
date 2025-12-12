@echo off
cd /d E:\claudecode\DD_v2\agda

echo Checking DDComplete.agda...
agda --include-path=. DDComplete.agda
if %ERRORLEVEL%==0 (echo PASS: DDComplete.agda) else (echo FAIL: DDComplete.agda)

echo Checking DDWithStdlib.agda...
agda --include-path=. DDWithStdlib.agda
if %ERRORLEVEL%==0 (echo PASS: DDWithStdlib.agda) else (echo FAIL: DDWithStdlib.agda)

echo Checking ThirdNecessity.agda...
agda --include-path=. ThirdNecessity.agda
if %ERRORLEVEL%==0 (echo PASS: ThirdNecessity.agda) else (echo FAIL: ThirdNecessity.agda)

echo Checking GoldenRatio.agda...
agda --include-path=. GoldenRatio.agda
if %ERRORLEVEL%==0 (echo PASS: GoldenRatio.agda) else (echo FAIL: GoldenRatio.agda)

echo Checking DistCategory.agda...
agda --include-path=. DistCategory.agda
if %ERRORLEVEL%==0 (echo PASS: DistCategory.agda) else (echo FAIL: DistCategory.agda)

echo Checking SU3Necessity.agda...
agda --include-path=. SU3Necessity.agda
if %ERRORLEVEL%==0 (echo PASS: SU3Necessity.agda) else (echo FAIL: SU3Necessity.agda)

echo Checking FundamentalConstants.agda...
agda --include-path=. FundamentalConstants.agda
if %ERRORLEVEL%==0 (echo PASS: FundamentalConstants.agda) else (echo FAIL: FundamentalConstants.agda)

echo Checking StandardModelFromDD.agda...
agda --include-path=. StandardModelFromDD.agda
if %ERRORLEVEL%==0 (echo PASS: StandardModelFromDD.agda) else (echo FAIL: StandardModelFromDD.agda)

echo Done.
