@echo off
set DATA=.\data
set PROJ=.\harness\lean_project

REM Ensure the project is built before running tests (prevents slow automatic builds)
echo Ensuring Lean project is built...
powershell -ExecutionPolicy Bypass -File .\scripts\ensure_built.ps1 -ProjectDir %PROJ%
if %ERRORLEVEL% NEQ 0 (
    echo Build check failed. Please run 'lake build' manually in %PROJ%
    pause
    exit /b 1
)

REM Run the harness
python harness\check_s0.py --data %DATA% --project %PROJ%
pause
