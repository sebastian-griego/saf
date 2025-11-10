@echo off
set DATA=.\data
set PROJ=.\harness\lean_project
python harness\check_s0.py --data %DATA% --project %PROJ%
pause
