@echo off
chcp 65001 >nul
cd /d "%~dp0"
set PY="%LOCALAPPDATA%\Programs\Python\Python314\python.exe"
%PY% twd_bot.py diag
pause
