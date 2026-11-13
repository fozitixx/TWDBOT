@echo off
chcp 65001 >nul
cd /d "%~dp0"
set "PY="
for %%V in (314 313 312 311 310) do if not defined PY if exist "%LOCALAPPDATA%\Programs\Python\Python%%V\python.exe" set "PY=%LOCALAPPDATA%\Programs\Python\Python%%V\python.exe"
for %%V in (314 313 312 311 310) do if not defined PY if exist "%ProgramFiles%\Python%%V\python.exe" set "PY=%ProgramFiles%\Python%%V\python.exe"
for %%V in (314 313 312 311 310) do if not defined PY if exist "C:\Python%%V\python.exe" set "PY=C:\Python%%V\python.exe"
if not defined PY for /d %%D in ("%LOCALAPPDATA%\Python\pythoncore-3*") do if exist "%%D\python.exe" set "PY=%%D\python.exe"
if not defined PY for /f "delims=" %%P in ('py -3 -c "import sys;print(sys.executable)" 2^>nul') do set "PY=%%P"
if not defined PY for /f "delims=" %%P in ('where python 2^>nul ^| findstr /v /i WindowsApps') do if not defined PY set "PY=%%P"
if not defined PY (
  echo Python не найден на этом компьютере.
  echo Установи его с https://www.python.org/downloads/ ^(при установке отметь "Add python.exe to PATH"^),
  echo потом запусти этот файл ещё раз.
  pause
  exit /b 1
)
for %%D in ("%PY%") do set "PYW=%%~dpDpythonw.exe"
if not exist "%PYW%" set "PYW=%PY%"
start "" "%PYW%" "%~dp0twd_bot.py"
