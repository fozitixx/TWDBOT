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
echo Python: %PY%
"%PY%" -c "import tkinter" 2>nul
if errorlevel 1 (
  echo В этом Python нет tkinter ^(окна приложения^). Переустанови Python с python.org,
  echo в установщике оставь галочку "tcl/tk and IDLE".
  pause
  exit /b 1
)
echo Ставлю библиотеки...
"%PY%" -m pip install --upgrade pynput numpy pillow websocket-client
if errorlevel 1 (echo Не удалось поставить библиотеки - пришли скриншот этого окна & pause & exit /b 1)
echo Создаю ярлык "TWD Farm" на рабочем столе...
set "TWD_DIR=%~dp0"
powershell -NoProfile -Command "$s=(New-Object -ComObject WScript.Shell).CreateShortcut([Environment]::GetFolderPath('Desktop')+'\TWD Farm.lnk'); $s.TargetPath=$env:PYW; $s.Arguments=[char]34+$env:TWD_DIR+'twd_bot.py'+[char]34; $s.WorkingDirectory=$env:TWD_DIR; $s.IconLocation=$env:TWD_DIR+'icon.ico'; $s.Description='TWD Farm'; $s.Save(); Write-Host ('Shortcut: '+$s.TargetPath)"
if errorlevel 1 (echo Не получилось создать ярлык & pause & exit /b 1)
echo.
echo Готово: ярлык "TWD Farm" на рабочем столе ^(старый ярлык он заменил^).
pause
