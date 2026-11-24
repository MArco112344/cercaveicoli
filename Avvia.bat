@echo off
chcp 65001 >nul
title Cercaveicoli Import
cd /d "%~dp0"

if not exist "server.py" goto nofiles

set "PYEXE="
set "PYARGS="

rem --- Cerca un Python gia' presente, in tutti i posti soliti ---
py -3 -c "import sys" >nul 2>nul && (set "PYEXE=py" & set "PYARGS=-3" & goto run)
python -c "import sys" >nul 2>nul && (set "PYEXE=python" & goto run)
python3 -c "import sys" >nul 2>nul && (set "PYEXE=python3" & goto run)
for /d %%D in ("%LocalAppData%\Programs\Python\Python3*") do if exist "%%D\python.exe" set "PYEXE=%%D\python.exe"
if defined PYEXE goto run
for /d %%D in ("%ProgramFiles%\Python3*") do if exist "%%D\python.exe" set "PYEXE=%%D\python.exe"
if defined PYEXE goto run
for /d %%D in ("C:\Python3*") do if exist "%%D\python.exe" set "PYEXE=%%D\python.exe"
if defined PYEXE goto run

rem --- Niente Python: lo si prende dal Microsoft Store (senza amministratore, senza scaricare file) ---
echo.
echo  Per funzionare, Cercaveicoli ha bisogno di Python, che e' gratuito.
echo  Apro il Microsoft Store: premi "Ottieni" (o "Installa"), aspetta che
echo  finisca, poi torna su questa finestra e premi un tasto.
echo.
start "" "ms-windows-store://search/?query=python 3.12"
pause

rem Dopo l'installazione dallo Store, "python" di solito e' subito disponibile.
python -c "import sys" >nul 2>nul && (set "PYEXE=python" & goto run)
for /d %%D in ("%LocalAppData%\Programs\Python\Python3*") do if exist "%%D\python.exe" set "PYEXE=%%D\python.exe"
if defined PYEXE goto run

rem Se lo Store non ha funzionato, provo l'installazione automatica (dove e' permessa).
where winget >nul 2>nul && (
  echo.
  echo  Provo a installarlo in automatico, un momento...
  winget install -e --id Python.Python.3.12 --accept-package-agreements --accept-source-agreements
)
python -c "import sys" >nul 2>nul && (set "PYEXE=python" & goto run)
for /d %%D in ("%LocalAppData%\Programs\Python\Python3*") do if exist "%%D\python.exe" set "PYEXE=%%D\python.exe"
if defined PYEXE goto run

echo.
echo  Non sono riuscito a installare Python su questo computer.
echo  Due strade:
echo    1) Microsoft Store: cerca "Python 3.12" e premi Ottieni. Poi riapri Avvia.bat.
echo    2) https://www.python.org/downloads/  (durante l'installazione spunta la
echo       casella "Add python.exe to PATH"). Poi riapri Avvia.bat.
echo.
echo  Se e' un PC di lavoro che blocca ogni installazione, scrivimelo: ti do una
echo  versione con Python gia' incluso, senza niente da installare.
echo.
pause
goto end

:nofiles
echo.
echo  Non trovo il file server.py accanto ad Avvia.bat.
echo  Devi prima estrarre la cartella dallo zip: clic destro sullo zip,
echo  "Estrai tutto", poi apri la cartella estratta e fai doppio clic su Avvia.bat.
echo.
pause
goto end

:run
rem --- La finestra non resta in primo piano: questo stesso file si riapre ridotto a icona nella barra in basso ---
if defined CV_MIN goto go
set "CV_MIN=1"
set "CV_BAT=%~f0"
set "CV_DIR=%~dp0"
if exist "%~dp0collegamento_creato.txt" goto relaunch
rem La prima volta mette sul desktop l'icona "Cercaveicoli" (una volta sola: se la cancelli non torna)
powershell -NoProfile -Command "try { $d=[Environment]::GetFolderPath('Desktop'); $l=Join-Path $d 'Cercaveicoli.lnk'; if (-not (Test-Path $l)) { $s=(New-Object -ComObject WScript.Shell).CreateShortcut($l); $s.TargetPath=$env:CV_BAT; $s.WorkingDirectory=$env:CV_DIR; $s.WindowStyle=7; $s.IconLocation=$env:SystemRoot+'\System32\shell32.dll,22'; $s.Description='Cercaveicoli Import'; $s.Save() } } catch {}" >nul 2>nul
echo fatto> "%~dp0collegamento_creato.txt" 2>nul
:relaunch
start "Cercaveicoli Import" /min "%~f0"
exit /b

:go
set "CV_LOOP=1"
:again
echo.
echo  Cercaveicoli Import e' in funzione: il programma e' nel browser.
echo  Questa finestra serve solo a tenerlo acceso: chiudila per spegnerlo.
echo.
"%PYEXE%" %PYARGS% server.py
rem Codice 75 = il programma si e' aggiornato da solo e chiede di essere riavviato
if errorlevel 76 goto failed
if errorlevel 75 goto again
if errorlevel 1 goto failed
exit

:failed
start "Cercaveicoli Import - errore" cmd /k "echo. & echo  Il programma si e' chiuso con un errore. & echo  Nella cartella del programma c'e' il file errore.txt: mandalo a chi ti segue il programma. & echo."
exit

:end
