#!/bin/bash
# Cercaveicoli Import per Mac: doppio clic per avviare.
cd "$(dirname "$0")" || exit 1
PY=""
for c in /Library/Frameworks/Python.framework/Versions/Current/bin/python3 /opt/homebrew/bin/python3 /usr/local/bin/python3 python3; do
  if command -v "$c" >/dev/null 2>&1 && "$c" -c "import sys; sys.exit(0 if sys.version_info >= (3, 8) else 1)" >/dev/null 2>&1; then
    PY="$c"
    break
  fi
done
if [ -z "$PY" ]; then
  echo ""
  echo " Per funzionare, Cercaveicoli ha bisogno di Python 3, che e' gratuito."
  echo " Scaricalo da https://www.python.org/downloads/ , installalo e poi riapri questo file."
  echo ""
  read -r -p " Premi Invio per chiudere."
  exit 1
fi
# Codice 75 = il programma si e' aggiornato da solo e chiede di essere riavviato
export CV_LOOP=1
while true; do
  "$PY" server.py
  st=$?
  [ "$st" -eq 75 ] || break
done
if [ "$st" -ne 0 ]; then
  echo ""
  echo " Il programma si e' chiuso con un errore (codice $st)."
  echo " Se nella cartella c'e' il file errore.txt, mandalo a chi ti segue il programma."
  read -r -p " Premi Invio per chiudere."
fi
