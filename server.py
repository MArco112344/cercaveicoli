#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Cercaveicoli Import - programma locale.

Apre l'interfaccia nel browser, legge dal computer dell'utente le pagine di
ricerca dei siti di annunci che lo ammettono, controlla ogni annuncio con i
filtri richiesti e riunisce quelli validi in una tabella.
Usa solo la libreria standard di Python: non serve installare altro.
"""
import atexit
import base64
import csv
import glob
import hashlib
import http.client
import http.cookiejar
import io
import json
import os
import queue
import re
import secrets
import shutil
import socket
import ssl
import struct
import subprocess
import sys
import threading
import time
import unicodedata
import uuid
import webbrowser
import zipfile
import zlib
from concurrent.futures import ThreadPoolExecutor
from html import unescape as html_unescape
from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib import error as urlerr
from urllib import request as urlreq
from urllib.parse import parse_qs, urljoin, urlparse, urlunparse

APP_DIR = os.path.dirname(os.path.abspath(__file__))


def data_dir():
    """Cartella dei dati del programma, fuori da quella scaricata: quello che c'e' qui resta da una versione all'altra."""
    if sys.platform.startswith('win'):
        base = os.environ.get('LOCALAPPDATA') or os.path.expanduser('~')
    elif sys.platform == 'darwin':
        base = os.path.expanduser('~/Library/Application Support')
    else:
        base = os.environ.get('XDG_DATA_HOME') or os.path.expanduser('~/.local/share')
    return os.path.join(base, 'CercaveicoliImport')


# Impostazioni e chiave Bright Data: nella cartella dei dati, cosi' non finiscono in uno zip passato ad altri
# e non vanno riscritte a ogni versione nuova. Fino alla 2.2 stavano accanto al programma.
CONFIG_PATH = os.path.join(data_dir(), 'config.json')
CA_BUNDLE = os.path.join(APP_DIR, 'cacert.pem')  # autorita' di certificazione riconosciute da Mozilla (le stesse di Firefox), distribuite con il programma
SITES_PATH = os.path.join(APP_DIR, 'siti_personali.json')
INDEX_PATH = os.path.join(APP_DIR, 'index.html')
BD_BASE = os.environ.get('CV_BRIGHTDATA_BASE', 'https://api.brightdata.com').rstrip('/')
SESSION_PATH = os.path.join(APP_DIR, 'sessione.json')
TOKEN = ''  # si legge piu' sotto: resta lo stesso da un avvio all'altro, cosi' una scheda rimasta aperta continua a funzionare
BOOT = secrets.token_hex(6)  # cambia a ogni avvio: la pagina se ne accorge e si aggiorna da sola
JOBS = {}
JOBS_LOCK = threading.Lock()
MAX_PAGES_PER_SCAN = 60
VERSION = '2.9'
# Lettura diretta: il programma si presenta con il proprio nome, senza fingersi un browser
UA = "CercaveicoliImport/2.9 (ricerca auto avviata dall'utente; poche pagine per sito)"
ROBOT_NAME = 'cercaveicoliimport'
DIRECT_GAP = float(os.environ.get('CV_DIRECT_GAP') or 1.2)  # secondi tra due letture dello stesso sito
TEST_ORIGIN = os.environ.get('CV_TEST_ORIGIN', '').rstrip('/')  # solo per le prove


# --------------------------------------------------------------------------
# Impostazioni
# --------------------------------------------------------------------------
def load_json(path, default):
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path, data):
    os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


ERROR_PATH = os.path.join(APP_DIR, 'errore.txt')


def log_error(where, exc):
    """Annota un errore imprevisto in errore.txt (al piu' 300 KB), con la versione di Python e del programma."""
    try:
        import traceback
        text = '--- %s | Cercaveicoli %s | Python %s | %s | %s\n%s\n' % (
            time.strftime('%Y-%m-%d %H:%M:%S'), VERSION, sys.version.split()[0], sys.platform, where,
            ''.join(traceback.format_exception(type(exc), exc, exc.__traceback__)))
        mode = 'a' if os.path.exists(ERROR_PATH) and os.path.getsize(ERROR_PATH) < 300000 else 'w'
        with open(ERROR_PATH, mode, encoding='utf-8') as f:
            f.write(text)
    except Exception:
        pass


def _load_token():
    saved = load_json(SESSION_PATH, {})
    tok = saved.get('token') if isinstance(saved, dict) else ''
    if not (isinstance(tok, str) and re.fullmatch(r'[A-Za-z0-9_-]{20,60}', tok)):
        tok = secrets.token_urlsafe(18)
        try:
            save_json(SESSION_PATH, {'token': tok})
        except OSError:
            pass  # cartella non scrivibile: il gettone vale solo per questo avvio
    return tok


TOKEN = _load_token()


def _ssl_context():
    """Certificati per i collegamenti sicuri. La verifica resta sempre attiva.
    A quelli del sistema si aggiunge l'elenco di Mozilla distribuito con il programma, perche' quelli del sistema spesso
    non bastano: Windows scarica le autorita' "al bisogno" e Python non sa chiederle (errore "unable to get local issuer
    certificate"); il Python di python.org su Mac non ne ha finche' non si esegue "Install Certificates"."""
    ctx = ssl.create_default_context()
    extra = []
    if os.path.exists(CA_BUNDLE):
        extra.append(CA_BUNDLE)
    else:  # il file non c'e' (cartella copiata a meta'): si prova con l'elenco che Python porta con se'
        for mod in ('certifi', 'pip._vendor.certifi'):
            try:
                extra.append(__import__(mod, fromlist=['where']).where())
                break
            except Exception:
                pass
    for path in ('/etc/ssl/cert.pem', '/private/etc/ssl/cert.pem', '/etc/ssl/certs/ca-certificates.crt', '/etc/pki/tls/certs/ca-bundle.crt'):
        if os.path.exists(path):
            extra.append(path)
            break
    for path in extra:
        try:
            ctx.load_verify_locations(cafile=path)
        except Exception:
            pass
    return ctx


SSL_CTX = _ssl_context()
_TLS = {'ctx': SSL_CTX, 'tried': False}
_TLS_LOCK = threading.Lock()


def _cert_refused(e):
    return isinstance(e, ssl.SSLCertVerificationError) or isinstance(getattr(e, 'reason', None), ssl.SSLCertVerificationError)


def _native_tls(failed):
    """Dopo un certificato rifiutato: passa, una volta sola, alla verifica fatta dal sistema operativo (Windows e Mac sanno
    procurarsi da soli i certificati che mancano). Resta una verifica vera, mai un collegamento alla cieca.
    Vero se c'e' un contesto diverso da quello che ha fallito, con cui riprovare."""
    with _TLS_LOCK:
        if _TLS['ctx'] is not failed:
            return True
        if _TLS['tried']:
            return False
        _TLS['tried'] = True
        try:
            from pip._vendor import truststore  # arriva insieme a pip nel Python per Windows e Mac
            ctx = truststore.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        except Exception:
            return False
        _TLS['ctx'] = ctx
        return True


def with_tls(call):
    """Esegue call(contesto). Se il certificato viene rifiutato, riprova una volta con la verifica del sistema operativo."""
    ctx = _TLS['ctx']
    try:
        return call(ctx)
    except Exception as e:
        if _cert_refused(e) and _native_tls(ctx):
            return call(_TLS['ctx'])
        raise


# ---- aggiornamento automatico --------------------------------------------------
# Il programma chiede a un indirizzo fisso se c'e' una versione nuova. Se c'e', scarica i file in una cartella a parte, controlla
# che siano interi (dimensione e impronta SHA-256 scritte nell'elenco), li prova avviandoli a vuoto, e solo allora li mette al
# posto di quelli vecchi (che restano in "_precedente") e si riavvia. Se qualcosa non torna, resta la versione di prima.
# I file di avvio (Avvia.bat, avvia.command) non vengono mai toccati: stanno girando mentre il programma lavora.
UPDATE_URL = (os.environ.get('CV_UPDATE_URL') or 'https://raw.githubusercontent.com/Marco112344/cercaveicoli/main/').rstrip('/') + '/'
UPDATE_FILES = ('server.py', 'index.html', 'LEGGIMI.txt', 'cacert.pem')
UPDATE_NEW = os.path.join(APP_DIR, '_nuova')
UPDATE_OLD = os.path.join(APP_DIR, '_precedente')
RESTART_CODE = 75  # codice di uscita che dice al file di avvio: "riavviami"
UPD = {'state': 'fermo', 'version': '', 'note': '', 'msg': '', 'from': '', 'when': 0}
UPD_LOCK = threading.Lock()
STARTED = time.time()


def _ver(v):
    return tuple(int(x) for x in re.findall(r'\d+', str(v))[:4])


def auto_update_on():
    if os.environ.get('CV_NO_UPDATE'):
        return False
    return load_json(CONFIG_PATH, {}).get('autoUpdate') is not False


def _download(url, limit=6000000, timeout=20):
    """Scarica un file dell'aggiornamento (solo https, oppure l'indirizzo di prova)."""
    if not (url.startswith('https://') or os.environ.get('CV_UPDATE_URL')):
        raise ValueError('indirizzo non sicuro')
    req = urlreq.Request(url, headers={'User-Agent': UA, 'Accept-Encoding': 'identity', 'Cache-Control': 'no-cache'})

    def go(ctx):
        with urlreq.build_opener(urlreq.HTTPSHandler(context=ctx)).open(req, timeout=timeout) as r:
            data = r.read(limit + 1)
            if len(data) > limit:
                raise ValueError('file troppo grande')
            return data
    return with_tls(go)


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _read_manifest(raw):
    """Controlla l'elenco dell'aggiornamento: versione, e per ogni file dimensione e impronta."""
    m = json.loads(raw.decode('utf-8'))
    if not isinstance(m, dict) or not _ver(m.get('version')) or not isinstance(m.get('files'), dict):
        raise ValueError('elenco non valido')
    files = {}
    for name, info in m['files'].items():
        if name not in UPDATE_FILES or not isinstance(info, dict):
            continue  # nomi non previsti (per esempio i file di avvio) non si scaricano
        sha, size = str(info.get('sha256') or '').lower(), info.get('size')
        if not re.fullmatch(r'[0-9a-f]{64}', sha) or not isinstance(size, int) or not 0 < size <= 6000000:
            raise ValueError('elenco non valido per ' + name)
        files[name] = {'sha256': sha, 'size': size}
    if 'server.py' not in files or 'index.html' not in files:
        raise ValueError('elenco incompleto')
    return {'version': '.'.join(str(x) for x in _ver(m['version'])), 'files': files, 'note': str(m.get('note') or '')[:300]}


def _pending():
    """L'aggiornamento gia' scaricato e controllato che aspetta di essere installato, oppure None."""
    try:
        with open(os.path.join(UPDATE_NEW, 'versione.json'), 'rb') as f:
            m = _read_manifest(f.read())
        if _ver(m['version']) <= _ver(VERSION) or not os.path.exists(os.path.join(UPDATE_NEW, 'pronta')):
            return None
        for name, info in m['files'].items():
            with open(os.path.join(UPDATE_NEW, name), 'rb') as f:
                data = f.read()
            if len(data) != info['size'] or _sha(data) != info['sha256']:
                return None
        return m
    except (OSError, ValueError):
        return None


def prepare_update():
    """Cerca una versione nuova e la prepara in "_nuova". Restituisce l'elenco se e' pronta, None se non c'e' nulla di nuovo."""
    raw = _download(UPDATE_URL + 'versione.json?t=%d' % int(time.time() // 120), limit=20000, timeout=10)
    m = _read_manifest(raw)
    if _ver(m['version']) <= _ver(VERSION):
        return None
    ready = _pending()
    if ready and ready['version'] == m['version']:
        return ready
    with UPD_LOCK:
        UPD.update({'state': 'scarico', 'version': m['version'], 'note': m['note']})
    shutil.rmtree(UPDATE_NEW, ignore_errors=True)
    os.makedirs(UPDATE_NEW, exist_ok=True)
    for name, info in m['files'].items():
        data = _download(UPDATE_URL + name + '?v=' + m['version'])
        if len(data) != info['size'] or _sha(data) != info['sha256']:
            raise ValueError('il file %s non corrisponde all\'elenco' % name)
        with open(os.path.join(UPDATE_NEW, name), 'wb') as f:
            f.write(data)
    for name in UPDATE_FILES:  # i file che l'aggiornamento non porta restano quelli di adesso, anche per la prova
        if name not in m['files'] and os.path.exists(os.path.join(APP_DIR, name)):
            shutil.copyfile(os.path.join(APP_DIR, name), os.path.join(UPDATE_NEW, name))
    with open(os.path.join(UPDATE_NEW, 'server.py'), 'r', encoding='utf-8') as f:
        src = f.read()
    with open(os.path.join(UPDATE_NEW, 'index.html'), 'r', encoding='utf-8') as f:
        page = f.read()
    compile(src, 'server.py', 'exec')
    if ("VERSION = '%s'" % m['version']) not in src or ("var PAGE_V = '%s'" % m['version']) not in page:
        raise ValueError('i file scaricati non sono della versione %s' % m['version'])
    # prova a vuoto della versione nuova, con lo stesso Python: se non parte, non la si installa
    env = dict(os.environ, CV_NO_BROWSER='1', CV_NO_UPDATE='1')
    r = subprocess.run([sys.executable, os.path.join(UPDATE_NEW, 'server.py'), '--prova'], capture_output=True, timeout=90, env=env, cwd=UPDATE_NEW)
    if r.returncode != 0 or ('PROVA OK ' + m['version']).encode() not in r.stdout:
        raise ValueError('la versione %s non supera la prova di avvio' % m['version'])
    with open(os.path.join(UPDATE_NEW, 'versione.json'), 'wb') as f:
        f.write(raw)
    with open(os.path.join(UPDATE_NEW, 'pronta'), 'w') as f:
        f.write(m['version'])
    return m


def install_update(m):
    """Mette i file nuovi al posto dei vecchi (che restano in "_precedente"). Vero se e' andata bene."""
    names = [n for n in UPDATE_FILES if n in m['files']]
    names.sort(key=lambda n: n == 'server.py')  # il programma per ultimo: se qualcosa va storto prima, resta quello vecchio
    shutil.rmtree(UPDATE_OLD, ignore_errors=True)
    os.makedirs(UPDATE_OLD, exist_ok=True)
    done = []
    try:
        for name in names:
            cur = os.path.join(APP_DIR, name)
            if os.path.exists(cur):
                shutil.copyfile(cur, os.path.join(UPDATE_OLD, name))
        for name in names:
            os.replace(os.path.join(UPDATE_NEW, name), os.path.join(APP_DIR, name))
            done.append(name)
    except OSError as e:
        for name in done:  # si torna indietro: mai una cartella con file di due versioni
            try:
                shutil.copyfile(os.path.join(UPDATE_OLD, name), os.path.join(APP_DIR, name))
            except OSError:
                pass
        log_error('installazione dell\'aggiornamento', e)
        return False
    save_json(os.path.join(data_dir(), 'aggiornato.json'), {'from': VERSION, 'to': m['version'], 'when': time.time()})
    shutil.rmtree(UPDATE_NEW, ignore_errors=True)
    return True


def restart_program():
    """Riavvia il programma dopo un aggiornamento. Con il file di avvio basta uscire con il codice convenuto: ci pensa lui."""
    try:
        _shutdown_reader()
    except Exception:
        pass
    try:
        sys.stdout.flush()
    except Exception:
        pass
    if os.environ.get('CV_LOOP'):
        os._exit(RESTART_CODE)
    args = [sys.executable] + [a for a in sys.argv if a != '--prova']
    if os.name == 'nt':
        subprocess.Popen(args, cwd=APP_DIR, close_fds=True)
        os._exit(0)
    os.execv(sys.executable, args)


def _busy():
    with JOBS_LOCK:
        return any(not j.get('done') for j in JOBS.values())


def update_worker(delay=2.0):
    """In sottofondo, dopo l'avvio: cerca la versione nuova, la prepara e, se nessuno sta ancora cercando, la installa subito."""
    time.sleep(delay)
    with UPD_LOCK:
        if UPD['state'] in ('controllo', 'scarico', 'riavvio'):
            return
        UPD.update({'state': 'controllo', 'msg': ''})
    try:
        m = prepare_update()
    except Exception as e:
        kind = _net_error(e).kind if isinstance(e, (OSError, http.client.HTTPException, urlerr.URLError)) else ''
        with UPD_LOCK:
            UPD.update({'state': 'errore', 'when': time.time(),
                        'msg': 'Non riesco a raggiungere il sito degli aggiornamenti.' if kind else 'Aggiornamento non riuscito: %s' % str(e)[:120]})
        if not kind:
            log_error('aggiornamento', e)
        return
    with UPD_LOCK:
        UPD['when'] = time.time()
        if not m:
            UPD.update({'state': 'aggiornato', 'version': VERSION})
            return
        UPD.update({'state': 'pronta', 'version': m['version'], 'note': m['note']})
    with JOBS_LOCK:
        untouched = not JOBS
    if auto_update_on() and untouched:
        apply_update()


def apply_update():
    """Installa l'aggiornamento pronto e riavvia. Falso (con il motivo in UPD) se non si puo' adesso."""
    m = _pending()
    if not m:
        return False
    if _busy():
        with UPD_LOCK:
            UPD['msg'] = 'C\'e\' una ricerca in corso: l\'aggiornamento si installa appena finisce o al prossimo avvio.'
        return False
    with UPD_LOCK:
        UPD.update({'state': 'riavvio', 'version': m['version'], 'msg': ''})
    time.sleep(1.5)  # il tempo perche' la pagina legga "riavvio" e si metta ad aspettare
    if not install_update(m):
        with UPD_LOCK:
            UPD.update({'state': 'errore', 'msg': 'Non sono riuscito a sostituire i file: resta la versione di prima.'})
        return False
    save_json(os.path.join(data_dir(), 'riavvio.json'), {'when': time.time()})
    restart_program()
    return True


def update_status():
    with UPD_LOCK:
        d = dict(UPD)
    d.update({'current': VERSION, 'auto': auto_update_on(), 'off': bool(os.environ.get('CV_NO_UPDATE'))})
    return d


def self_test():
    """Prova a vuoto, usata prima di installare un aggiornamento: i file ci sono e il programma sa leggere una pagina."""
    for name in ('index.html', 'cacert.pem'):
        if not os.path.exists(os.path.join(APP_DIR, name)):
            print('manca ' + name)
            return 1
    with open(INDEX_PATH, 'r', encoding='utf-8') as f:
        if ("var PAGE_V = '%s'" % VERSION) not in f.read():
            print('pagina di un\'altra versione')
            return 1
    card = '<article><a href="/auto/annonce-%d-volkswagen-golf"><h3>Volkswagen Golf 1.5 TSI %d</h3></a><p>%d \u20ac</p><span>2020</span><span>%d km</span></article>'
    page = '<html><body>' + ''.join(card % (i, i, 15000 + i, 50000 + i) for i in (1, 2, 3)) + '</body></html>'
    items = extract_listings(page, 'https://esempio.fr/auto/volkswagen/golf/')
    if [(i['price'], i['km'], i['year']) for i in items] != [(15001, 50001, 2020), (15002, 50002, 2020), (15003, 50003, 2020)]:
        print('lettura di prova sbagliata')
        return 1
    _ssl_context()
    print('PROVA OK ' + VERSION)
    return 0


def get_config():
    cfg = load_json(CONFIG_PATH, {})
    key = os.environ.get('BRIGHTDATA_API_KEY') or cfg.get('apiKey') or ''
    return {'apiKey': key, 'zone': cfg.get('zone') or os.environ.get('BRIGHTDATA_UNLOCKER_ZONE') or '',
            'serpZone': cfg.get('serpZone') or os.environ.get('BRIGHTDATA_SERP_ZONE') or ''}


def adopt_old_config():
    """Se in questa versione non c'e' ancora una chiave, riprende quella salvata da una versione precedente (accanto al
    programma, oppure in un'altra cartella "Cercaveicoli..." vicina a questa). Restituisce da dove l'ha presa."""
    cur = load_json(CONFIG_PATH, {}) if os.path.exists(CONFIG_PATH) else {}
    if not isinstance(cur, dict):
        cur = {}
    if cur.get('apiKey'):
        return ''
    parent = os.path.dirname(APP_DIR)
    grand = os.path.dirname(parent)
    found = []
    for pat in (os.path.join(APP_DIR, 'config.json'), os.path.join(parent, 'Cercaveicoli*', 'config.json'),
                os.path.join(grand, 'Cercaveicoli*', 'config.json'), os.path.join(grand, 'Cercaveicoli*', 'Cercaveicoli*', 'config.json')):
        try:
            found += glob.glob(pat)
        except OSError:
            pass
    seen, ordered = set(), []
    for p in found:
        k = os.path.normcase(os.path.abspath(p))
        if k not in seen and k != os.path.normcase(os.path.abspath(CONFIG_PATH)):
            seen.add(k)
            ordered.append(p)
    try:
        ordered.sort(key=lambda p: -os.path.getmtime(p))
    except OSError:
        pass
    for p in ordered:
        old = load_json(p, {})
        if isinstance(old, dict) and old.get('apiKey'):
            merged = {'apiKey': old.get('apiKey'), 'zone': cur.get('zone') or old.get('zone') or '', 'serpZone': cur.get('serpZone') or old.get('serpZone') or ''}
            try:
                save_json(CONFIG_PATH, merged)
            except OSError:
                return ''
            return p
    return ''


def public_status(extra=None):
    cfg = get_config()
    out = {'ok': True, 'version': VERSION, 'boot': BOOT, 'hasKey': bool(cfg['apiKey']), 'keyTail': cfg['apiKey'][-4:] if cfg['apiKey'] else '',
           'zone': cfg['zone'], 'serpZone': cfg['serpZone'], 'reader': reader_status()}
    if extra:
        out.update(extra)
    return out


# --------------------------------------------------------------------------
# Bright Data
# --------------------------------------------------------------------------
class BDError(Exception):
    def __init__(self, msg, code=0):
        Exception.__init__(self, msg)
        self.code = code  # codice HTTP; -1 = Bright Data non raggiungibile, -2 = tempo scaduto


def _explain(code, body):
    body = (body or '').strip().replace('\n', ' ')[:160]
    if code in (401, 403):
        return 'Bright Data ha rifiutato la chiave o la zona (%d). %s' % (code, body)
    if code == 400:
        return 'Richiesta non accettata da Bright Data: controlla il nome della zona. %s' % body
    if code == 402:
        return 'Credito Bright Data esaurito.'
    if code == 404:
        return 'Pagina non trovata sul sito (404).'
    if code == 429:
        return 'Troppe richieste a Bright Data: riprova tra poco.'
    return 'Errore %d da Bright Data. %s' % (code, body)


def bd_request(cfg, url, zone=None, country=None, timeout=90):
    """Scarica una pagina tramite Bright Data (Web Unlocker o SERP). Restituisce il testo."""
    payload = {'zone': zone or cfg['zone'], 'url': url, 'format': 'raw'}
    if country:
        payload['country'] = country
    req = urlreq.Request(BD_BASE + '/request', data=json.dumps(payload).encode('utf-8'), method='POST',
                         headers={'Authorization': 'Bearer ' + cfg['apiKey'], 'Content-Type': 'application/json'})
    def go(ctx):
        with urlreq.urlopen(req, timeout=timeout, context=ctx) as resp:
            raw = resp.read()
            charset = resp.headers.get_content_charset() or 'utf-8'
            return raw.decode(charset, errors='replace')
    try:
        return with_tls(go)
    except urlerr.HTTPError as e:
        body = ''
        try:
            body = e.read().decode('utf-8', errors='replace')
        except Exception:
            pass
        raise BDError(_explain(e.code, e.headers.get('x-brd-error') or e.headers.get('x-luminati-error') or body), e.code)
    except urlerr.URLError as e:
        if isinstance(e.reason, (TimeoutError, socket.timeout)):
            raise BDError('Il sito non ha risposto in tempo.', -2)
        raise BDError('Non riesco a raggiungere Bright Data: %s' % e.reason, -1)
    except (TimeoutError, socket.timeout):
        raise BDError('Il sito non ha risposto in tempo.', -2)


def bd_check(cfg):
    """Controlla la chiave elencando le zone attive (non consuma crediti)."""
    if not cfg['apiKey']:
        return {'ok': False, 'msg': 'Manca la chiave API.'}
    req = urlreq.Request(BD_BASE + '/zone/get_active_zones', headers={'Authorization': 'Bearer ' + cfg['apiKey']})
    def go(ctx):
        with urlreq.urlopen(req, timeout=30, context=ctx) as resp:
            return json.loads(resp.read().decode('utf-8', errors='replace'))
    try:
        zones = with_tls(go)
    except urlerr.HTTPError as e:
        if e.code in (401, 403):
            return {'ok': False, 'badKey': True, 'msg': 'Bright Data non riconosce questa chiave API: non l\'ho salvata.'}
        return {'ok': False, 'msg': 'Chiave salvata, ma non riesco a leggere le zone (errore %d). Scrivi il nome della zona a mano.' % e.code}
    except ValueError:
        return {'ok': False, 'net': 'altro', 'msg': 'Chiave salvata, ma Bright Data ha risposto in modo inatteso: forse un filtro di rete si mette in mezzo. Riprova tra poco.'}
    except Exception as e:  # rete assente, certificato non accettato
        kind = _net_error(e).kind
        why = {'cert': "questo computer non accetta il collegamento sicuro con Bright Data (certificato). Controlla che data e ora del computer siano giuste. "
                       "Se c'è un antivirus che controlla i collegamenti protetti (voce «scansione HTTPS» o «scansione SSL»), prova a spegnere quella voce e riprova",
               'rete': "non trovo il sito di Bright Data. Controlla il collegamento a internet; se con il browser navighi, è l'antivirus o il firewall che blocca Python",
               'tempo': "Bright Data non ha risposto in tempo. Riprova tra poco",
               'firewall': "il firewall o l'antivirus di questo computer blocca il programma. Consenti a Python l'accesso a internet",
               'proxy': "questa rete esce su internet attraverso un proxy che il programma non può usare. Prova da un'altra rete"}.get(kind, 'il collegamento non è riuscito')
        return {'ok': False, 'net': kind, 'msg': 'Chiave salvata, ma non sono riuscito a verificarla: %s. (Dettaglio tecnico: %s)' % (why, str(getattr(e, 'reason', None) or e)[:140])}
    names = [(z.get('name'), z.get('type')) for z in zones if isinstance(z, dict)]
    # il tipo della zona Web Unlocker di solito e' "unblocker"; se Bright Data lo chiama in altro modo, vale il nome (es. cli_unlocker)
    unl = [n for n, t in names if str(t or '').lower() in ('unblocker', 'unlocker', 'web_unlocker')]
    if not unl:
        unl = [n for n, t in names if re.search(r'unlock|unblock', str(n or '') + ' ' + str(t or ''), re.I)]
    serp = [n for n, t in names if str(t or '').lower() == 'serp']
    return {'ok': True, 'zones': names, 'unlocker': unl, 'serp': serp,
            'msg': 'Chiave valida. Zone trovate: %s.' % (', '.join('%s (%s)' % nt for nt in names) or 'nessuna')}


# --------------------------------------------------------------------------
# Lettura diretta (gratuita)
# Il programma legge le pagine dal computer dell'utente, dichiara il proprio nome
# e rispetta il file robots.txt di ogni sito: se un sito non ammette la lettura
# automatica, non insiste e non lo aggira.
# --------------------------------------------------------------------------
class FetchError(Exception):
    """Il sito non e' raggiungibile. kind dice il tipo di problema, per poter dare un consiglio unico se riguarda tutti i siti."""

    def __init__(self, msg, kind='altro'):
        Exception.__init__(self, msg)
        self.kind = kind


def _net_error(e):
    detail = str(getattr(e, 'reason', None) or e)
    low = detail.lower()
    if 'certificate' in low or 'ssl' in low or 'tls' in low:
        kind, msg = 'cert', 'Collegamento sicuro non riuscito'
    elif any(x in low for x in ('getaddrinfo', 'name or service', 'nodename', 'name resolution', '11001', '11004', 'no address')):
        kind, msg = 'rete', 'Sito non trovato: sembra mancare il collegamento a internet'
    elif 'timed out' in low or 'timeout' in low:
        kind, msg = 'tempo', 'Il sito non ha risposto in tempo'
    elif any(x in low for x in ('10013', 'access permissions', 'permission denied', 'not permitted')):
        kind, msg = 'firewall', 'Collegamento impedito dal computer (firewall o antivirus)'
    elif 'proxy' in low or 'tunnel' in low:
        kind, msg = 'proxy', 'Collegamento rifiutato dal proxy di questa rete'
    elif any(x in low for x in ('refused', '10061', 'reset', '10054', 'unreachable', '10051', '10065', 'aborted', '10053')):
        kind, msg = 'rete', 'Collegamento interrotto'
    else:
        kind, msg = 'altro', 'Non riesco a collegarmi al sito'
    return FetchError('%s (%s).' % (msg, detail[:100]), kind)


NET_HINTS = {
    'cert': "Nessun sito è stato letto: questo computer non accetta i collegamenti sicuri del programma (certificati). Controlla che data e ora del computer siano giuste. "
            "Se c'è un antivirus che controlla i collegamenti protetti (voce «scansione HTTPS» o «scansione SSL»), prova a spegnere quella voce. "
            "Controlla anche che nella cartella del programma ci sia il file cacert.pem.",
    'rete': "Nessun sito è stato letto: il programma non riesce a uscire su internet. Controlla la connessione. Se con il browser navighi normalmente, "
            "è quasi certamente l'antivirus o il firewall che blocca Python: consentigli l'accesso a internet e riprova.",
    'firewall': "Nessun sito è stato letto: il firewall o l'antivirus di questo computer blocca il programma. Consenti a Python (python.exe) l'accesso a internet e riprova.",
    'proxy': "Nessun sito è stato letto: questa rete esce su internet attraverso un proxy che il programma non può usare. Prova da un'altra rete, per esempio usando il telefono come hotspot.",
    'tempo': "Nessun sito ha risposto in tempo: la connessione è molto lenta oppure bloccata. Riprova tra qualche minuto.",
    'altro': "Nessun sito è stato letto per un problema di collegamento. Premi «Scarica diagnostica» e manda il file a chi ti segue il programma.",
}


REFUSED = 'Il sito ha rifiutato la richiesta del programma, o ha chiesto una verifica: aprilo dal link.'
RULES = 'Le regole del sito escludono i programmi da questa pagina: aprila dal link.'
_HOST_LOCKS, _HOST_LAST, _ROBOTS, _ROBOTS_LOCKS = {}, {}, {}, {}
_GUARD = threading.Lock()


def _lock_for(table, key):
    with _GUARD:
        return table.setdefault(key, threading.Lock())


def _private_host(netloc):
    h = netloc.rsplit('@', 1)[-1]
    h = h[1:h.index(']')] if h.startswith('[') and ']' in h else h.split(':')[0]
    h = h.lower()
    if h in ('', 'localhost', '::1') or h.endswith(('.local', '.internal', '.lan')):
        return True
    if re.match(r'(127|10|0)\.|192\.168\.|169\.254\.|172\.(1[6-9]|2\d|3[01])\.', h):
        return True
    return ':' in h and h.startswith(('fc', 'fd', 'fe80'))


def _decode_body(raw, headers):
    enc = (headers.get('Content-Encoding') or '').lower()
    try:
        if 'gzip' in enc:
            raw = zlib.decompressobj(16 + zlib.MAX_WBITS).decompress(raw)
        elif 'deflate' in enc:
            try:
                raw = zlib.decompress(raw)
            except zlib.error:
                raw = zlib.decompressobj(-zlib.MAX_WBITS).decompress(raw)
    except zlib.error:
        pass
    charset = headers.get_content_charset()
    if not charset:
        m = re.search(rb'<meta[^>]+charset=["\']?([\w-]+)', raw[:4000], re.I)
        charset = m.group(1).decode('ascii', 'replace') if m else 'utf-8'
    try:
        return raw.decode(charset, errors='replace')
    except LookupError:
        return raw.decode('utf-8', errors='replace')


class _NoRedirect(urlreq.HTTPRedirectHandler):
    """I rinvii non si seguono alla cieca: li gestisce chi chiama, un passo alla volta."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def http_get(url, timeout=25, jar=None):
    """Legge una pagina, senza seguire i rinvii. Restituisce (codice, testo, indirizzo, indirizzo a cui il sito rimanda).
    jar = cookie della scansione in corso: un sito che ne assegna uno prima di rimandare alla pagina lo ritrova al passo dopo."""
    p = urlparse(url)
    host = p.netloc.lower()
    if p.scheme not in ('http', 'https') or (_private_host(host) and not TEST_ORIGIN):
        raise FetchError('Indirizzo non valido.')
    target = url.split('#', 1)[0]
    if TEST_ORIGIN:
        target = TEST_ORIGIN + '/' + host + (p.path or '/') + ('?' + p.query if p.query else '')
    with _lock_for(_HOST_LOCKS, host):
        wait = _HOST_LAST.get(host, 0) + DIRECT_GAP - time.time()
        if wait > 0:
            time.sleep(wait)
        req = urlreq.Request(target, headers={
            'User-Agent': UA, 'Accept': 'text/html,application/xhtml+xml;q=0.9,*/*;q=0.5',
            'Accept-Language': 'it-IT,it;q=0.9,en;q=0.6', 'Accept-Encoding': 'gzip, deflate'})
        cookies = jar if jar is not None else http.cookiejar.CookieJar()

        def go(ctx):
            opener = urlreq.build_opener(_NoRedirect, urlreq.HTTPSHandler(context=ctx), urlreq.HTTPCookieProcessor(cookies))
            with opener.open(req, timeout=timeout) as resp:
                raw = resp.read(8000000)
                return resp.status, _decode_body(raw, resp.headers), url, None
        try:
            return with_tls(go)
        except urlerr.HTTPError as e:
            try:
                body = _decode_body(e.read(200000), e.headers)
            except Exception:
                body = ''
            return e.code, body, url, (e.headers.get('Location') if e.headers else None)
        except (OSError, http.client.HTTPException, ValueError) as e:
            raise _net_error(e)
        finally:
            _HOST_LAST[host] = time.time()


def parse_robots(text):
    """Regole di robots.txt valide per questo programma: il gruppo con il suo nome, altrimenti quello generale (*)."""
    groups, cur, in_header = [], None, False
    for line in text.splitlines():
        line = line.split('#', 1)[0].strip()
        if ':' not in line:
            continue
        k, v = line.split(':', 1)
        k, v = k.strip().lower(), v.strip()
        if k == 'user-agent':
            if not in_header:
                cur = {'agents': [], 'rules': []}
                groups.append(cur)
                in_header = True
            cur['agents'].append(v.lower())
        elif k in ('allow', 'disallow'):
            in_header = False
            if cur is not None and v:
                cur['rules'].append((k == 'allow', v))
    mine = [g for g in groups if ROBOT_NAME in g['agents']] or [g for g in groups if '*' in g['agents']]
    return [r for g in mine for r in g['rules']]


def _robots_regex(pattern):
    anchored = pattern.endswith('$')
    if anchored:
        pattern = pattern[:-1]
    return re.compile(''.join('.*' if ch == '*' else re.escape(ch) for ch in pattern) + ('$' if anchored else ''))


def robots_can_fetch(rules, target):
    """Vince la regola piu' lunga; a pari lunghezza vince Allow. Nessuna regola = permesso."""
    best = None
    for allow, pat in rules:
        if _robots_regex(pat).match(target):
            cand = (len(pat), allow)
            if best is None or cand > best:
                best = cand
    return True if best is None else best[1]


def robots_allows(url):
    p = urlparse(url)
    origin = p.scheme + '://' + p.netloc.lower()
    with _lock_for(_ROBOTS_LOCKS, origin):
        hit = _ROBOTS.get(origin)
        if hit and time.time() - hit[0] < 3600:
            rules = hit[1]
        else:
            target = origin + '/robots.txt'
            for _hop in range(5):  # il file delle regole puo' essere stato spostato (da http a https, da un nome all'altro)
                code, text, _, loc = http_get(target, timeout=15)
                if code not in (301, 302, 303, 307, 308) or not loc:
                    break
                target = urljoin(target, loc)
            if code == 200:
                rules = parse_robots(text)
            elif code in (401, 403):
                rules = None  # il sito respinge del tutto questo programma
            elif 400 <= code < 500:
                rules = []  # nessun robots.txt: nessun divieto
            else:  # sito in errore: non si puo' sapere che cosa ammette, quindi non lo si legge
                raise FetchError('Il sito non risponde (errore %d).' % code)
            _ROBOTS[origin] = (time.time(), rules)
    if rules is None:
        return False
    return robots_can_fetch(rules, (p.path or '/') + ('?' + p.query if p.query else ''))


# --------------------------------------------------------------------------
# Lettura degli annunci da una pagina
#
# Regola di fondo: un dato vale solo se l'annuncio lo dichiara in modo esplicito
# (campo strutturato oppure etichetta a se' stante come "2019", "108.700 km",
# "Automatico"). Niente viene dedotto dal testo libero delle descrizioni, dove
# frasi come "TUV 03/2027" o "Klimaautomatik" porterebbero a letture sbagliate.
# --------------------------------------------------------------------------
NUM = r"\d{1,3}(?:[.,\s']\d{3})+|\d+"
CUR = r"(?:€|eur|euro)"
PRICE_TOKEN = re.compile(r"^(?:(?:prezzo|precio|prix|preis|price|al contado)\s*:?\s*)?(?:" + CUR + r"\s*)?(" + NUM + r")(?:[.,]\d{1,2}(?!\d)|,-|\.-)?\s*" + CUR
                         + r"?\s*(?:vb|v\.b\.|vhb|fp|ttc|tvac|\*|neg\.?|trattabili|negociable)?$")
KM_WORDS = r"(?:kilometerstand|kilometrage|kilometraje|kilometros|chilometraggio|chilometri|kilometer|mileage|tellerstand|km-stand|kms|km)"
KM_TOKEN = re.compile(r"^(?:" + KM_WORDS + r"\s*:?\s*)?(" + NUM + r")\s*(?:km|kms|km\.)$")
KM_LABELLED = re.compile(r"^" + KM_WORDS + r"\s*:?\s*(" + NUM + r")$")
KM_BARE = re.compile(r"^(" + NUM + r")$")
KM_LABELS = {'km', 'kms', 'kilometerstand', 'kilometrage', 'kilometraje', 'kilometros', 'chilometraggio', 'chilometri', 'kilometer', 'mileage', 'tellerstand', 'km-stand'}
# etichette che precedono l'anno di immatricolazione, e etichette che precedono altre date (revisione, garanzia, inserzione)
YEAR_LABELS = {'ez', 'erstzulassung', 'baujahr', 'bj', 'bj.', 'modelljahr', 'jahr', 'annee', 'annee modele', 'mise en circulation', 'date de mise en circulation',
               '1ere immatriculation', 'premiere immatriculation', 'anno', 'immatricolazione', 'prima immatricolazione', 'ano', 'matriculacion', 'ano de matriculacion',
               'fecha de matriculacion', 'year', 'registration', 'first registration', 'bouwjaar', 'mec'}
NOT_YEAR_LABELS = {'hu', 'tuv', 'au', 'hu/au', 'tuv/au', 'hu bis', 'tuv bis', 'hu neu', 'tuv neu', 'itv', 'proxima itv', 'ct', 'controle technique', 'prochain ct', 'revisione',
                   'prossima revisione', 'garantie', 'garantia', 'garanzia', 'garantie bis', 'date', 'datum', 'fecha', 'data', 'online seit', 'inserat online seit', 'eingestellt',
                   'publie le', 'publicado', 'pubblicato', 'disponible', 'disponibile', 'verfugbar ab', 'lieferung', 'livraison', 'entrega', 'consegna', 'bis', 'gultig bis'}
YEAR_TOKEN = re.compile(r"^(?:(?:ez|erstzulassung|bj\.?|baujahr|annee|anno|ano|year|mec|immatricolazione|matriculacion)\s*:?\s*)?"
                        r"(?:(?:0?[1-9]|1[0-2])\s?[/.\-]\s?)?((?:19[5-9]|20[0-3])\d)$")
MONTHLY_START = ('/mes', '/ mes', '/mois', '/ mois', '/monat', '/mese', '/month', 'al mes', 'par mois', 'mtl', 'pro monat', 'al mese', 'p.m.')
PRICE_LOOSE = re.compile(r"(?:(?:€|\beur\b|\beuro\b)\s*(?<!\d)(" + NUM + r"))|(?:(?<![\d\-−–])(" + NUM + r")(?:[.,]\d{1,2}(?!\d)|,-)?\s*(?:€|eur\b|euro\b))", re.I)
MONTHLY_RE = re.compile(r"^\s*(?:,-)?\s*(?:/|par |al |pro |a |im )?\s*(?:mois|mes|monat|mese|month|mtl|maand)", re.I)
SPLIT_RE = re.compile(r"\s*[•·|;]\s*|,\s+|\s+[-–—]\s+")
NAV_SEGMENTS = ('login', 'signin', 'register', 'account', 'compte', 'konto', 'cuenta', 'help', 'hilfe', 'aide', 'ayuda', 'contact',
                'kontakt', 'privacy', 'datenschutz', 'cookie', 'legal', 'impressum', 'cgu', 'agb', 'about', 'blog', 'magazin',
                'news', 'ratgeber', 'conseil', 'consejos', 'favori', 'merkzettel', 'compar', 'vendre', 'verkaufen', 'vender',
                'credit', 'assurance', 'versicherung', 'seguro', 'financ', 'm-einloggen', 'm-meine', 'vendez', 'cars-dealers', 'dealers',
                'haendler', 'vendeur', 'concesionario', 'agence', 'landing', 'marcas')
SOCIAL_HOSTS = ('facebook.', 'instagram.', 'twitter.', 'youtube.', 'linkedin.', 'apple.com', 'play.google', 'tiktok.', 'pinterest.', 'whatsapp.')
ASSET_EXT = ('.jpg', '.jpeg', '.png', '.webp', '.gif', '.svg', '.css', '.js', '.ico', '.pdf')
# paese dichiarato nella scheda (aggregatori che riuniscono annunci di piu' paesi)
COUNTRY_TOKENS = {'germany': 'DE', 'deutschland': 'DE', 'allemagne': 'DE', 'alemania': 'DE', 'germania': 'DE', 'belgium': 'BE', 'belgique': 'BE', 'belgie': 'BE',
                  'belgien': 'BE', 'belgica': 'BE', 'belgio': 'BE', 'france': 'FR', 'frankreich': 'FR', 'francia': 'FR', 'spain': 'ES', 'espagne': 'ES',
                  'espana': 'ES', 'spanien': 'ES', 'spagna': 'ES', 'italy': 'IT', 'italie': 'IT', 'italia': 'IT', 'italien': 'IT', 'netherlands': 'NL',
                  'pays-bas': 'NL', 'nederland': 'NL', 'niederlande': 'NL', 'luxembourg': 'LU', 'luxemburg': 'LU', 'austria': 'AT', 'autriche': 'AT',
                  'osterreich': 'AT', 'switzerland': 'CH', 'suisse': 'CH', 'schweiz': 'CH', 'portugal': 'PT', 'poland': 'PL', 'pologne': 'PL', 'polen': 'PL'}
WANTED_TOKENS = {'gesuch', 'gesucht', 'recherche', 'se busca', 'cerco', 'wanted'}  # annunci di chi cerca, non di chi vende
GEAR_LABEL = {'A': 'Automatico', 'M': 'Manuale'}
FUEL_LABEL = {'D': 'Diesel', 'B': 'Benzina', 'H': 'Ibrida', 'E': 'Elettrica', 'L': 'GPL', 'C': 'Metano',
              'MB': 'Mild hybrid benzina', 'MD': 'Mild hybrid diesel', 'M': 'Mild hybrid'}


def to_int(s):
    d = re.sub(r'\D', '', str(s))
    return int(d) if d else None


def _plain(s):
    """Minuscole, senza accenti, spazi normalizzati."""
    s = unicodedata.normalize('NFD', str(s).replace(' ', ' ').replace(' ', ' ').replace(' ', ' '))
    s = ''.join(ch for ch in s if unicodedata.category(ch) != 'Mn').lower()
    return ' '.join(s.split())


def _compact(s):
    return re.sub(r'[^a-z0-9]', '', _plain(s))


def _year_from(v):
    if isinstance(v, bool) or v is None:
        return None
    if isinstance(v, (int, float)):
        return int(v) if 1950 <= v <= 2039 else None
    m = re.search(r'(?<!\d)((?:19[5-9]|20[0-3])\d)(?!\d)', str(v))
    return int(m.group(1)) if m else None


# ---- cambio e alimentazione ------------------------------------------------
GEAR_LABELS = {'cambio', 'tipo di cambio', 'getriebe', 'getriebeart', 'boite', 'boite de vitesse', 'boite de vitesses', 'transmission', 'transmision',
               'caja', 'caja de cambios', 'gearbox', 'versnellingsbak', 'schaltung'}
GEAR_PREFIX = re.compile(r'^(?:' + '|'.join(sorted((re.escape(x) for x in GEAR_LABELS), key=len, reverse=True)) + r')\s*:?\s*')
GEAR_AUTO = {'automatico', 'automatica', 'automatic', 'automatik', 'automatique', 'automaat', 'automat', 'automatisch', 'auto.', 'aut.', 'autom.',
             'boite automatique', 'boite auto', 'cambio automatico', 'automatikgetriebe', 'transmission automatique', 'automatica secuencial',
             'semiautomatico', 'semi-automatico', 'semiautomatica', 'semi-automatica', 'halbautomatik', 'semi-automatique', 'semiautomatic', 'semi-automatic',
             'automatizado', 'automatizzato', 'robotizzato', 'robotisee', 'sequenziale', 'tiptronic', 'dsg', 's tronic', 's-tronic', 'cvt', 'e-cvt',
             'automatic gearbox', 'automatic transmission', 'automatica robotizzata', 'automatique robotisee'}
GEAR_MAN = {'manuale', 'manual', 'manuell', 'manuelle', 'manuel', 'manueel', 'boite manuelle', 'schaltgetriebe', 'handgeschakeld', 'handschaltung', 'handgeschaltet',
            'cambio manuale', 'mecanique', 'mecanica', 'transmission manuelle', 'manual gearbox', 'manual transmission'}
FUEL_PREFIX = re.compile(r'^(?:carburant|carburante|kraftstoff|combustible|fuel|alimentazione|brandstof|energie|energia)\s*:?\s*')
FALSE_AUTO = re.compile(
    r'(?:start[- ]?stopp?[- ]?|licht[- ]?|klima[- ]?|einpark[- ]?|park[- ]?|fernlicht[- ]?|brems[- ]?|abstands[- ]?|sitz[- ]?|regen[- ]?)automatik'
    r'|(?:clima\w*|climatizzatore|climatisation|clim|climatizador|aire acondicionado|aria condizionata|air conditionne|fari|luci|feux|phares|luces|faros|freno|frein'
    r'|parcheggio|parking|aparcamiento|portellone|hayon|porton|tergicristalli|essuie[- ]glaces?|limpiaparabrisas|sensor\w*|capteur|retrovis\w*|allumage|encendido'
    r'|accensione|chiusura|fermeture|cierre)\s+(?:\w+\s+){0,2}automati\w+'
    r'|automatic\s+(?:climate|lights?|wipers?|headlights?|parking|tailgate|air|high beam)')
AUTO_HINT = re.compile(r'(?<![a-z0-9])(?:dsg\d?|s[- ]?tronic|tiptronic|steptronic|multitronic|\dg[- ]?tronic|g[- ]?tronic|geartronic|xtronic|powershift|pdk|edc\d?'
                       r'|dct\d?|dkg|eat\d|bva\d?|cvt|e-?cvt|aut\.|aut(?=[/ ]|$)|autom\.|automatik|automatikgetriebe|automatic[oa]?|automatique|automaat|boite auto|bte auto|cambio aut\w*|caja aut\w*)(?![a-z0-9])')
MAN_HINT = re.compile(r'(?<![a-z0-9])(?:bvm\d?|schaltgetriebe|schalter|handschalt\w*|handgeschakeld|manuale|manuell\w*|manual|boite manuelle|[56]-gang)(?![a-z0-9])')


def gear_label(text, structured=False):
    """Cambio da un'etichetta a se' stante ("Automatico", "Boite manuelle").
    "Auto" da solo vale soltanto in un campo del cambio ("Boite: Auto"), perche' altrove significa automobile."""
    raw = _plain(text or '')
    p = GEAR_PREFIX.sub('', raw)
    own = structured or p != raw
    for cand in (p.strip(' :'), p.strip(' .:')):
        if cand in GEAR_AUTO or (own and cand in ('auto', 'automatica', 'automatico')):
            return 'A'
        if cand in GEAR_MAN:
            return 'M'
    return None


def gear_hint(text):
    """Cambio da sigle tecniche nel titolo (DSG, S tronic, BVM6...). Ignora "Klimaautomatik" e simili."""
    t = FALSE_AUTO.sub(' ', _plain(text or ''))
    a, m = AUTO_HINT.search(t), MAN_HINT.search(t)
    if a and not m:
        return 'A'
    if m and not a:
        return 'M'
    return None


def fuel_label(text):
    """Alimentazione da un'etichetta breve ("Diesel", "Elettrica/Benzina", "Micro-hybride essence")."""
    t = FUEL_PREFIX.sub('', _plain(text or '')).strip(' .:')
    if not t or len(t) > 45 or len(t.split()) > 5 or re.search(r'\d', t.replace('100%', '').replace('100 %', '')):
        return None
    die = re.search(r'diesel|gasoil|gasoleo|gazole', t)
    pet = re.search(r'benzin|essence|gasolin|petrol|nafta', t)
    if re.search(r'micro|mild|mhev|leger|ligero', t) and re.search(r'h[iy]brid|ibrid|mhev', t):
        return 'MD' if die else ('MB' if pet else 'M')
    if re.search(r'h[iy]brid|ibrid|phev|plug|recharge|enchuf|elettric\w*\s?/|electri\w*\s?/|elektr\w*\s?/|/\s?elettric|/\s?electri|/\s?elektr', t):
        return 'H'
    if re.fullmatch(r'(?:100 ?% ?)?(?:elettric[ao]|electric|electrique|electric[ao]|elektro|elektrisch|strom|ev|bev)', t):
        return 'E'
    if re.search(r'(?<![a-z])(?:gpl|lpg|glp|autogas)(?![a-z])', t):
        return 'L'
    if re.search(r'(?<![a-z])(?:metano|cng|gnc|gnv|erdgas|aardgas)(?![a-z])', t):
        return 'C'
    if die and not pet:
        return 'D'
    if pet and not die:
        return 'B'
    return None


def fuel_hint(text):
    """Alimentazione da sigle tecniche nel titolo (TDI, TSI, 320d, eTSI, PHEV...)."""
    t = _plain(text or '')
    die = re.search(r'(?<![a-z])(?:tdi|hdi|bluehdi|dci|cdi|crdi|jtdm?|multijet|tdci|cdti|d-4d|sdi|diesel|gasoil|gtd)(?![a-z])|(?<![a-z0-9])(?:[a-z]{1,3})?\d{3}\s?d(?![a-z0-9])', t)  # 320d, e anche le sigle Mercedes attaccate: A180 d, C220d, GLC220 d
    pet = re.search(r'(?<![a-z])(?:tsi|tfsi|fsi|tce|puretech|ecoboost|gti|t-gdi|mpi|vti|benzin\w*|essence|gasolina)(?![a-z])|(?<![a-z0-9])\d{3}\s?i(?![a-z0-9])', t)
    if re.search(r'(?<![a-z])etsi(?![a-z])', t):
        return 'MB'
    if re.search(r'(?<![a-z])(?:mhev|mild)(?![a-z])', t):
        return 'MD' if die else ('MB' if pet else 'M')
    if re.search(r'(?<![a-z])(?:hybrid\w*|hibrid\w*|ibrid\w*|phev|e-?hybrid|plug-?in|rechargeable|gte)(?![a-z])', t):
        return 'H'
    if die and not pet:
        return 'D'
    if pet and not die:
        return 'B'
    return None


def fuel_ok(want, have):
    """True/False se l'alimentazione corrisponde o no; None se non si puo' dire."""
    if not want:
        return True
    if have is None:
        return None
    table = {'B': ('B', 'MB'), 'D': ('D', 'MD'), 'H': ('H', 'MB', 'MD', 'M'), 'E': ('E',), 'L': ('L',), 'C': ('C',)}
    if have in table.get(want, ()):
        return True
    if have == 'M' and want in ('B', 'D'):
        return None
    return False


# ---- carrozzeria ---------------------------------------------------------------
# Ogni marca chiama la station wagon a modo suo: nei titoli si riconosce da questi nomi.
BODY_WORDS = {
    'SW': r'sw|station ?wagon|wagon|avant|touring|variant|combi|kombi|break|estate|sports ?tourer|sportswagon|sportwagon|sport ?wagon|sportbrake|shooting ?brake|grandtour|t[ -]?modell|allroad|alltrack',
    'BE': r'limousine|lim|berline|berlina|sedan|saloon|stufenheck',
    'CA': r'cabrio|cabriolet|convertible|roadster|spider|spyder|decapotable|descapotable',
    'CO': r'coupe',
    'HB': r'sportback|hatchback|schragheck|compact',
}


def body_ok(want, title):
    """True se il titolo dichiara la carrozzeria richiesta, False se ne dichiara un'altra, None se non la dichiara."""
    if not want or want not in BODY_WORDS:
        return True
    t = _plain(title)
    has = lambda k: re.search(r'(?<![a-z0-9])(?:' + BODY_WORDS[k] + r')(?![a-z0-9])', t) is not None
    if has(want):
        return True
    if any(has(k) for k in BODY_WORDS if k != want):
        return False
    return None


# ---- corrispondenza con modello e parole chiave ------------------------------
# ---- potenza, IVA, venditore, danni, trazione, colore, dotazioni ---------------
# Valgono le stesse regole di cambio e alimentazione: conta solo quello che l'annuncio dichiara (dato strutturato,
# etichetta, oppure sigla nel titolo). Quello che non e' dichiarato resta "non indicato", mai dedotto.
POWER_PAIR = re.compile(r'(?<![\d.,])(\d{2,3})\s?kw\s*[(/|,;-]?\s*\(?\s*(\d{2,4})\s?(?:ps|cv|ch|hp|pk|bhp)\b')
POWER_HP = re.compile(r'(?<![\d.,/])(\d{2,4})\s?(?:ps|cv|ch|hp|pk|bhp|cavalli|chevaux|caballos)\b(?!\s*fisc)')
POWER_KW = re.compile(r'(?<![\d.,])(\d{2,3})\s?kw\b(?!h)')


def power_from(text):
    """Potenza in CV dichiarata nel testo ("110 kW (150 PS)", "150 CV", "110 kW"), oppure None."""
    p = _plain(text or '')
    if not p:
        return None
    m = POWER_PAIR.search(p)
    if m and 40 <= int(m.group(2)) <= 1600:
        return int(m.group(2))
    for m in POWER_HP.finditer(p):
        if 'fisc' in p[max(0, m.start() - 22):m.start()]:
            continue  # cavalli fiscali, non potenza
        if 40 <= int(m.group(1)) <= 1600:
            return int(m.group(1))
    m = POWER_KW.search(p)
    if m and 30 <= int(m.group(1)) <= 1200:
        return int(round(int(m.group(1)) * 1.35962))
    return None


VAT_NEG = re.compile(r'(?:nicht\s+ausweisbar|ohne\s+mwst|differenzbesteuer\w*|(?:§|par\.?)\s?25\s?a|25a\s+ustg|iva\s+non\s+(?:deducibile|detraibile|esposta|esponibile)|'
                     r'tva\s+non\s+(?:recup\w*|deductible)|sans\s+tva|iva\s+no\s+deducible|sin\s+iva\s+deducible|regimen\s+(?:especial\s+)?de\s+bienes\s+usados|\brebu\b|'
                     r'regime\s+del\s+margine|margeregeling|marge\s?auto|marge\s?wagen|btw\s+niet\s+(?:aftrekbaar|verrekenbaar)|regime\s+de\s+la\s+marge|tva\s+sur\s+(?:la\s+)?marge)')
VAT_POS = re.compile(r'(?:mwst\.?\s*(?:ist\s+)?ausweisbar|ausweisbare\s+mwst|inkl\.?\s*\d{1,2}(?:[.,]\d)?\s?%\s*mwst|\d{1,2}(?:[.,]\d)?\s?%\s*mwst|zzgl\.?\s*mwst|\+\s?mwst|'
                     r'iva\s+(?:deducibile|detraibile|esposta|esponibile)|\+\s?iva\b|tva\s+(?:recup\w*|deductible)|prix\s+ht\b|hors\s+taxes?|iva\s+deducible|precio\s+sin\s+iva|'
                     r'btw\s+(?:aftrekbaar|verrekenbaar)|btw[- ]auto|btw[- ]wagen|excl\.?\s*btw|ex\.?\s*btw|vat\s+(?:deductible|reclaimable|qualifying|recov\w*))')


def vat_hint(text):
    """True se l'annuncio dichiara l'IVA detraibile (esposta), False se dichiara il contrario, None se non dice nulla."""
    p = _plain(text or '')
    if VAT_NEG.search(p):
        return False
    return True if VAT_POS.search(p) else None


SELLER_D = re.compile(r'(?<![a-z0-9])(?:handler|haendler|gewerblich\w*|autohaus|professionnel\w*|concessionnaire|profesional|concesionario|handelaar|dealer|concessionario|concessionaria|rivenditore)(?![a-z0-9])')
SELLER_P = re.compile(r'(?<![a-z0-9])(?:privat|privatanbieter|privatverkauf|von\s+privat|privatperson|particulier|particular|privato|private\s+seller|prive)(?![a-z0-9])')
SELLER_WORDS = {'pro': 'Concessionario', 'professional': 'Concessionario', 'professionnel': 'Concessionario', 'profesional': 'Concessionario', 'dealer': 'Concessionario',
                'business': 'Concessionario', 'trade': 'Concessionario', 'company': 'Concessionario', 'gewerblich': 'Concessionario', 'commercial': 'Concessionario',
                'haendler': 'Concessionario', 'handler': 'Concessionario', 'entreprise': 'Concessionario', 'bedrijf': 'Concessionario', 'concessionario': 'Concessionario',
                'private': 'Privato', 'privateseller': 'Privato', 'privat': 'Privato', 'particulier': 'Privato', 'particuliere': 'Privato', 'particular': 'Privato',
                'privato': 'Privato', 'individual': 'Privato', 'person': 'Privato', 'consumer': 'Privato'}


def seller_word(v):
    """Venditore da un valore strutturato ("Dealer", "pro", "PrivateSeller")."""
    return SELLER_WORDS.get(_compact(v), '')


def seller_hint(text):
    p = _plain(text or '')
    d, pr = bool(SELLER_D.search(p)), bool(SELLER_P.search(p))
    return 'Concessionario' if d and not pr else ('Privato' if pr and not d else '')


DMG_NEG = re.compile(r'(?<![a-z0-9])(?:unfall\s?frei\w*|unfallfreiheit|kein\w*\s+unfall\w*|ohne\s+unfall\w*|nicht\s+unfall\w*|kein\w*\s+(?:motor|getriebe|vor)?schaden|ohne\s+(?:motor|getriebe|vor)?schaden|'
                     r'kein\w*\s+defekt\w*|ohne\s+defekt\w*|kein\w*\s+mangel|non\s+accidente\w*|jamais\s+accidente\w*|pas\s+accidente\w*|sans\s+accident\w*|aucun\s+accident\w*|'
                     r'sin\s+accidentes?|sin\s+siniestros?|sin\s+golpes?|nunca\s+siniestrad\w*|no\s+siniestrad\w*|libre\s+de\s+(?:siniestros|accidentes|golpes|cargas)|'
                     r'schade\s?vrij\w*|geen\s+schade\w*|zonder\s+schade\w*|ongeval\s?vrij\w*|non\s+incidentat\w*|mai\s+incidentat\w*|senza\s+incident\w*|senza\s+danni|senza\s+sinistri|'
                     r'mai\s+sinistrat\w*|accident[- ]free|no\s+accidents?|never\s+(?:been\s+)?(?:damaged|crashed)|not\s+damaged|no\s+damage)(?![a-z0-9])')
DMG_POS = re.compile(r'(?<![a-z0-9])(?:unfall\w*|unfaller|motorschaden|getriebeschaden|totalschaden|wasserschaden|brandschaden|hagelschaden|frontschaden|heckschaden|seitenschaden|'
                     r'turboschaden|kupplungsschaden|blechschaden|defekt\w*|beschadigt\w*|nicht\s+fahrbereit|bastler\w*|accidente\w*|en\s+panne|pour\s+pieces|epave|non\s+roulant\w*|'
                     r'moteur\s+hs|boite\s+hs|embrayage\s+hs|turbo\s+hs|a\s+reparer|siniestr\w*|averiad\w*|para\s+piezas|para\s+despiece|motor\s+roto|golpead\w*|schadeauto|'
                     r'schadewagen|motorschade|met\s+schade|ongevalwagen|niet\s+rijdbaar|rijdt\s+niet|incidentat\w*|sinistrat\w*|danneggiat\w*|non\s+marciante|per\s+ricambi|motore\s+fuso|'
                     r'da\s+riparare|damaged|accident\s+damage\w*|for\s+parts|engine\s+failure|not\s+running|salvage|motor\s?defe[ck]t|engine\s+damage)(?![a-z0-9])')


def damage_hint(text):
    """True se l'annuncio dichiara un incidente, un danno o un guasto (e non il contrario: "unfallfrei", "sin golpes")."""
    p = DMG_NEG.sub(' ', _plain(text or ''))
    return bool(DMG_POS.search(p))


AWD_POS = re.compile(r'(?<![a-z0-9])(?:4x4|4wd|awd|awd-i|e-awd|4\s?motion|4matic\+?|4-matic|xdrive\w*|x-drive\w*|quattro|allrad\w*|vierradantrieb|all[- ]?wheel(?:[- ]drive)?|'
                     r'trazione\s+integrale|integrale|4\s?ruote\s+motrici|(?:quatre|4)\s?roues\s+motrices|transmission\s+integrale|traccion\s+(?:total|integral|4x4)|'
                     r'all4|4drive|4xe|e[- ]four|sh-awd|s-awc|allgrip|4x4i|allroad|alltrack|vierwielaandrijving|4-wielaandrijving)(?![a-z0-9])')
AWD_NEG = re.compile(r'(?<![a-z0-9])(?:4x2|2wd|fwd|rwd|sdrive\w*|frontantrieb|vorderradantrieb|heckantrieb|hinterradantrieb|traction\s+avant|propulsion|deux\s+roues\s+motrices|'
                     r'2\s?roues\s+motrices|trazione\s+(?:anteriore|posteriore)|traccion\s+(?:delantera|trasera)|voorwielaandrijving|achterwielaandrijving|front[- ]wheel|rear[- ]wheel)(?![a-z0-9])')


def drive_hint(text):
    """True = trazione integrale dichiarata, False = due ruote motrici dichiarate, None = non indicata."""
    p = _plain(text or '')
    if AWD_POS.search(p):
        return True
    return False if AWD_NEG.search(p) else None


# colore: le parole che compaiono anche nei nomi degli allestimenti ("Black Edition", "BlueMotion", "Red Line") non contano
_TRIM_AFTER = r'(?!\s*-?\s*(?:edition|line|pack|paket|package|style|optic|optik|week|series|sky|motion|hdi|tec|efficiency|drive|dci|tdi|perf|label|star|magic|ink|vision|wing))'
COLOR_RX = {
    'nero': r'(?:nero|nera|schwarz\w*|noir\w*|negro|negra|zwart\w*|black' + _TRIM_AFTER + r')',
    'bianco': r'(?:bianco|bianca|weiss\w*|blanc|blanche|blanco|blanca|wit|witte|white' + _TRIM_AFTER + r')',
    'grigio': r'(?:grigio|grigia|grau\w*|gris|grise|grijs\w*|grey|gray|antracite|anthrazit\w*|anthracite)',
    'argento': r'(?:argento|silber\w*|argent|plata|plateado|zilver\w*|silver' + _TRIM_AFTER + r')',
    'blu': r'(?:blu|azzurro|blau\w*|bleu\w*|azul\w*|blauw\w*|blue' + _TRIM_AFTER + r')',
    'rosso': r'(?:rosso|rossa|rot|rote[rsn]?|rouge|rojo|roja|rood|rode|red' + _TRIM_AFTER + r')',
    'verde': r'(?:verde|grun\w*|gruen\w*|vert|verte|groen\w*|green)',
    'giallo': r'(?:giallo|gialla|gelb\w*|jaune|amarillo|amarilla|geel|gele|yellow)',
    'marrone': r'(?:marrone|braun\w*|marron|brun|brune|bruin\w*|brown)',
    'beige': r'(?:beige)',
    'arancione': r'(?:arancione|arancio|naranja|oranje|orange)',
    'oro': r'(?:oro|dorado|dore|gold' + _TRIM_AFTER + r')',
    'bronzo': r'(?:bronzo|bronze|bronce)',
    'lilla': r'(?:lilla|viola|violett\w*|lila|violet|morado|paars|purple)'}
COLOR_RE = dict((k, re.compile(r'(?<![a-z0-9])' + v + r'(?![a-z0-9])')) for k, v in COLOR_RX.items())


def color_hint(text):
    """Colori dichiarati nel testo (nomi italiani), in ordine di comparsa."""
    p = _plain(text or '')
    hits = []
    for name, rx in COLOR_RE.items():
        m = rx.search(p)
        if m:
            hits.append((m.start(), name))
    return [n for _, n in sorted(hits)]


# dotazioni: come le chiamano gli annunci nelle varie lingue
EQUIP = {
    'tetto': ('tetto panoramico', r'pano|panorama\w*|panoram\w*|toit\s+(?:ouvrant\s+)?pano\w*|techo\s+(?:solar\s+)?panoram\w*|glasdach|panoramadak|tetto\s+panoram\w*'),
    'apribile': ('tetto apribile', r'schiebedach|schiebe-?dach|toit\s+ouvrant|techo\s+(?:solar|corredizo|practicable)|sunroof|tetto\s+apribile|tettuccio(?:\s+apribile)?|schuifdak|open\s+dak|panorama\w*schiebedach'),
    'pelle': ('interni in pelle', r'\w*leder\w*|cuir|cuero|piel|pelle|leather|lederen'),
    'navi': ('navigatore', r'navi\w*|gps|navegador'),
    'gancio': ('gancio traino', r'ahk|anhangerkupplung|anhaengerkupplung|anhangerkuppl\w*|attelage|enganche|bola\s+de\s+remolque|gancio(?:\s+(?:di\s+)?traino)?|trekhaak|tow\s?bar'),
    'sedilirisc': ('sedili riscaldati', r'sitzheizung|shz|sieges\s+chauffants|asientos\s+calefactables|asientos\s+calefactados|sedili\s+riscaldat\w*|stoelverwarming|heated\s+seats'),
    'hud': ('head-up display', r'head[- ]?up(?:[- ]display)?|hud|affichage\s+tete\s+haute'),
    'acc': ('cruise control adattivo', r'acc|abstandstempomat|abstandsregel\w*|adaptive\s+cruise(?:\s+control)?|regulateur\s+adaptatif|control\s+de\s+crucero\s+adaptativo|cruise\s+(?:control\s+)?adattivo|distronic\w*'),
    'carplay': ('Apple CarPlay', r'carplay|car\s+play|apple\s+car\w*'),
    'android': ('Android Auto', r'android\s+auto'),
    'camera': ('telecamera', r'ruckfahrkamera|rueckfahrkamera|kamera|camera(?:\s+de\s+recul)?|camara(?:\s+trasera)?|telecamera|retrocamera|achteruitrijcamera|rfk'),
    'cam360': ('telecamera 360', r'360\s?(?:°|grad)?\s*(?:kamera|camera|camara)?|surround\s+view|area\s+view|top\s+view'),
    'xenon': ('fari xeno', r'xenon|bi-?xenon|xeno'),
    'led': ('fari LED', r'led|voll-?led|full\s?led|matrix\w*|iq\.?\s?light'),
    'clima': ('clima automatico', r'klimaautomatik|klimaaut\w*|clim(?:atisation)?\s+auto\w*|climatizador|clima\s+automatico|climatizzatore\s+automatico|climate\s+control|bizona|bi-?zone|2-?zonen'),
    'portellone': ('portellone elettrico', r'elektr\w*\s+heckklappe|heckklappe\s+elektr\w*|hayon\s+(?:electrique|motorise)|porton\s+electrico|portellone\s+(?:posteriore\s+)?elettrico|elektrische\s+achterklep|power\s+tailgate'),
    'sedilisport': ('sedili sportivi', r'sportsitze?|sieges\s+sport|asientos\s+deportivos|sedili\s+sportivi|sportstoelen|sport\s+seats|recaro'),
    'volante': ('volante riscaldato', r'lenkradheizung|volant\s+chauffant|volante\s+calefactable|volante\s+calefactado|volante\s+riscaldato|stuurverwarming|heated\s+steering'),
    'pneumatiche': ('sospensioni pneumatiche', r'luftfederung|luftfahrwerk|suspension\s+pneumatique|suspension\s+neumatica|sospensioni\s+pneumatiche|luchtvering|air\s+suspension|airmatic'),
    'webasto': ('riscaldamento ausiliario', r'standheizung|webasto|chauffage\s+(?:additionnel|stationnaire|auxiliaire)|calefaccion\s+(?:auxiliar|estatica)|riscaldamento\s+(?:ausiliario|supplementare)|standkachel'),
    'keyless': ('apertura senza chiave', r'keyless(?:\s+(?:go|entry|access))?|kessy|acces\s+mains\s+libres|mains\s+libres|acceso\s+sin\s+llave|senza\s+chiave'),
    'oscurati': ('vetri oscurati', r'getonte\s+scheiben|abgedunkelte\s+scheiben|privacy(?:\s+glass|verglasung)?|vitres\s+(?:sur)?teintees|cristales\s+(?:tintados|oscurecidos)|vetri\s+(?:oscurati|scuri)|getint\w*\s+glas'),
    'ventilati': ('sedili ventilati', r'sitzbeluftung|sitzklima|klimasitze?|sieges\s+ventiles|asientos\s+ventilados|sedili\s+ventilati|stoelventilatie|ventilated\s+seats'),
    'sensori': ('sensori di parcheggio', r'pdc|einparkhilfe|parksensor\w*|park\s?distance(?:\s+control)?|radars?\s+de\s+(?:recul|stationnement)|aide\s+au\s+stationnement|sensores?\s+de\s+aparcamiento|sensori\s+(?:di\s+)?parcheggio|parkeersensoren|parking\s+sensors?|parktronic'),
    'cockpit': ('strumentazione digitale', r'virtual\s+cockpit|digital\s+cockpit|cockpit\s+(?:digital\w*|virtuel\w*)|digitales?\s+(?:cockpit|kombiinstrument)|active\s+info(?:\s+display)?|quadro\s+strumenti\s+digitale|interamente\s+digitale|i-?cockpit'),
}
EQUIP_RE = dict((k, re.compile(r'(?<![a-z0-9])(?:' + v[1] + r')(?![a-z0-9])')) for k, v in EQUIP.items())
OWNER1_RE = re.compile(r'(?<![a-z0-9])(?:unico\s+proprietario|uniproprietario|1\s?\.?\s?hand|erste[rn]?\s+hand|1\.\s?hd|premiere\s+main|1\s?(?:ere|re)\s+main|primera\s+mano|unico\s+dueno|'
                       r'un\s+solo\s+dueno|unico\s+propietario|1\s+eigenaar|1e\s+eigenaar|eerste\s+eigenaar|one\s+owner|1\s+owner|first\s+owner)(?![a-z0-9])')
SEATS_RE = re.compile(r'(?<![a-z0-9])(\d)\s?-?\s?(?:posti|sitzer|sitze|sitzplatze|places|plazas|seater|seats|zits|zitplaatsen|zitter|pl)(?![a-z0-9])')


DOORS_RE = re.compile(r'(?<![a-z0-9])(?:([2-5])\s?-?\s?(?:porte|turig|tuerig|turer|tuerer|trg|portes|puertas|deurs|doors)|([35])p)(?![a-z0-9])')


def seats_hint(text):
    m = SEATS_RE.search(_plain(text or '').replace('siebensitzer', '7 sitzer'))
    return int(m.group(1)) if m and 2 <= int(m.group(1)) <= 9 else None


FAMILY = {'serie', 'classe', 'klasse', 'class', 'clase', 'model', 'range', 'grand', 'santa', 'land'}
ROMAN_N = {'i': 1, 'ii': 2, 'iii': 3, 'iv': 4, 'v': 5, 'vi': 6, 'vii': 7, 'viii': 8, 'ix': 9, 'x': 10}
ROMAN = set(ROMAN_N)
GLUE_PREFIX = {'blue', 'e', 'eco', 'bi', 'twin', 'multi'}  # "hdi" vale anche per BlueHDi, "tsi" per eTSI
# lettere che si attaccano solo a certe parole: xDrive, sDrive, S line. Non a tutte: una Kia XCeed non e' una Ceed
GLUE_PREFIX_ONLY = {'x': ('drive', 'line'), 's': ('drive', 'tronic', 'line')}
GLUE_SUFFIX = {'paket', 'pakket', 'pack', 'package', 'edition'}  # "sport" vale anche per Sportpaket
# allestimenti che portano il nome di una versione sportiva senza esserlo: M Sport, M Paket, AMG Line, AMG Styling
M_PACK = r'(?:sport|paket|pakket|technik|performance|aerodynamik)'
AMG_PACK = r'(?:paket|pakket|styling|sportpaket|optik|look|exterieur|interieur)'
# modelli in cui il numero fa parte del nome e non e' la generazione: "ioniq 5" non e' una Ioniq
NUMBER_NAMED = {'ioniq', 'atto'}
# sigle che insieme a una cifra fanno il nome del modello: ID.3, RS 3, EV6, MX-5
NAME_STEMS = {'id', 'rs', 'ev', 'mx', 'cx', 'sq', 'xc', 'eq', 'bz', 'ds'}
# dopo "golf 5" non deve seguire "porte", "Gang", "Jahre"...: allora il numero non e' la generazione
GEN_AFTER = (r'(?![a-z0-9])(?![.,])(?!\s*-?\s*(?:tur|tuer|trg|port|puert|door|deur|sitz|post|plac|plaz|gang|speed|vitess|march|hand|jahr|year|ans|anos|anni|monat|mesi|mois'
             r'|zon|fach|zyl|cil|cyl|schl|key|kw|ps|cv|ch|x|p|v|er))')
UNIT_AFTER = r'(?!\s?(?:ps|cv|ch|kw|pk|hp|bhp|km|tkm|nm|€|eur))(?!\.\d{3})'


def _norm_compounds(plain):
    """"R-Line", "S line", "e-tron", "T-Roc" diventano una parola sola: cosi' "golf r" non vale per una Golf R-Line."""
    plain = re.sub(r'(?<![a-z0-9])r\.\s?s\.?(?![a-z0-9])', 'rs', plain)  # "R.S. Line"
    plain = re.sub(r'(?<![a-z0-9])(st|gt|rs|amg|[a-z])[\s-](line|tronic)(?![a-z0-9])', r'\1\2', plain)
    plain = re.sub(r'(?<![a-z0-9])gr[\s-]sport(?![a-z0-9])', 'grsport', plain)  # Toyota GR Sport non e' una GR
    plain = re.sub(r'(?<![a-z0-9])m[\s-](?=' + M_PACK + ')', 'm', plain)  # BMW M Sport, M Sportpaket, M Paket: non e' una M
    plain = re.sub(r'(?<![a-z0-9])amg[\s-](?=' + AMG_PACK + ')', 'amg', plain)  # AMG Styling, AMG Paket: non e' una AMG
    return re.sub(r'(?<![a-z0-9-])([a-z])-(?!klasse|class|clas)(?=[a-z]{2,})', r'\1', plain)


def _word_parts(plain):
    """Parole del testo, divise anche tra lettere e cifre: "2.0tdi" -> 2 | 0, tdi; "320d" -> 320, d."""
    toks = re.findall(r'[a-z0-9]+', plain)
    parts = []
    for ti, tok in enumerate(toks):
        sub = re.findall(r'[a-z]+|\d+', tok)
        for si, x in enumerate(sub):
            parts.append((x, ti, si == 0, si == len(sub) - 1))
    return toks, parts


def _glued(tok, ck):
    """ck dentro una parola composta: BlueHDi, eTSI, xDrive, Sportpaket, M Sport."""
    if tok == ck:
        return False
    for pre, pack in (('m', M_PACK), ('amg', AMG_PACK)):  # "msportpaket" (M Sportpaket) contiene "sport" e "sportpaket"
        rest = tok[len(pre):]
        if tok.startswith(pre) and rest and re.match(pack, rest) and (rest == ck or (rest.startswith(ck) and rest[len(ck):] in GLUE_SUFFIX)):
            return True
    if tok.endswith(ck):
        pre = tok[:-len(ck)]
        if pre in GLUE_PREFIX or ck in GLUE_PREFIX_ONLY.get(pre, ()):
            return True
    return tok.startswith(ck) and tok[len(ck):] in GLUE_SUFFIX and ck != 'amg'


def _has_run(ck, parts):
    """ck e' scritto nel testo come parola: da solo, attaccato a cifre ("golf7", "2.0tdi") o diviso in parole intere ("s max", "c 220 d")."""
    n = len(parts)
    for i in range(n):
        acc = ''
        for j in range(i, min(n, i + 5)):
            acc += parts[j][0]
            if not ck.startswith(acc):
                break
            if acc != ck:
                continue
            if parts[i][1] == parts[j][1]:
                return True
            tail = j + 1 < n and parts[j + 1][1] == parts[j][1] and parts[j][0].isdigit() and parts[j + 1][3] and len(parts[j + 1][0]) <= 2
            if parts[i][2] and (parts[j][3] or tail):
                return True
            break
    return False


def words_match(title, make, words, extra='', aliases=()):
    """True se l'annuncio contiene il modello e le parole richieste, come parole intere.
    `title` e' il titolo dell'annuncio; `extra` altro testo dove le parole possono comparire (indirizzo, scheda).
    Se il titolo dichiara un'altra generazione o un'altra cilindrata rispetto a quelle richieste, non corrisponde."""
    tplain = _norm_compounds(_plain(title))
    plain = (tplain + ' ' + _norm_compounds(_plain(extra))).strip() if extra else tplain
    toks, parts = _word_parts(plain)
    tokens = set(toks)
    comp = ''.join(toks)
    mk = _plain(make or '')
    # la marca come puo' stare scritta nel titolo: il nome e le sue sigle ("volkswagen", "vw"; "ds automobiles", "ds")
    names = [x for x in [mk] + [_plain(a) for a in (aliases or ())] if re.search(r'[a-z0-9]', x)]
    mkpat = '|'.join(sorted(set(r'[\s-]?'.join(re.escape(x) for x in re.findall(r'[a-z0-9]+', nm)) for nm in names), key=len, reverse=True))
    mkpat = '(?:' + mkpat + ')' if mkpat else ''
    w = [x for x in _norm_compounds(' '.join(_plain(v) for v in (words or []))).split() if re.search(r'[a-z0-9]', x)]
    i, first, model, model0 = 0, True, '', ''
    while i < len(w):
        cur, nxt = w[i], (w[i + 1] if i + 1 < len(w) else None)
        ck = re.sub(r'[^a-z0-9]', '', cur)
        n2 = re.sub(r'[^a-z0-9]', '', nxt) if nxt else ''
        if cur in FAMILY and n2:
            ok = (cur + n2) in comp
            if 'bmw' in mk and cur == 'serie' and n2.isdigit():  # 320d, 330e, 3er, 3 Series, 3-serie, 3 Reeks: non "306 PS" ne' "12.320 EUR"
                ok = (ok or bool(re.search(r'(?<![a-z0-9.,])m?' + n2 + r'[1-6]\d' + UNIT_AFTER + r'(?:\s?[a-z]{1,2})?(?![a-z0-9])', plain))
                      or (n2 + 'er') in tokens or any(x in comp for x in ('series' + n2, n2 + 'serie', n2 + 'reeks', 'reeks' + n2, 'reihe' + n2)))
            elif 'bmw' in mk and cur == 'serie' and n2 in ('x', 'z', 'm'):  # serie X = X1...X7, serie Z = Z3, Z4, serie M = M2...M8
                ok = ok or bool(re.search(r'(?<![a-z0-9])' + n2 + r'\d(?![0-9])', plain))
            elif 'mercedes' in mk and cur in ('classe', 'klasse', 'class', 'clase'):
                ok = ok or bool(re.search(r'(?<![a-z0-9])' + re.escape(n2) + r'[ -]?\d{2,3}(?![0-9])', plain)) or any(
                    x in comp for x in (n2 + 'klasse', n2 + 'class', 'clase' + n2, 'classe' + n2, n2 + 'classe'))
            if not ok:
                return False
            i, first, model = i + 2, False, ''
            continue
        if not first and (re.fullmatch(r'\d', cur) or re.fullmatch(r'\d[.,]\d', cur) or (cur in ROMAN_N and cur != 'x')):
            if re.fullmatch(r'\d[.,]\d', cur):  # cilindrata
                seen = set(a + '.' + b for a, b in re.findall(r'(?<![\d.,])([0-6])[.,](\d)(?![.,]?\d)', tplain))
                if seen and cur.replace(',', '.') not in seen:
                    return False
            elif model:  # generazione: "golf 7" non e' "Golf VIII"
                want = ROMAN_N.get(cur) or int(cur)
                if model in NUMBER_NAMED and cur.isdigit():
                    if not re.search(r'(?<![a-z0-9])' + re.escape(model) + r'[\s-]*' + cur + r'(?![0-9])', plain):
                        return False
                else:
                    names = '|'.join(re.escape(x) for x in sorted(set((model, model0 or model))))
                    gens = [ROMAN_N.get(g) or int(g) for g in re.findall(
                        r'(?<![a-z0-9])(?:' + names + r')[\s-]*(viii|vii|vi|iv|ix|iii|ii|v(?!\s?(?:6|8|10|12)(?![0-9]))|[1-9])' + GEN_AFTER, tplain)]
                    if gens and want not in gens:
                        return False
            i += 1
            continue
        if n2:  # "c 220 d", "320 d", "x5 m", "s line", "m sport": valgono anche scritti attaccati
            cat, last, best, j = ck, ck, None, i + 1
            while j < len(w) and j <= i + 2:
                b = re.sub(r'[^a-z0-9]', '', w[j])
                if not b or not ((last.isalpha() and len(last) <= 3 and b[:1].isdigit()) or (len(b) == 1 and b.isalpha()) or (len(last) == 1 and last.isalpha() and b.isalpha())):
                    break
                cat, last = cat + b, b
                if _has_run(cat, parts):
                    best = j
                j += 1
            if best is not None:
                i, first, model = best + 1, False, ''
                continue
            if first and re.fullmatch(r'\d', n2) and (re.fullmatch(r'[a-z]', ck) or ck in NAME_STEMS):
                return False  # "id 3" non e' una ID.4, "rs 3" non e' una RS 5: qui il numero fa parte del nome
        joined = bool(mkpat) and re.search(r'(?<![a-z0-9])' + mkpat + r'[\s-]?' + re.escape(ck) + r'(?![a-z0-9])', plain) is not None  # "Mazda3"
        if re.fullmatch(r'\d[-/]\d', cur):  # Saab 9-3, 9-5
            hit = re.search(r'(?<![a-z0-9.,])' + cur[0] + r'[\s/-]?' + cur[2] + r'(?![a-z0-9])(?![.,]\d)', plain) is not None
        elif ck.isdigit():
            if len(ck) == 1:  # "mazda 3" non e' "CX-3", ne' una Mazda 6 "2.0", ne' una "5 porte"
                hit = joined or re.match(r'\s*' + ck + GEN_AFTER, tplain or plain) is not None
                if not hit and 'renault' in mk:  # "Renault R5"
                    hit = re.search(r'(?<![a-z0-9])r[\s-]?' + ck + r'(?![a-z0-9])', plain) is not None
            else:  # "500" non e' "500X"; "320" vale per 320d, 320i, 330e; "220" per C220d
                hit = joined or any(t == ck or re.fullmatch(r'(?:[a-z]{1,3})?' + ck + r'(?:[a-z]{1,2})?', t) and (t[:1].isalpha() or re.fullmatch(ck + r'(?:[diecs]|cc|sw)', t)) for t in toks)
        elif len(ck) == 1:
            hit = joined or re.search(r'(?<![a-z0-9-])' + ck + r'(?![a-z0-9-])', plain) is not None
        else:
            hit = joined or _has_run(ck, parts) or (ck.isalpha() and (len(ck) >= 3 or ck == 'up') and any(_glued(x[0], ck) for x in parts))
        if not hit:
            return False
        model = ck if ck.isalpha() and len(ck) >= 3 else ''
        model0 = model0 or model
        i, first = i + 1, False
    return True


# ---- modelli diversi con un nome simile ---------------------------------------
GEN_BETWEEN = r'[\s._-]*(?:(?:viii|vii|vi|iv|v|iii|ii|i|\d)[\s_-]+)?'
_SIB_CACHE = {}


def sibling_re(phrase):
    """Dal nome di un modello ("C3 Aircross", "Q8 * e-tron") l'espressione che lo riconosce in un titolo.
    L'asterisco vale per qualche parola in mezzo: "Q8 Sportback 55 e-tron"."""
    key = str(phrase)
    if key not in _SIB_CACHE:
        pat, gap = '', GEN_BETWEEN
        for word in _plain(key).split():
            if word == '*':
                gap = r'(?:[\s._-]+[a-z0-9.,]+){0,4}?[\s._-]+'
                continue
            bits = [re.escape(b) for b in re.findall(r'[a-z0-9]+', word)]
            if not bits:
                continue
            pat += (gap if pat else '') + r'[\s._-]*'.join(bits)
            gap = GEN_BETWEEN
        # dopo un numero ("Ioniq 5") non devono seguire porte o posti: "Ioniq 5-Tuerer" e' una Ioniq a cinque porte
        tail = r'(?![.,]\d)(?!\s*-?\s*(?:tur|tuer|trg|port|puert|door|deur|sitz|post|plac|plaz))' if pat[-1:].isdigit() else ''
        _SIB_CACHE[key] = re.compile(r'(?<![a-z0-9])' + pat + r'(?![a-z0-9])' + tail + r'(?![\s-]*(?:paket|pakket|pack|package))') if pat else None
    return _SIB_CACHE[key]


def sibling_hit(crit, text):
    """Nome del modello diverso (tra quelli da tenere fuori) che il testo dichiara, oppure ''."""
    names = crit.get('siblings')
    if not isinstance(names, list):
        return ''
    plain = _plain(text)
    for phrase in names[:40]:
        if not isinstance(phrase, str) or len(phrase) > 40:
            continue
        rx = sibling_re(phrase)
        if rx is not None and rx.search(plain):
            return str(phrase).replace(' *', '')
    return ''


# ---- indirizzi ---------------------------------------------------------------
def url_key(u):
    p = urlparse(u)
    q = '&'.join(x for x in p.query.split('&') if x and not x.lower().startswith(('utm_', 'gclid', 'fbclid')))
    return urlunparse((p.scheme, p.netloc.lower(), p.path.rstrip('/'), '', q, ''))


def _is_detail(href, base_url):
    if not href or href.startswith(('#', 'javascript:', 'mailto:', 'tel:')):
        return None
    full = urljoin(base_url, href.split('#', 1)[0])
    p, b = urlparse(full), urlparse(base_url)
    if p.scheme not in ('http', 'https') or p.path.lower().endswith(ASSET_EXT):
        return None
    if p.path.rstrip('/') == b.path.rstrip('/') or len(p.path) < 12:
        return None
    if any(h in p.netloc.lower() for h in SOCIAL_HOSTS):
        return None
    if any(seg.startswith(NAV_SEGMENTS) for seg in p.path.lower().split('/') if seg):  # pagine di servizio, non annunci
        return None
    return full


def _listing_url_ok(full, base_url):
    p, b = urlparse(full), urlparse(base_url)
    if p.scheme not in ('http', 'https') or p.path.lower().endswith(ASSET_EXT):
        return False
    return not (p.netloc.lower() == b.netloc.lower() and p.path.rstrip('/') == b.path.rstrip('/'))


def _clean_title(t):
    t = ' '.join(str(t or '').replace('•', ' ').replace(' ', ' ').split())
    words, out = t.split(' '), []
    for w in words:  # "Volkswagen Golf Golf 1.5 TSI" -> "Volkswagen Golf 1.5 TSI"
        if not out or out[-1].lower() != w.lower():
            out.append(w)
    half = len(out) // 2
    if half >= 2 and len(out) % 2 == 0 and [x.lower() for x in out[:half]] == [x.lower() for x in out[half:]]:
        out = out[:half]  # lo stesso titolo scritto due volte di seguito
    return ' '.join(out).strip(' -|')[:160]


# ---- foto degli annunci --------------------------------------------------------
# Il programma non scarica le foto: ne prende solo l'indirizzo dalla pagina dei risultati, e a mostrarle e' il browser.
IMG_EXT = re.compile(r'\.(?:jpe?g|webp|avif|png)(?:$|[?&#/!,_.])', re.I)
IMG_BAD = re.compile(r"(?<![a-z])(?:logos?|icons?|ico|pictos?|pictogram\w*|sprites?|placeholder|blank|spacer|pixel|badges?|flags?|avatar|loader|spinner|banners?|efficiencyclass"
                     r"|energy|energie|etiquetas?|etiquettes?|co2|emissions?|warranty|garantie|labels?|ratings?|stars?|markers?|payment|novisu|equipements?|sello|siegel)(?![a-z])"
                     r"|no[-_]?(?:image|photo|foto|img|picture|visuel)|default[-_](?:image|img|car|vehicle)|\.svg|\.gif", re.I)
IMG_GOOD = re.compile(r'vehic|veicol|fahrzeug|coche|voiture|photo|foto|thumb|gallery|galerie|listing|annonce|anzeige|vignette|cover|picture|bild|car[-_]image|image[-_]?car', re.I)
IMG_LAZY = ('data-src', 'data-lazy-src', 'data-original', 'data-lazy', 'data-url', 'data-image', 'data-img', 'data-full', 'data-echo', 'lazy-src')
IMG_KEYS = {'image', 'images', 'img', 'imgs', 'photo', 'photos', 'picture', 'pictures', 'thumbnail', 'thumbnails', 'thumb', 'cover', 'coverimage', 'mainimage', 'mainphoto',
            'imageurl', 'imageurls', 'pictureurl', 'photourl', 'thumbnailurl', 'gallery', 'media', 'medias', 'imagelist', 'fotos', 'foto', 'bilder', 'bild', 'mainpicture'}
IMG_SIZE_RANK = (('medium', 0), ('mid', 0), ('normal', 0), ('large', 2), ('big', 2), ('full', 2), ('original', 2), ('zoom', 2), ('xl', 2), ('small', 3), ('thumb', 4), ('tiny', 4), ('xs', 4))  # 1 = senza misura
MAX_PHOTOS = 6


def _img_url(u, base_url):
    """Indirizzo completo (http o https) di una foto, oppure ''."""
    if not isinstance(u, str):
        return ''
    u = html_unescape(u).strip()
    if not u or u[:5].lower() == 'data:' or len(u) > 900 or '<' in u or '"' in u:
        return ''
    m = re.search(r'(?<=[A-Za-z0-9])https?://', u[8:])
    if m:  # due indirizzi incollati per errore dal sito ("...vehicleshttps://cdn...jpg&w=321"): la foto e' il secondo
        u = u[8 + m.start():]
        if '?' not in u:
            u = u.split('&')[0]
    if u.startswith('//'):
        u = 'https:' + u
    try:
        u = urljoin(base_url, u)
    except ValueError:
        return ''
    if not u.lower().startswith(('http://', 'https://')):
        return ''
    return u.replace(' ', '%20')


def _srcset_pick(v):
    """Da un elenco "indirizzo larghezza, indirizzo larghezza" quello piu' vicino a 480 punti (basta per l'anteprima)."""
    best = None
    for part in re.split(r',\s+', str(v).strip()):
        bits = part.strip().split()
        if not bits or bits[0][:5].lower() == 'data:':
            continue
        w = 0
        if len(bits) > 1 and bits[-1][-1:] in 'wW' and bits[-1][:-1].isdigit():
            w = int(bits[-1][:-1])
        score = abs(w - 480) if w else 400
        if best is None or score < best[0]:
            best = (score, bits[0])
    return best[1] if best else ''


def _img_attr(tag, a):
    """L'indirizzo della foto fra gli attributi di <img> o <source>: prima quelli del caricamento ritardato, poi srcset, poi src."""
    if tag == 'img':
        for k in IMG_LAZY:
            v = a.get(k)
            if v and v[:5].lower() != 'data:':
                return v
    for k in ('data-srcset', 'data-lazy-srcset', 'srcset'):
        if a.get(k):
            u = _srcset_pick(a[k])
            if u:
                return u
    if tag != 'img':
        return ''
    for k, v in a.items():
        if k.startswith('data-') and isinstance(v, str) and ' ' not in v.strip() and v[:5].lower() != 'data:' and IMG_EXT.search(v):
            return v
    v = a.get('src') or ''
    return '' if v[:5].lower() == 'data:' else v


def _small(a):
    try:
        w, h = int(str(a.get('width') or '0').split('.')[0] or 0), int(str(a.get('height') or '0').split('.')[0] or 0)
    except ValueError:
        return False
    return 0 < w < 70 and 0 < h < 70


def _pick_photos(imgs, base_url, title='', href=''):
    """Le foto dell'auto fra le immagini di una scheda, la piu' probabile per prima; via loghi, bollini, etichette e icone."""
    words = set(w for w in re.findall(r'[a-z0-9]{3,}', _plain(title)) if w not in SLUG_GENERIC)
    slug = _compact(urlparse(href).path) if href else ''
    scored, seen = [], set()
    for n, (raw, alt, marks, small) in enumerate(imgs):
        u = _img_url(raw, base_url)
        if not u or u in seen:
            continue
        seen.add(u)
        pu = urlparse(u)
        where = (pu.path + '?' + pu.query).lower()
        if small or IMG_BAD.search(where) or IMG_BAD.search(marks or ''):
            continue
        score = 0
        aw = [w for w in re.findall(r'[a-z0-9]{3,}', _plain(alt or '')) if w not in SLUG_GENERIC]
        if aw and (any(w in words for w in aw) or (slug and any(w in slug for w in aw))):
            score += 3
        if re.search(r'\.(?:jpe?g|webp|avif)(?:$|[?&#/!,_.])', where):
            score += 1
        elif '.png' in where:
            score -= 2
        if IMG_GOOD.search((marks or '') + ' ' + where):
            score += 1
        if score >= 0:
            scored.append((-score, n, u, bool(aw)))
    scored.sort()
    if scored and -scored[0][0] >= 3:  # c'e' una foto il cui testo nomina l'auto: le immagini con un altro testo sono altro (promozioni, bollini)
        scored = [t for t in scored if -t[0] >= 3 or not t[3]]
    return [t[2] for t in scored][:MAX_PHOTOS]


def _html_images(seg, base_url, title='', href=''):
    """Le foto dentro un pezzo di pagina gia' isolato (una scheda)."""
    imgs = []
    for tag, body in re.findall(r'<(img|source)\b([^>]*)>', seg or '', re.I):
        a = dict((k.lower(), html_unescape(v)) for k, v in ATTR_RE.findall(body))
        raw = _img_attr(tag.lower(), a)
        if raw:
            imgs.append((raw, a.get('alt') or '', (a.get('class') or '').lower(), _small(a)))
    return _pick_photos(imgs, base_url, title, href)


def _state_images(d, base_url, depth=0, out=None):
    """Le foto dentro i dati di un annuncio: campi come images, photos, pictures, thumbnail (elenchi, testi o gruppi per misura)."""
    out = [] if out is None else out

    def add(v):
        u = _img_url(v, base_url)
        if u and u not in out and not IMG_BAD.search(urlparse(u).path.lower()) and len(out) < MAX_PHOTOS:
            out.append(u)

    def take(v, lv=0):
        if isinstance(v, str):
            if v.startswith(('http://', 'https://', '//')) or (v.startswith('/') and IMG_EXT.search(v)):
                add(v)
        elif isinstance(v, list) and lv < 3:
            for x in v[:12]:
                take(x, lv + 1)
        elif isinstance(v, dict) and lv < 3:
            ranked = []
            for k, x in v.items():
                nk = _norm_key(k)
                if isinstance(x, (dict, list)) or (isinstance(x, str) and (x.startswith(('http://', 'https://', '//')) or IMG_EXT.search(x))):
                    ranked.append((next((r for w, r in IMG_SIZE_RANK if w in nk), 1), len(ranked), x))
            ranked.sort(key=lambda t: t[:2])
            lists = [t for t in ranked if isinstance(t[2], list)]
            if lists:
                take(lists[0][2], lv + 1)   # le stesse foto in piu' misure ("urls", "urls_large", "urls_thumb"): basta un elenco
            elif ranked and all(isinstance(x, str) for _r, _i, x in ranked):
                take(ranked[0][2], lv + 1)  # lo stesso scatto in piu' misure: ne basta una
            else:
                for _r, _i, x in ranked:
                    take(x, lv + 1)

    if isinstance(d, dict) and depth <= 2:
        for k, v in d.items():
            if _norm_key(k) in IMG_KEYS:
                take(v)
        if not out:
            for k, v in d.items():
                if isinstance(v, dict) and len(v) <= 60:
                    _state_images(v, base_url, depth + 1, out)
                    if out:
                        break
    return out


def _ph(item, src, base_url):
    """Aggiunge all'annuncio le foto trovate nei suoi dati (gruppo di campi) o nel suo pezzo di pagina."""
    try:
        photos = _html_images(src, base_url, item.get('title'), item.get('url')) if isinstance(src, str) else _state_images(src, base_url)
    except Exception:
        photos = []
    if photos:
        item['img'], item['imgs'] = photos[0], photos
    return item


def _item(title, price, km, year, gear, fuel, url, src, txt='', **extra):
    it = {'title': _clean_title(title), 'price': price, 'km': km, 'year': year, 'gear': gear, 'fuel': fuel, 'url': url, 'src': src, '_txt': (txt or '')[:900]}
    it.update(extra)
    return it


# ---- siti di cui e' nota la struttura dei dati ---------------------------------
def _next_data(html):
    m = re.search(r'<script[^>]*id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.S)
    if not m:
        return None
    try:
        return json.loads(m.group(1))
    except ValueError:
        return None


AS24_ART = re.compile(r'<article\b([^>]*\bdata-guid="[^"]+"[^>]*)>', re.I)
ATTR_RE = re.compile(r'([a-zA-Z_:][-\w:.]*)\s*=\s*"([^"]*)"')
AS24_FUEL = {'b': 'B', 'd': 'D', 'e': 'E', 'l': 'L', 'c': 'C', '2': 'H', '3': 'H'}
AS24_CC = {'d': 'DE', 'b': 'BE', 'f': 'FR', 'e': 'ES', 'i': 'IT', 'a': 'AT', 'nl': 'NL', 'l': 'LU'}


def parse_autoscout24_dom(html, base_url):
    """AutoScout24 senza il blocco dati, come nella pagina copiata a mano. Le schede non hanno un link all'annuncio:
    prezzo, km, immatricolazione e alimentazione stanno negli attributi della scheda, e l'indirizzo si ricava dal suo codice.
    Il cambio non compare nelle schede: vale quello dichiarato nell'intestazione della pagina ("... cambio automatico ...")."""
    marks = list(AS24_ART.finditer(html))
    if not marks:
        return []
    h1 = re.search(r'<h1\b[^>]*>(.*?)</h1>', html[:marks[0].start()], re.S | re.I)
    h1 = _plain(re.sub(r'<[^>]+>', ' ', h1.group(1))) if h1 else ''
    page_gear = 'A' if 'cambio automatico' in h1 else ('M' if 'cambio manuale' in h1 else None)
    host = urlparse(base_url).netloc or 'www.autoscout24.it'
    out = []
    for i, m in enumerate(marks):
        a = dict((k.lower(), v) for k, v in ATTR_RE.findall(m.group(1)))
        seg = html[m.end():(marks[i + 1].start() if i + 1 < len(marks) else m.end() + 30000)]
        h2 = re.search(r'<h2\b[^>]*>(.*?)</h2>', seg, re.S | re.I)
        title = ' '.join(re.sub(r'<[^>]+>', ' ', h2.group(1)).split()) if h2 else ''
        title = title or ' '.join(x for x in (a.get('data-make', ''), a.get('data-model', '')) if x).title()
        fuel = AS24_FUEL.get(a.get('data-fuel-type', '').lower())
        if fuel is None:
            pill = re.search(r'data-testid="VehicleDetails-gas_pump"[^>]*>(.*?)</div>', seg, re.S | re.I)
            fuel = fuel_label(re.sub(r'<[^>]+>', ' ', pill.group(1))) if pill else None
        km = a.get('data-mileage', '')
        extra = {'gsrc': 'filtro della pagina'} if page_gear else {}
        out.append(_ph(_item(title, to_int(a.get('data-price')), int(km) if km.isdigit() else None, _year_from(a.get('data-first-registration')), page_gear, fuel,
                         'https://%s/annunci/%s' % (host, a['data-guid']), 'dati', title,
                         seller={'d': 'Concessionario', 'p': 'Privato'}.get(a.get('data-seller-type', '').lower(), ''), cc=AS24_CC.get(a.get('data-listing-country', '').lower(), ''), **extra), seg, base_url))
    return out


def parse_autoscout24(html, base_url):
    data = _next_data(html)
    try:
        listings = data['props']['pageProps']['listings']
    except (TypeError, KeyError):
        return parse_autoscout24_dom(html, base_url)
    out = []
    for l in listings or []:
        if not isinstance(l, dict) or not l.get('url'):
            continue
        v, t, p = l.get('vehicle') or {}, l.get('tracking') or {}, l.get('price') or {}
        price = p.get('priceRaw') if isinstance(p.get('priceRaw'), (int, float)) else (to_int(t.get('price')) or to_int(p.get('priceFormatted') or ''))
        km = to_int(t.get('mileage')) if str(t.get('mileage') or '').strip() != '' else to_int(v.get('mileageInKm') or '')
        base = ' '.join(str(x) for x in (v.get('make'), v.get('model'), v.get('modelVersionInput')) if x)
        have = set(re.findall(r'[a-z0-9]+', _plain(base)))
        extra = ' '.join(w for w in str(v.get('variant') or '').split() if not (set(re.findall(r'[a-z0-9]+', _plain(w))) <= have))
        title = ' '.join(str(x) for x in (v.get('make'), v.get('model'), extra, v.get('modelVersionInput')) if x) or l.get('title') or ''
        seller = seller_word((l.get('seller') or {}).get('type') or '')  # "Dealer" oppure "PrivateSeller"
        power = next((pw for pw in (power_from(d.get('data')) for d in (l.get('vehicleDetails') or []) if isinstance(d, dict)) if pw), None)
        extra = {'seller': seller, 'cc': str((l.get('location') or {}).get('countryCode') or '').upper(),
                 'dmg': bool(v.get('isCurrentlyDamaged')) or str(v.get('offerType') or '').upper() == 'A'}  # offerta di tipo A = incidentata
        if power:
            extra['power'] = power
        if str(p.get('priceSuperscriptString') or '') == '1':  # la nota 1 accanto al prezzo e' "IVA deducibile"
            extra['iva'] = True
        sub = str(v.get('subtitle') or '')
        out.append(_ph(_item(title, int(price) if price else None, km, _year_from(t.get('firstRegistration')), gear_label(v.get('transmission'), True), fuel_label(v.get('fuel')),
                         urljoin(base_url, l['url']), 'dati', (title + ' | ' + sub) if sub else title, **extra), l, base_url))
    return out


def parse_marktplaats(html, base_url):
    """2ememain.be, 2dehands.be (stessa piattaforma)."""
    data = _next_data(html)
    try:
        listings = data['props']['pageProps']['searchRequestAndResponse']['listings']
    except (TypeError, KeyError):
        return []
    out = []
    for l in listings or []:
        if not isinstance(l, dict) or not l.get('vipUrl'):
            continue
        attrs = {}
        for a in (l.get('attributes') or []) + (l.get('extendedAttributes') or []):
            if isinstance(a, dict) and a.get('key') and a.get('key') not in attrs:
                attrs[a['key']] = a.get('value')
        cents = (l.get('priceInfo') or {}).get('priceCents')
        price = int(cents // 100) if isinstance(cents, (int, float)) and cents > 0 else None
        adv = _plain(attrs.get('advertiser') or '')
        seller = 'Concessionario' if adv in ('entreprise', 'bedrijf', 'professionnel') else ('Privato' if adv in ('particulier', 'particuliere') else '')
        title = l.get('title') or ''
        out.append(_ph(_item(title, price, to_int(attrs['mileage']) if attrs.get('mileage') not in (None, '') else None, _year_from(attrs.get('constructionYear')),
                         gear_label(attrs.get('transmission'), True), fuel_label(attrs.get('fuel')), urljoin(base_url, l['vipUrl']), 'dati', title, seller=seller,
                         more=str(attrs.get('model') or '')), l, base_url))
    return out


def parse_willhaben(html, base_url):
    """willhaben.at: ogni annuncio e' un elenco di attributi con nome (HEADING, PRICE, MILEAGE, YEAR_MODEL, SEO_URL...)."""
    data = _next_data(html)
    try:
        ads = data['props']['pageProps']['searchResult']['advertSummaryList']['advertSummary']
    except (TypeError, KeyError):
        return []
    out = []
    for ad in ads or []:
        if not isinstance(ad, dict):
            continue
        at = {}
        for a in ((ad.get('attributes') or {}).get('attribute') or []):
            if isinstance(a, dict) and a.get('name') and isinstance(a.get('values'), list) and a['values']:
                at.setdefault(str(a['name']), a['values'][0])
        seo = str(at.get('SEO_URL') or '')
        if not seo:
            continue
        num = lambda k: _num(at.get(k)) if at.get(k) not in (None, '') else None
        price, km, kw = num('PRICE'), num('MILEAGE'), num('ENGINE/EFFECT')
        title = str(at.get('HEADING') or ad.get('description') or '')
        extra = {'seller': {'1': 'Privato', '0': 'Concessionario'}.get(str(at.get('ISPRIVATE')), '')}
        cc = COUNTRY_TOKENS.get(_plain(at.get('COUNTRY') or ''))
        if cc:
            extra['cc'] = cc
        if kw and 20 <= kw <= 1200:
            extra['power'] = int(round(kw * 1.35962))
        item = _item(title, int(price) if price else None, int(km) if km is not None else None, _year_from(at.get('YEAR_MODEL')),
                     gear_label(str(at.get('TRANSMISSION_RESOLVED') or ''), True), fuel_label(str(at.get('ENGINE/FUEL_RESOLVED') or '')),
                     urljoin('https://www.willhaben.at/iad/', seo), 'dati', ' | '.join(x for x in (title, str(at.get('CONDITION_RESOLVED') or '')) if x), **extra)
        pics = [x for x in str(at.get('ALL_IMAGE_URLS') or '').split(';') if re.fullmatch(r'[\w/.-]{6,120}\.(?:jpe?g|png|webp)', x)][:MAX_PHOTOS]
        photos = ['https://cache.willhaben.at/mmo/' + re.sub(r'\.(jpe?g|png|webp)$', r'_hoved.\1', x) for x in pics]
        if not photos and re.match(r'https://cache\.willhaben\.at/mmo/[\w/.-]+$', str(at.get('MMO') or '')):
            photos = [str(at['MMO'])]
        if photos:
            item['img'], item['imgs'] = photos[0], photos
        out.append(item)
    return out


def parse_cochescom(html, base_url):
    data = _next_data(html)
    try:
        listings = data['props']['pageProps']['classifieds']['classifiedList']
    except (TypeError, KeyError):
        return []
    hrefs = {}
    for href, vid in re.findall(r'href="([^"]+\?id=([A-Za-z0-9_-]+))"', html):
        hrefs.setdefault(vid, href.replace('&amp;', '&'))
    name = lambda d: (d or {}).get('name') if isinstance(d, dict) else d
    out = []
    for l in listings or []:
        if not isinstance(l, dict):
            continue
        vid = l.get('visibleId')
        url = hrefs.get(vid)
        if not url:
            continue  # senza indirizzo dell'annuncio non serve a nulla
        make = str(name(l.get('make')) or '')
        title = ' '.join(x for x in (make.title() if make.isupper() and len(make) > 3 else make, name(l.get('model')), name(l.get('version'))) if x)
        price = (l.get('price') or {}).get('amount')  # prezzo in contanti ("al contado")
        km = (l.get('mileage') or {}).get('amount')
        dealer = (l.get('dealer') or {}).get('type')
        out.append(_ph(_item(title, int(price) if isinstance(price, (int, float)) and price > 0 else None, int(km) if isinstance(km, (int, float)) else None,
                         _year_from((l.get('registration') or {}).get('year')), gear_label(name(l.get('transmission')), True), fuel_label(name(l.get('fuel'))),
                         urljoin(base_url, url), 'dati', title, seller='Concessionario' if dealer else ''), l, base_url))
    return out


def parse_flexicar(html, base_url):
    data = _next_data(html)
    try:
        listings = data['props']['pageProps']['initialVehicles']
    except (TypeError, KeyError):
        return []
    out = []
    for l in listings or []:
        if not isinstance(l, dict) or not l.get('slug'):
            continue
        title = ' '.join(str(x) for x in (l.get('brand'), l.get('model'), l.get('version')) if x)
        cash = l.get('cashPrice') if isinstance(l.get('cashPrice'), (int, float)) and l.get('cashPrice') else l.get('price')  # il prezzo "price" vale solo con finanziamento
        out.append(_ph(_item(title, int(cash) if isinstance(cash, (int, float)) and cash > 0 else None, int(l['km']) if isinstance(l.get('km'), (int, float)) else None,
                         _year_from(l.get('year')), gear_label(l.get('transmission'), True), fuel_label(l.get('fuel')),
                         'https://www.flexicar.es/coches-ocasion/%s/' % l['slug'], 'dati', title, seller='Concessionario', iva=bool(l.get('taxDeductible'))), l, base_url))
    return out


SITE_PARSERS = (('autoscout24.', parse_autoscout24), ('2ememain.be', parse_marktplaats), ('2dehands.be', parse_marktplaats), ('marktplaats.nl', parse_marktplaats),
                ('coches.com', parse_cochescom), ('flexicar.es', parse_flexicar), ('willhaben.at', parse_willhaben))


# ---- dati schema.org (JSON-LD) -------------------------------------------------
LD_RE = re.compile(r'<script\b[^>]*type=["\']application/ld\+json["\'][^>]*>(.*?)</script>', re.S | re.I)
LD_TYPES = {'car', 'vehicle', 'product', 'motorvehicle', 'individualproduct', 'offer'}


def _ld_walk(node, base_url, out, depth=0):
    if depth > 12:
        return
    if isinstance(node, list):
        for x in node:
            _ld_walk(x, base_url, out, depth + 1)
        return
    if not isinstance(node, dict):
        return
    types = node.get('@type')
    types = [str(t).lower() for t in (types if isinstance(types, list) else [types]) if t]
    offers = node.get('offers')
    offers = offers[0] if isinstance(offers, list) and offers else offers
    if any(t in LD_TYPES for t in types) and isinstance(offers, dict) and 'offerCount' not in offers and 'highPrice' not in offers:
        price = offers.get('price')
        try:
            price = int(float(str(price).replace(',', '.'))) if price not in (None, '') else None
        except ValueError:
            price = to_int(price)
        url = node.get('url') or offers.get('url')
        if price and isinstance(url, str):
            mil = node.get('mileageFromOdometer')
            km = mil.get('value') if isinstance(mil, dict) else mil
            try:
                km = int(float(km)) if km not in (None, '') else None
            except (TypeError, ValueError):
                km = to_int(km)
            year = next((y for y in (_year_from(node.get(k)) for k in ('dateVehicleFirstRegistered', 'vehicleModelDate', 'productionDate', 'modelDate')) if y), None)
            extra = {}
            eng = node.get('vehicleEngine')
            eng = eng[0] if isinstance(eng, list) and eng else eng
            pw = (eng or {}).get('enginePower') if isinstance(eng, dict) else None
            if isinstance(pw, dict) and pw.get('value') not in (None, ''):
                unit = _plain(str(pw.get('unitCode') or '') + ' ' + str(pw.get('unitText') or ''))
                try:
                    val = float(str(pw['value']).replace(',', '.'))
                    cv = val * 1.35962 if ('kwt' in unit or 'kw' in unit.split()) else (val if re.search(r'bhp|n12|ps|cv|ch|hp|pk', unit) else None)
                    if cv and 40 <= cv <= 1600:
                        extra['power'] = int(round(cv))
                except ValueError:
                    pass
            who = node.get('seller') or offers.get('seller') or offers.get('offeredBy')
            if isinstance(who, dict):
                kind = _plain(str(who.get('@type') or ''))
                extra['seller'] = 'Privato' if kind == 'person' else ('Concessionario' if kind in ('autodealer', 'organization', 'localbusiness', 'automotivebusiness', 'corporation') else '')
            name = str(node.get('name') or '')
            brand = node.get('brand')
            brand = brand.get('name') if isinstance(brand, dict) else brand
            more = ' '.join(str(x) for x in (brand, node.get('model') if not isinstance(node.get('model'), dict) else node['model'].get('name')) if x)
            if isinstance(brand, str) and brand.strip() and name and _compact(brand) and _compact(brand) not in _compact(name):
                name = brand.strip() + ' ' + name
            out.append(_ph(_item(name, price, km, year, gear_label(node.get('vehicleTransmission'), True), fuel_label(node.get('fuelType')),
                             urljoin(base_url, url), 'dati', ' | '.join(str(x) for x in (name, node.get('description')) if x)[:900], more=more, **extra), {'image': node.get('image')}, base_url))
            return
    for v in node.values():
        if isinstance(v, (dict, list)):
            _ld_walk(v, base_url, out, depth + 1)


def extract_ld(html, base_url):
    out = []
    for body in LD_RE.findall(html):
        try:
            _ld_walk(json.loads(body.strip()), base_url, out)
        except ValueError:
            continue
    return out


# ---- dati contenuti nella pagina (siti che compongono la pagina nel browser) ----
# Molti siti tengono l'elenco degli annunci in un blocco di dati dentro la pagina. Qui lo si cerca senza conoscere il
# sito: un annuncio e' un gruppo di campi con un titolo, un prezzo, un indirizzo e almeno l'anno o i chilometri, e ogni
# dato si prende solo da un campo che dice che cosa contiene (nome del campo oppure unita' di misura nel valore).
SCRIPT_RE = re.compile(r'<script\b([^>]*)>(.*?)</script>', re.S | re.I)
ASSIGN_RE = re.compile(r'(?:window\.|self\.|globalThis\.|var\s+|let\s+|const\s+)?([A-Za-z_$][\w$]{2,48})\s*=\s*(JSON\.parse\(\s*)?(?=[\[{"])')
STATE_NAME = re.compile(r'^__\w+__$|state|props|data|store|payload|initial|preload|apollo|redux|search|result', re.I)
K_URL = ('url', 'link', 'href', 'permalink', 'relativeurl', 'detailurl', 'detailsurl', 'detailpageurl', 'vipurl', 'weburl', 'adurl', 'canonicalurl', 'seourl', 'publicurl',
         'listingurl', 'vehicleurl', 'offerurl', 'shareurl', 'absoluteurl', 'path', 'uri', 'weblink', 'deeplink')
K_TITLE = ('title', 'subject', 'headline', 'shorttitle', 'adtitle', 'vehicletitle', 'fulltitle', 'name', 'displayname', 'longtitle')
K_KM = ('mileage', 'mileagekm', 'mileageinkm', 'km', 'kms', 'kilometers', 'kilometres', 'kilometros', 'kilometraje', 'kilometrage', 'kilometer', 'odometer', 'laufleistung',
        'kilometerstand', 'chilometraggio', 'chilometri', 'mileagevalue', 'ml')
K_YEAR = ('year', 'regdate', 'firstregistration', 'firstregistrationdate', 'firstregistrationyear', 'registrationdate', 'registrationyear', 'constructionyear', 'modelyear',
          'buildyear', 'manufactureyear', 'manufacturingyear', 'yearofregistration', 'yearofmanufacture', 'anno', 'annee', 'ano', 'ez', 'erstzulassung', 'fr', 'vehicleyear',
          'registration', 'dateofregistration', 'circulationdate', 'miseencirculation', 'matriculacion')
K_GEAR = ('gearbox', 'gearboxtype', 'transmission', 'transmissiontype', 'gear', 'geartype', 'gearing', 'getriebe', 'boite', 'boitedevitesse', 'cambio', 'caja', 'tr')
K_FUEL = ('fuel', 'fueltype', 'fuelcategory', 'kraftstoff', 'carburant', 'combustible', 'energy', 'energie', 'alimentazione', 'ft')
K_HP = ('powerhp', 'powerps', 'powercv', 'horsepower', 'hp', 'ps', 'cv', 'horsepowerdin', 'puissancedin', 'powerinhp', 'powerinps', 'enginepowerhp', 'chevaux', 'caballos', 'potenciacv')
K_KW = ('powerkw', 'kw', 'powerinkw', 'enginepowerkw', 'leistungkw')
K_POWER = ('power', 'enginepower', 'leistung', 'puissance', 'potencia', 'potenza', 'pw')
K_SELLER = ('sellertype', 'ownertype', 'advertisertype', 'customertype', 'vendortype', 'sellerkind', 'advertiser', 'usertype', 'accounttype', 'type')
K_SELLER_BOOL = ('isprofessional', 'ispro', 'isdealer', 'professional', 'isprofessionalseller', 'pro')
K_VAT = ('vatdeductible', 'vatreclaimable', 'deductiblevat', 'taxdeductible', 'vehiclevat', 'ivadeducible', 'tvarecuperable', 'isvatdeductible', 'vatded', 'mwstausweisbar')
K_MAKE = ('make', 'brand', 'marque', 'marca', 'manufacturer', 'makename', 'brandname')
K_MODEL = ('model', 'modele', 'modelo', 'modell', 'modelname')
K_VERSION = ('version', 'variant', 'trim', 'finition', 'acabado', 'modelversion', 'versionname', 'subtitle')
PRICE_SEG = ('price', 'preis', 'prix', 'precio', 'prezzo')
PRICE_LEAF = ('price', 'priceraw', 'pricevalue', 'priceamount', 'amount', 'value', 'gross', 'grossamount', 'cashprice', 'saleprice', 'sellingprice', 'publicprice', 'finalprice',
              'currentprice', 'pricecents', 'priceincents', 'cents', 'preis', 'prix', 'precio', 'prezzo', 'consumerprice', 'consumerpricegross', 'raw')
PRICE_SKIP = ('month', 'mensual', 'mensuel', 'financ', 'rate', 'leasing', 'install', 'cuota', 'old', 'previous', 'before', 'original', 'strike', 'crossed', 'net', 'deposit',
              'evaluation', 'rating', 'drop', 'reduc', 'saving', 'discount', 'min', 'max', 'from', 'range', 'new', 'catalog', 'list', 'rrp', 'avg', 'average', 'market', 'estimate')
ATTR_SEG = ('attr', 'attrs', 'attributes', 'specs', 'details', 'keyfacts', 'characteristics', 'features', 'tags', 'vehicledetails', 'technicaldata', 'properties', 'criteria', 'highlights')
KM_VALUE = re.compile(r"^(\d{1,3}(?:[.\s,']\d{3})+|\d{1,7})\s?(?:km|kms)\.?$")
MONEY_VALUE = re.compile(r"^(?:€|eur)?\s?(\d{1,3}(?:[.\s,']\d{3})+|\d{3,7})(?:[.,]\d{2}|,-|\.-)?\s?(?:€|eur|euro)?$")


def _norm_key(k):
    return re.sub(r'[^a-z0-9]', '', _plain(k))


def _flat(d, prefix='', depth=0, out=None):
    """Campi di un gruppo, anche annidati (fino a tre livelli), come 'price.cashprice.value': valore."""
    out = {} if out is None else out
    for k, v in d.items():
        key = prefix + _norm_key(k)
        if isinstance(v, dict):
            if depth < 2 and len(v) <= 80:
                _flat(v, key + '.', depth + 1, out)
        elif isinstance(v, list):
            if v and all(not isinstance(x, (dict, list)) for x in v):
                out.setdefault(key, v[0])
            elif v and len(v) <= 60 and all(isinstance(x, dict) and len(x) <= 7 for x in v):  # elenco di coppie nome-valore
                for x in v:
                    name = next((x[n] for n in ('key', 'type', 'name', 'id', 'code', 'ariaLabel', 'label') if isinstance(x.get(n), str) and x.get(n)), None)
                    val = next((x[n] for n in ('value_label', 'valueLabel', 'text', 'displayValue', 'formattedValue', 'value', 'data', 'label')
                                if x.get(n) not in (None, '', []) and not isinstance(x.get(n), (dict, list)) and x.get(n) != name), None)
                    if name is not None and val is not None:
                        out.setdefault(key + '.' + _norm_key(name), val)
        else:
            out.setdefault(key, v)
    return out


def _pick(flat, names, test=None):
    """Primo valore il cui nome (ultimo tratto del percorso) e' tra quelli dati; i percorsi corti prima."""
    for path in sorted(flat, key=lambda p: (p.count('.'), len(p))):
        if path.rsplit('.', 1)[-1] in names:
            v = flat[path]
            if v not in (None, '') and (test is None or test(path, v)):
                return path, v
    return None, None


def _num(v):
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return float(v)
    t = _plain(v)
    if re.match(r'^\d+(?:\.\d+)?$', t):
        return float(t)
    return None


def _state_price(flat):
    best = None
    for path, v in flat.items():
        segs = path.split('.')
        leaf = segs[-1]
        if leaf not in PRICE_LEAF or not any(any(w in sg for w in PRICE_SEG) for sg in segs):
            continue
        if any(w in sg for sg in segs for w in PRICE_SKIP):
            continue
        n = _num(v)
        if n is None and isinstance(v, str):
            m = MONEY_VALUE.match(_plain(v))
            n = float(to_int(m.group(1))) if m else None
        if n is None:
            continue
        if 'cent' in leaf:
            n = n / 100.0
        if not 300 <= n <= 5000000:
            continue
        rank = (0 if any(w in path for w in ('cash', 'gross', 'consumer', 'contado')) else 1, len(segs), len(path))
        if best is None or rank < best[0]:
            best = (rank, int(n))
    return best[1] if best else None


def _state_item(d, base_url, ctx):
    flat = _flat(d)
    if len(flat) < 4:
        return None
    price = _state_price(flat)
    if price is None:
        return None
    _, url = _pick(flat, K_URL, lambda p, v: isinstance(v, str) and (v.startswith(('http://', 'https://', '/')) and len(v) >= 8) and not v.lower().endswith(ASSET_EXT))
    if not url:
        ident = next((str(flat[k]) for k in ('id', 'adid', 'listid', 'listingid', 'vehicleid', 'slug', 'webslug', 'visibleid') if flat.get(k) not in (None, '')), '')
        if len(ident) >= 5:
            if ctx.get('hrefs') is None:
                ctx['hrefs'] = [h.replace('&amp;', '&') for h in re.findall(r'href=["\']([^"\'#]+)', ctx['html'])]
            url = next((h for h in ctx['hrefs'] if ident in h), None)
    if not url:
        return None
    _, title = _pick(flat, K_TITLE, lambda p, v: isinstance(v, str) and 4 <= len(v.strip()) <= 220 and '.' not in p)
    make = _pick(flat, K_MAKE, lambda p, v: isinstance(v, str) and 2 <= len(v) <= 40)[1] or _pick(flat, ('name', 'label', 'valuelabel'), lambda p, v: isinstance(v, str) and p.split('.')[0] in K_MAKE)[1]
    model = _pick(flat, K_MODEL, lambda p, v: isinstance(v, str) and 1 <= len(v) <= 60)[1] or _pick(flat, ('name', 'label', 'valuelabel'), lambda p, v: isinstance(v, str) and p.split('.')[0] in K_MODEL)[1]
    version = _pick(flat, K_VERSION, lambda p, v: isinstance(v, str) and 1 <= len(v) <= 120)[1]
    if not title:
        if not (make and model):
            return None
        title = ' '.join(str(x) for x in (make, model, version) if x)
    km = year = gear = fuel = power = None
    kpath, kv = _pick(flat, K_KM)
    if kv is not None:
        n = _num(kv)
        km = int(n) if n is not None else (to_int(KM_VALUE.match(_plain(kv)).group(1)) if isinstance(kv, str) and KM_VALUE.match(_plain(kv)) else None)
        if km is not None and not 0 <= km <= 1500000:
            km = None
    ypath, yv = _pick(flat, K_YEAR, lambda p, v: _year_from(v) is not None)
    if yv is not None:
        year = _year_from(yv)
    gv = _pick(flat, K_GEAR, lambda p, v: isinstance(v, str) and gear_label(v, True))[1]
    gear = gear_label(gv, True) if gv else None
    fv = _pick(flat, K_FUEL, lambda p, v: isinstance(v, str) and fuel_label(v))[1]
    fuel = fuel_label(fv) if fv else None
    hv = _pick(flat, K_HP)[1]
    if hv is not None:
        n = _num(hv)
        power = int(n) if n is not None and 40 <= n <= 1600 else power_from(str(hv) if _num(hv) is None else '')
    if power is None:
        wv = _pick(flat, K_KW)[1]
        n = _num(wv) if wv is not None else None
        if n is not None and 30 <= n <= 1200:
            power = int(round(n * 1.35962))
    if power is None:
        pv = _pick(flat, K_POWER, lambda p, v: isinstance(v, str))[1]
        power = power_from(pv) if pv else None
    # valori che dicono da soli che cosa sono ("85.000 km", "180 kW (245 PS)", "Automatik"), dentro un elenco di caratteristiche
    for path, v in flat.items():
        segs = path.split('.')
        if len(segs) < 2 or not isinstance(v, str) or not any(sg in ATTR_SEG for sg in segs[:-1]):
            continue
        pv = _plain(v)
        if km is None and KM_VALUE.match(pv) and to_int(KM_VALUE.match(pv).group(1)) <= 1500000:
            km = to_int(KM_VALUE.match(pv).group(1))
        elif power is None and power_from(v):
            power = power_from(v)
        elif gear is None and len(pv) <= 30 and gear_label(v, True):
            gear = gear_label(v, True)
        elif fuel is None and len(pv) <= 30 and fuel_label(v):
            fuel = fuel_label(v)
    if km is None and year is None:
        return None  # senza anno ne' chilometri non e' riconoscibile come annuncio di un veicolo
    extra = {}
    sv = _pick(flat, K_SELLER, lambda p, v: isinstance(v, str) and seller_word(v) and (p.rsplit('.', 1)[-1] != 'type' or any(w in p for w in ('seller', 'owner', 'advertiser', 'dealer', 'vendor', 'user'))))[1]
    if sv:
        extra['seller'] = seller_word(sv)
    else:
        bv = _pick(flat, K_SELLER_BOOL, lambda p, v: isinstance(v, bool))[1]
        if bv is not None:
            extra['seller'] = 'Concessionario' if bv else 'Privato'
    vv = _pick(flat, K_VAT)[1]
    if isinstance(vv, bool) or (isinstance(vv, str) and _plain(vv) in ('true', 'false', '1', '0', 'yes', 'no')):
        extra['iva'] = vv if isinstance(vv, bool) else _plain(vv) in ('true', '1', 'yes')
    if power:
        extra['power'] = power
    more = ' '.join(str(x) for x in (make, model, version) if x)
    return _ph(_item(str(title).strip(), price, km, year, gear, fuel, urljoin(base_url, url), 'dati', str(title), more=more, **extra), d, base_url)


def _state_walk(node, base_url, out, ctx, depth=0):
    if depth > 18 or ctx['n'] > 80000:
        return
    ctx['n'] += 1
    if isinstance(node, list):
        for x in node:
            if isinstance(x, (dict, list)):
                _state_walk(x, base_url, out, ctx, depth + 1)
    elif isinstance(node, dict):
        if 4 <= len(node) <= 400:
            try:
                it = _state_item(node, base_url, ctx)
            except Exception:
                it = None
            if it:
                out.append(it)
                return
        for v in node.values():
            if isinstance(v, (dict, list)):
                _state_walk(v, base_url, out, ctx, depth + 1)


def extract_state(html, base_url):
    """Annunci letti dai blocchi di dati della pagina."""
    out, ctx, dec, budget = [], {'n': 0, 'html': html, 'hrefs': None}, json.JSONDecoder(), 12000000
    for attrs, body in SCRIPT_RE.findall(html):
        if len(body) < 300 or re.search(r'\bsrc\s*=', attrs) or 'ld+json' in attrs.lower():
            continue
        budget -= len(body)
        if budget < 0:
            break
        text = body.strip()
        roots = []
        if text[:1] in '{[':
            try:
                roots.append(json.loads(text))
            except ValueError:
                pass
        if not roots:
            for m in list(ASSIGN_RE.finditer(text))[:40]:
                if not STATE_NAME.search(m.group(1)):
                    continue
                try:
                    val, _ = dec.raw_decode(text, m.end())
                    if m.group(2) and isinstance(val, str):
                        val = json.loads(val)
                except ValueError:
                    continue
                if isinstance(val, (dict, list)):
                    roots.append(val)
        for r in roots:
            _state_walk(r, base_url, out, ctx)
    return out


# ---- schede nella pagina (HTML) ------------------------------------------------
VOID_TAGS = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}
SKIP_TAGS = {'script', 'style', 'noscript', 'svg', 'template', 'head', 'select', 'button'}
HEAD_TAGS = {'h1', 'h2', 'h3', 'h4', 'h5'}
STRIKE_TAGS = {'del', 's', 'strike'}
BLOCK_TAGS = {'article', 'li', 'section'}
CARD_WORDS = ('card', 'listing', 'result', 'vehicle', 'vehicule', 'annonce', 'anzeige', 'aditem', 'tile', 'teaser')
STRIKE_WORDS = ('line-through', 'strike', 'tachado', 'old-price', 'price-old', 'oldprice', 'barre', 'previousprice', 'previous-price', 'price-previous', 'was-price',
                'precio-anterior', 'prezzo-precedente', 'prix-initial')
HEAD_YEAR = re.compile(r"^(?:[a-z\u00e0-\u00ff.]{2,12}\s)?(?:(?:0?[1-9]|1[0-2])\s?[/.\-]\s?)?((?:19[5-9]|20[0-3])\d)$")  # "2022", "05/2018", "Auto. 2023"
SLUG_GENERIC = {'occasion', 'occasions', 'voiture', 'voitures', 'auto', 'autos', 'gebrauchtwagen', 'gebraucht', 'kaufen', 'coche', 'coches', 'segunda', 'mano', 'ocasion',
                'annonce', 'annonces', 'anzeige', 'anzeigen', 'used', 'car', 'cars', 'comprar', 'vehicule', 'vehicules', 'vehiculo', 'vehiculos', 'detail', 'details',
                'fahrzeug', 'fahrzeuge', 'vente', 'achat', 'usato', 'usate', 'html', 'www', 'tweedehands', 'occasie'}
VERSION_RE = re.compile(r'\d[.,]\d|(?<![a-z0-9])\d{2,3}\s?(?:cv|ch|ps|kw|hp|pk)(?![a-z])|(?<![a-z])(?:tdi|tsi|tfsi|hdi|bluehdi|dci|cdi|gti|gtd|gte|dsg|tce|crdi|jtd|mhev|phev|hybrid|etsi|tgi|amg)(?![a-z])')


class _Stream(HTMLParser):
    """Trasforma la pagina in una sequenza di testi, link e confini di scheda."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.items = []
        self.stack = []
        self.skip = 0
        self.head = 0
        self.head_id = 0
        self.ns = 0
        self.strike = 0
        self.glue = False
        self.space = False

    def handle_starttag(self, tag, attrs):
        self.glue = False
        if tag in SKIP_TAGS:
            self.skip += 1
            self.ns += tag == 'noscript'
            return
        if self.skip:
            if tag == 'img' and self.ns and self.skip == self.ns:  # la foto vera, dentro <noscript>, quando quella visibile si carica in ritardo
                self._image(tag, dict(attrs))
            return
        if tag == 'li':
            for e in reversed(self.stack):
                if e[0] in ('ul', 'ol'):
                    break
                if e[0] == 'li':
                    self.handle_endtag('li')
                    break
        a = dict(attrs)
        marks = ' '.join(str(a.get(k) or '') for k in ('class', 'data-testid', 'data-test', 'data-obs')).lower()
        block = tag in BLOCK_TAGS or (tag == 'div' and any(w in marks for w in CARD_WORDS))
        head = tag in HEAD_TAGS
        strike = tag in STRIKE_TAGS or any(w in marks for w in STRIKE_WORDS)
        if tag == 'a' and a.get('href'):
            self.items.append(('a', a['href']))
        elif tag == 'img' and a.get('alt'):
            self.items.append(('t', ' '.join(a['alt'].split()), False, False, True))
        if tag in ('img', 'source'):
            self._image(tag, a, marks)
        elif a.get('style') and 'url(' in a['style']:
            m = re.search(r'background(?:-image)?\s*:[^;]*?url\(\s*[\'"]?([^\'")]+)', a['style'], re.I)
            if m:
                self.items.append(('i', m.group(1), '', marks, False))
        if tag in VOID_TAGS:
            return
        if block:
            self.items.append(('b', None))
        if head and not self.head:
            self.head_id += 1
        self.head += head
        self.strike += strike
        self.stack.append((tag, block, head, strike))

    def _image(self, tag, a, marks=None):
        raw = _img_attr(tag, a)
        if raw:
            if marks is None:
                marks = str(a.get('class') or '').lower()
            self.items.append(('i', raw, a.get('alt') or '', marks, _small(a)))

    def handle_endtag(self, tag):
        self.glue = False
        if tag in SKIP_TAGS:
            self.skip = max(0, self.skip - 1)
            if tag == 'noscript':
                self.ns = max(0, self.ns - 1)
            return
        if self.skip or not any(e[0] == tag for e in self.stack):
            return
        while self.stack:
            t, block, head, strike = self.stack.pop()
            self.head -= head
            self.strike -= strike
            if t == 'a':
                self.items.append(('/a', None))
            if block:
                self.items.append(('/b', None))
            if t == tag:
                break

    def handle_data(self, data):
        if self.skip:
            return
        s = ' '.join(data.replace(' ', ' ').replace(' ', ' ').split())
        if not s:
            self.space = self.space or bool(data)
            return
        if self.glue and self.items and self.items[-1][0] == 't' and not self.items[-1][4]:
            prev = self.items[-1]  # testo spezzato solo da un commento: "108.700<!-- --> km"
            joiner = ' ' if (self.space or data[:1].isspace()) else ''
            self.items[-1] = ('t', prev[1] + joiner + s, prev[2], prev[3], False)
        else:
            self.items.append(('t', s, self.head_id if self.head > 0 else 0, self.strike > 0, False))
        self.glue = True
        self.space = data[-1:].isspace()

    def handle_comment(self, data):
        pass


def _tokens(texts):
    out = []
    for text, head, strike, href, alt in texts:
        for part in SPLIT_RE.split(text):
            p = _plain(part)
            if p:
                out.append({'raw': part.strip(), 'p': p, 'head': head, 'strike': strike, 'href': href, 'alt': alt})
    return out


def _price_of(tok):
    if '€' not in tok['p'] and not re.search(r'(?<![a-z])eur', tok['p']):
        return None
    m = PRICE_TOKEN.match(tok['p'])
    v = to_int(m.group(1)) if m else None
    return v if v is not None and 300 <= v <= 3000000 else None


def find_price_loose(text):
    for m in PRICE_LOOSE.finditer(text):
        v = to_int(m.group(1) or m.group(2))
        if v is None or not (300 <= v <= 3000000) or MONTHLY_RE.match(text[m.end():m.end() + 14]):
            continue
        return v
    return None


def _card_item(texts, hrefs, base_url, imgs=()):
    if not hrefs:
        return None
    toks = _tokens(texts)
    if any(t['p'] in WANTED_TOKENS for t in toks if not t['alt']):
        return None
    now = time.localtime().tm_year
    cc = next((COUNTRY_TOKENS[t['p']] for t in toks if not t['alt'] and t['p'] in COUNTRY_TOKENS), '')
    if not cc:  # il paese detto con una bandierina: <img src="/flags/de.svg">
        for im in imgs:
            m = re.search(r'/flags?/([a-z]{2})\.(?:svg|png|gif|webp)(?:$|[?#])', str(im[0]).lower())
            if m and m.group(1) in TLD_CC:
                cc = TLD_CC[m.group(1)]
                break
    price = struck = None
    km = gear = fuel = None
    years, prev = [], ''
    for i, t in enumerate(toks):
        p = t['p']
        label, prev = prev, p.strip(' :')  # il testo subito prima: "Erstzulassung" | "03/2019", "HU" | "03/2027"
        if t['alt']:
            continue
        v = _price_of(t)
        if v is not None:
            nxt = toks[i + 1]['p'] if i + 1 < len(toks) else ''
            if nxt.startswith(MONTHLY_START):
                continue
            if t['strike']:
                struck = struck or v
            elif price is None:
                price = v
            continue
        if t['head']:
            continue
        if km is None:
            m = KM_TOKEN.match(p) or KM_LABELLED.match(p) or (KM_BARE.match(p) if label in KM_LABELS else None)
            if m and to_int(m.group(1)) <= 1500000:
                km = to_int(m.group(1))
                continue
        m = YEAR_TOKEN.match(p)
        if m:
            own = p[:1].isalpha()  # etichetta nello stesso testo: "EZ 03/2019"
            if own or label not in NOT_YEAR_LABELS:
                lab = own or label in YEAR_LABELS
                if int(m.group(1)) <= now + (1 if lab else 0):  # una data futura non e' un'immatricolazione
                    years.append((lab, int(m.group(1))))
            continue
        if gear is None:
            gear = gear_label(t['raw'], label in GEAR_LABELS)
            if gear:
                continue
        if fuel is None:
            fuel = fuel_label(t['raw'])
    # alcuni siti mettono anno e chilometri dentro l'intestazione, dopo il nome ("Golf 1.5 TSI | 2022 | 99.038km"): si leggono
    # solo se sono un testo a se' stante, mai dal nome dell'auto (in "Peugeot 2008" il 2008 e' il modello)
    if km is None or not years:
        first = {}
        for i, t in enumerate(toks):
            if not t['head'] or t['alt']:
                continue
            if t['head'] not in first:
                first[t['head']] = i
                continue  # il primo testo dell'intestazione e' il nome
            if km is None:
                m = KM_TOKEN.match(t['p'])
                if m and to_int(m.group(1)) <= 1500000:
                    km = to_int(m.group(1))
                    continue
            if not years:
                m = HEAD_YEAR.match(t['p'])
                if m and int(m.group(1)) <= now:
                    years.append((True, int(m.group(1))))
    loose = False
    if price is None:
        price = struck
    if price is None:
        price = find_price_loose(' | '.join(t['raw'] for t in toks if not t['head'] and not t['alt']))
        loose = True
    if price is None:
        return None
    # titolo: intestazione della scheda, altrimenti il primo testo del link all'annuncio
    spec = lambda raw: bool(_price_of({'p': _plain(raw)}) or KM_TOKEN.match(_plain(raw)) or KM_LABELLED.match(_plain(raw)) or YEAR_TOKEN.match(_plain(raw))
                            or gear_label(raw) or fuel_label(raw) or _plain(raw).strip(' :') in KM_LABELS | YEAR_LABELS | NOT_YEAR_LABELS | GEAR_LABELS)
    groups = {}  # testi di ogni intestazione; nel titolo "2008" e' un modello, non un anno
    for x in texts:
        if x[1] and not x[4] and _price_of({'p': _plain(x[0])}) is None:
            groups.setdefault(x[1], []).append(x[0])
    heads = []
    for g in groups.values():  # la stessa intestazione ripetuta (versione per schermi piccoli) conta una volta: resta la piu' completa
        cand = ' '.join(g)
        same = next((k for k, h in enumerate(heads) if _plain(cand) in _plain(h) or _plain(h) in _plain(cand)), None)
        if same is None:
            heads.append(cand)
        elif len(cand) > len(heads[same]):
            heads[same] = cand
    idx = None
    if heads:
        title = ' '.join(heads)
        idx = max(i for i, x in enumerate(texts) if x[1] and not x[4])
    else:
        cand = [(i, x[0]) for i, x in enumerate(texts) if x[3] and not x[4] and len(x[0]) >= 8 and len(x[0].split()) >= 2 and not spec(x[0])]
        if not cand:
            cand = [(i, x[0]) for i, x in enumerate(texts) if x[3] and not x[4] and len(x[0]) >= 6 and not spec(x[0])]
        if not cand:
            cand = [(i, x[0]) for i, x in enumerate(texts) if x[4] and len(x[0]) >= 6]
        if not cand:
            return None
        idx, title = cand[0]
        # scheda senza intestazione: se il primo testo non c'entra con l'annuncio ("BONNE AFFAIRE") ma un altro riprende le parole
        # dell'indirizzo dell'annuncio (marca e modello), il nome e' quello; marca e modello possono stare in due testi di fila
        slug = _compact(urlparse(hrefs[0]).path)
        near = lambda raw: sum(1 for w in re.findall(r'[a-z0-9]{3,}', _plain(raw)) if w not in SLUG_GENERIC and w in slug)
        if not near(title):
            run = []
            for i, x in enumerate(texts):
                ok = bool(x[3]) and not x[4] and not spec(x[0]) and len(x[0]) <= 60 and near(x[0])
                if ok and len(run) < 3:
                    run.append(i)
                elif run:
                    break
            if run:
                idx, title = run[-1], ' '.join(texts[i][0] for i in run)
    if len(title.split()) <= 3:  # "Volkswagen Golf" + riga della versione "1.6 TDI 110 CV"
        for x in texts[idx + 1:]:
            if x[4] or spec(x[0]) or not re.search(r'[a-z0-9]', _plain(x[0])):
                continue
            if len(x[0]) <= 60 and not x[0].rstrip().endswith(('...', '\u2026')) and VERSION_RE.search(_plain(x[0])):
                title = title + ' ' + x[0]
                break
            break  # solo la riga subito dopo il titolo puo' essere la versione
    year = None
    if years:  # prima l'anno con etichetta; altrimenti il piu' vecchio (revisioni e garanzie vengono dopo l'immatricolazione)
        in_title = set(re.findall(r'(?<!\d)\d{4}(?!\d)', title))
        pool = [c for c in years if str(c[1]) not in in_title] or years
        labelled = [y for lab, y in pool if lab]
        year = labelled[0] if labelled else min(y for lab, y in pool)
    # indirizzo dell'annuncio: il link che racchiude il titolo; altrimenti il piu' ripetuto, preferendo quelli dello stesso sito
    best = next((x[3] for x in texts if x[1] and x[3] and not x[4]), None)
    if not best:
        host = urlparse(base_url).netloc.lower().replace('www.', '')
        own = [h for h in hrefs if urlparse(h).netloc.lower().replace('www.', '') == host] or hrefs
        best = max(set(own), key=lambda h: (own.count(h), -own.index(h)))
    txt = ' | '.join(x[0] for x in texts if not x[4])
    item = _item(title, price, km, year, gear, fuel, best, 'pagina', txt, loose=loose, **({'cc': cc} if cc else {}))
    photos = _pick_photos(imgs, base_url, title, best) if imgs else []
    if photos:
        item['img'], item['imgs'] = photos[0], photos
    return item


def extract_cards(html, base_url):
    ps = _Stream()
    try:
        ps.feed(html)
        ps.close()
    except Exception:
        pass
    items = ps.items
    # 1) schede delimitate (article, li, section, div "card"): per ogni annuncio il contenitore piu' grande che ne contiene uno solo
    root = {'texts': [], 'hrefs': [], 'kids': [], 'imgs': []}
    stack, cur = [root], None
    for it in items:
        kind = it[0]
        if kind == 'b':
            node = {'texts': [], 'hrefs': [], 'kids': [], 'imgs': []}
            stack[-1]['kids'].append(node)
            stack.append(node)
        elif kind == '/b':
            if len(stack) > 1:
                stack.pop()
        elif kind == 'a':
            cur = _is_detail(it[1], base_url)
            if cur:
                for n in stack[1:]:
                    n['hrefs'].append(cur)
        elif kind == '/a':
            cur = None
        elif kind == 't':
            tup = (it[1], it[2], it[3], cur, it[4])
            for n in stack[1:]:
                n['texts'].append(tup)
        elif kind == 'i':
            for n in stack[1:]:
                if len(n['imgs']) < 40:
                    n['imgs'].append(it[1:])
    out = []

    def priced(n):
        if 'priced' not in n:
            n['priced'] = bool(n['hrefs']) and any(_price_of({'p': _plain(p)}) is not None for t in n['texts'] if not t[4] for p in SPLIT_RE.split(t[0]))
        return n['priced']

    def prices(n):
        if 'prices' not in n:
            n['prices'] = set(v for v in (_price_of({'p': _plain(p)}) for t in n['texts'] if not t[4] and not t[2] for p in SPLIT_RE.split(t[0])) if v is not None)
        return n['prices']

    def emit(n, depth=0):
        d = set(n['hrefs'])
        if not d or depth > 60:
            return
        if len(d) <= 12 and len(prices(n)) <= 3 and sum(len(t[0]) for t in n['texts']) <= 2500:
            pk = [k for k in n['kids'] if priced(k)]
            multi = any(not (set(x['hrefs']) & set(y['hrefs'])) for i, x in enumerate(pk) for y in pk[i + 1:])
            if not multi:
                card = _card_item(n['texts'], n['hrefs'], base_url, n['imgs'])
                if card:
                    out.append(card)
                    return
        for k in n['kids']:
            emit(k, depth + 1)

    for k in root['kids']:
        emit(k)
    if len(out) >= 2:
        return out
    # 2) nessuna scheda riconoscibile: il testo che segue ogni link a un annuncio
    out2, seen = [], set()
    cur, texts, hrefs, size, in_a = None, [], [], 0, None
    imgs, before = [], []  # "before" = immagini viste subito prima del link di un annuncio (la foto sta spesso sopra il titolo)

    def flush():
        if cur and texts:
            card = _card_item(texts, hrefs, base_url, imgs)
            if card and url_key(card['url']) not in seen:
                seen.add(url_key(card['url']))
                out2.append(card)

    for it in items:
        kind = it[0]
        if kind == 'a':
            h = _is_detail(it[1], base_url)
            in_a = h
            if h and h != cur:
                has_price = any(_price_of({'p': _plain(p)}) for t in texts for p in SPLIT_RE.split(t[0]))
                if cur is None or has_price or size > 500:
                    flush()
                    cur, texts, hrefs, size = h, [], [h], 0
                    imgs, before = before, []
        elif kind == '/a':
            in_a = None
        elif kind == 'i':
            if cur and not any(_price_of({'p': _plain(p)}) for t in texts for p in SPLIT_RE.split(t[0])):
                if len(imgs) < 40:
                    imgs.append(it[1:])
            else:
                before = (before + [it[1:]])[-8:]
        elif kind == 't' and cur and size <= 900:
            texts.append((it[1], it[2], it[3], in_a if in_a == cur else None, it[4]))
            size += len(it[1])
    flush()
    return out2 if len(out2) > len(out) else out


def extract_listings(html, base_url):
    """Annunci letti dalla pagina, senza doppioni, con cambio e alimentazione completati dalle sigle del titolo."""
    host = urlparse(base_url).netloc.lower()
    items = []
    for key, fn in SITE_PARSERS:
        if key in host:
            try:
                items = fn(html, base_url)
            except Exception:
                items = []
            break
    if not items:
        ld = extract_ld(html, base_url)
        cards = extract_cards(html, base_url)
        try:
            state = extract_state(html, base_url)
        except Exception:
            state = []
        by, twin = {}, {}
        for it in state + cards + ld:  # i dati della pagina sono i piu' affidabili; la scheda e schema.org completano quello che manca
            k = url_key(it['url'])
            sig = (it.get('price'), it.get('km'), _compact(it.get('title'))[:28]) if it.get('km') is not None else None
            if k not in by and sig in twin:
                k = twin[sig]  # lo stesso annuncio con due indirizzi (dai dati e dalla scheda): conta una volta
            if k not in by:
                by[k] = it
                if sig:
                    twin[sig] = k
                continue
            old = by[k]
            for f in ('km', 'year', 'gear', 'fuel', 'power', 'seller', 'iva', 'cc', 'img', 'imgs'):
                if old.get(f) in (None, '') and it.get(f) not in (None, ''):
                    old[f] = it[f]
            if old.get('src') != 'dati' and len(it.get('title') or '') > len(old.get('title') or ''):
                old['title'] = it['title']
            if old.get('loose') and it.get('price'):
                old['price'], old['loose'] = it['price'], False
            if it.get('_txt') and it['_txt'] not in (old.get('_txt') or ''):
                old['_txt'] = ((old.get('_txt') or '') + ' | ' + it['_txt'])[:1500]
        items = list(by.values())
    out, seen = [], set()
    for it in items:
        if not it.get('url') or not _listing_url_ok(it['url'], base_url):
            continue
        k = url_key(it['url'])
        if k in seen:
            continue
        seen.add(k)
        slug = urlparse(it['url']).path.replace('-', ' ').replace('_', ' ').replace('/', ' ')
        if it.get('gear') is None:
            it['gear'] = gear_hint(it.get('title')) or gear_hint(slug)
            if it['gear']:
                it['gsrc'] = 'titolo'
        if it.get('fuel') is None:
            it['fuel'] = fuel_hint(it.get('title')) or fuel_label(' '.join(w for w in slug.split() if w in ('diesel', 'gasolina', 'benzina', 'essence', 'benzin', 'hibrido', 'electrico')))
            if it['fuel']:
                it['fsrc'] = 'titolo'
        if it.get('fuel') == 'E' and it.get('gear') is None:
            it['gear'], it['gsrc'] = 'A', 'elettrica'  # le elettriche non hanno cambio manuale
        card = (it.get('title') or '') + ' | ' + (it.get('_txt') or '')
        if not it.get('power'):
            pw = power_from(it.get('title')) or power_from(it.get('_txt'))
            if pw:
                it['power'] = pw
        if it.get('iva') is None:
            iva = vat_hint(card)
            if iva is not None:
                it['iva'] = iva
        if not it.get('seller'):
            who = seller_hint(it.get('_txt'))
            if who:
                it['seller'] = who
        out.append(it)
    return out


def judge(item, crit, trust=()):
    """Verifica un annuncio contro i filtri richiesti.
    Restituisce ('ok', []), ('incerto', [dati mancanti]) oppure ('scartato', [motivo])."""
    p, km, y = item.get('price'), item.get('km'), item.get('year')
    if p is None:
        return 'scartato', ['senza prezzo']
    if p < 900 and not (crit.get('priceMin') and crit['priceMin'] < 900):
        return 'scartato', ['prezzo troppo basso per essere un prezzo di vendita']
    if (crit.get('priceMin') and p < crit['priceMin']) or (crit.get('priceMax') and p > crit['priceMax']):
        return 'scartato', ['prezzo fuori dai limiti']
    title = item.get('title') or ''
    slug = (re.sub(r'[-_/+.]+', ' ', urlparse(item.get('url') or '').path) + ' ' + str(item.get('more') or '')).strip()
    card = item.get('_txt') or ''
    words = crit.get('words') or []
    aliases = [_compact(a) for a in (crit.get('makeAliases') or []) if _compact(a)]
    ctitle = _compact(title)
    lead = re.findall(r'[a-z0-9]+', _plain(title))[:2]
    others = set(_compact(o) for o in (crit.get('otherMakes') or []))
    if aliases and lead and others and not any(a in ctitle for a in aliases) and ({lead[0], ''.join(lead)} & others):
        return 'scartato', ['altra marca']
    missing = []
    if words:
        if not words_match(title, crit.get('make'), words, slug, crit.get('makeAliases')):
            if card and card != title and words_match(title, crit.get('make'), words, slug + ' ' + card, crit.get('makeAliases')):
                missing.append('modello nel titolo')  # citato solo nel testo della scheda: non basta per darlo come verificato
            else:
                return 'scartato', ['modello o parole chiave non presenti']
        other = sibling_hit(crit, title + ' | ' + slug)
        if other:
            return 'scartato', ['altro modello: ' + other]
    elif aliases:
        comp = _compact(' '.join((title, slug, card)))
        if not any(a in comp for a in aliases):
            return 'scartato', ['marca non presente']
    text = title + ' | ' + str(item.get('more') or '') + ' | ' + card  # tutto quello che l'annuncio dichiara nella sua scheda
    for w in crit.get('excl') or []:
        w = _plain(w)
        if w and re.search(r'(?<![a-z0-9])' + r'[\s-]?'.join(re.escape(x) for x in w.split()) + r'(?![a-z0-9])', _plain(text)):
            return 'scartato', ['contiene una parola esclusa']
    dmg = bool(item.get('dmg')) or damage_hint(text)
    want_dmg = crit.get('damaged') or 'no'
    if want_dmg == 'no' and dmg:
        return 'scartato', ['incidentata o con danni dichiarati']
    if want_dmg == 'only' and not dmg and 'damage' not in trust:
        return 'scartato', ['non dichiarata incidentata']
    if crit.get('kmMax') or crit.get('kmMin'):
        if km is None:
            if 'km' not in trust:
                missing.append('km')
        elif (crit.get('kmMax') and km > crit['kmMax']) or (crit.get('kmMin') and km < crit['kmMin']):
            return 'scartato', ['km fuori dai limiti']
    if crit.get('yearMin') or crit.get('yearMax'):
        if y is None:
            if 'year' not in trust:
                missing.append('anno')
        elif (crit.get('yearMin') and y < crit['yearMin']) or (crit.get('yearMax') and y > crit['yearMax']):
            return 'scartato', ['anno fuori dai limiti']
    if crit.get('gear'):
        g = item.get('gear')
        if g is None:
            if 'gear' not in trust:
                missing.append('cambio')
        elif g != crit['gear']:
            return 'scartato', ['cambio diverso']
    if crit.get('fuel'):
        ok = fuel_ok(crit['fuel'], item.get('fuel'))
        if ok is False:
            return 'scartato', ['alimentazione diversa']
        if ok is None and 'fuel' not in trust:
            missing.append('alimentazione')
    if crit.get('body') and 'body' not in trust:
        ok = body_ok(crit['body'], title + ' ' + str(item.get('more') or ''))
        if ok is False:
            return 'scartato', ['carrozzeria diversa']
        if ok is None:
            missing.append('carrozzeria')
    if crit.get('powerMin') or crit.get('powerMax'):
        pw = item.get('power')
        if not pw:
            if 'power' not in trust:
                missing.append('potenza')
        elif (crit.get('powerMin') and pw < crit['powerMin'] - 2) or (crit.get('powerMax') and pw > crit['powerMax'] + 2):
            return 'scartato', ['potenza fuori dai limiti']
    if crit.get('seller') in ('D', 'P'):
        who = {'Concessionario': 'D', 'Privato': 'P'}.get(item.get('seller') or '')
        if not who:
            if 'seller' not in trust:
                missing.append('venditore')
        elif who != crit['seller']:
            return 'scartato', ['venditore diverso']
    if crit.get('vat'):
        iva = item.get('iva')
        if iva is False:
            return 'scartato', ['IVA non detraibile']
        if iva is None and 'vat' not in trust:
            missing.append('IVA esposta')
    if crit.get('drive') == '4':
        awd = drive_hint(text)
        if awd is False and 'drive' not in trust:
            return 'scartato', ['trazione non integrale']
        if awd is None and 'drive' not in trust:
            missing.append('trazione 4x4')
    if crit.get('color') in COLOR_RE:
        found = color_hint(title + ' | ' + card + ' | ' + slug)
        if 'color' not in trust:
            if found and crit['color'] not in found:
                return 'scartato', ['colore diverso']
            if not found:
                missing.append('colore')
    if 'eq' not in trust:
        ptext = _plain(text)
        for key in crit.get('eq') or []:  # 'eq:tetto' = questa dotazione l'ha gia' filtrata il sito
            if key in EQUIP_RE and ('eq:' + key) not in trust and not EQUIP_RE[key].search(ptext):
                missing.append(EQUIP[key][0])
    if crit.get('owners1') and 'owners' not in trust and not OWNER1_RE.search(_plain(text)):
        missing.append('unico proprietario')
    if crit.get('doors') in (3, 5) and 'doors' not in trust:
        m = DOORS_RE.search(_plain(text))
        if not m:
            missing.append('%d porte' % crit['doors'])
        elif (int(m.group(1) or m.group(2)) <= 3) != (crit['doors'] == 3):
            return 'scartato', ['numero di porte diverso']
    if crit.get('seatsMin') and 'seats' not in trust:
        seats = seats_hint(text)
        if seats is None:
            missing.append('%d posti' % crit['seatsMin'])
        elif seats < crit['seatsMin']:
            return 'scartato', ['posti insufficienti']
    return ('incerto', missing) if missing else ('ok', [])


def judge_all(found, crit, trust=()):
    """Divide gli annunci letti in validi (con eventuali dati mancanti) e scartati."""
    kept, dropped = [], 0
    for it in found:
        verdict, why = judge(it, crit, trust)
        if verdict == 'scartato':
            dropped += 1
            continue
        it = dict(it)
        it['unk'] = why
        if it.get('dmg') or damage_hint((it.get('title') or '') + ' | ' + (it.get('_txt') or '')):
            it['dmg'] = True
        else:
            it.pop('dmg', None)
        for k in ('_txt', 'src', 'loose', 'more'):
            it.pop(k, None)
        kept.append(it)
    return kept, dropped


# --------------------------------------------------------------------------
# Scansione
# --------------------------------------------------------------------------
CC = {'DE': 'de', 'BE': 'be', 'FR': 'fr', 'ES': 'es', 'NL': 'nl', 'AT': 'at', 'LU': 'lu'}
TLD_CC = {'de': 'DE', 'be': 'BE', 'fr': 'FR', 'es': 'ES', 'it': 'IT', 'nl': 'NL', 'at': 'AT', 'ch': 'CH', 'lu': 'LU', 'pt': 'PT'}
DIAG_MAX_PAGE = 3000000
DIAG_MAX_TOTAL = 60000000
MAX_PAGES_PER_SITE = 10
BROWSER_PAGES = 3  # il browser del computer legge un sito alla volta: piu' di tre pagine a sito allungherebbero troppo la ricerca
THIN_PAGE = 4      # meno annunci di cosi' in una pagina letta direttamente: con Bright Data attivo la si rilegge, perche' puo' essere una pagina a meta'
# pagina che dice da sola di non avere risultati: non serve farla rileggere a Bright Data o al browser
NO_RESULTS_RE = re.compile(r"(?<![\d.,])0\s+(?:gebrauchtwagen|fahrzeuge?|ergebnisse?|treffer|angebote?|annonces?|r[e\u00e9]sultats?|v[e\u00e9]hicules?|voitures?|coches?|resultados?|anuncios?|veh[i\u00ed]culos?|zoekresultaten|resultaten|auto's)\b"
                           r"|keine\s+(?:passenden\s+)?(?:ergebnisse|treffer|fahrzeuge|angebote|anzeigen)\b|leider\s+(?:keine|nichts)\s+gefunden"
                           r"|aucun(?:e)?\s+(?:r[e\u00e9]sultat|annonce|v[e\u00e9]hicule|voiture|offre)\b|pas\s+de\s+r[e\u00e9]sultat"
                           r"|sin\s+resultados|no\s+(?:hay|hemos\s+encontrado|se\s+han\s+encontrado|se\s+encontraron)\s+(?:resultados|coches|anuncios|veh[i\u00ed]culos)"
                           r"|ning[u\u00fa]n\s+(?:resultado|coche|anuncio|veh[i\u00ed]culo)\b|geen\s+(?:resultaten|zoekresultaten|auto's)\b", re.I)


TOTAL_RE = re.compile(r"(?<![\d.,])(\d{1,3}(?:[.\s\u00a0\u202f]\d{3})+|\d{1,6})\s+(?:gebrauchtwagen|fahrzeuge|ergebnisse|treffer|angebote|anzeigen|annonces|r[e\u00e9]sultats|v[e\u00e9]hicules|voitures|coches|resultados|anuncios"
                      r"|veh[i\u00ed]culos|resultaten|occasions|ofertas|annunci)\b", re.I)


def _stated_total(html):
    """Quanti annunci la pagina dice di avere ("160 annonces", "4.681 Angebote"), se lo dice."""
    m = TOTAL_RE.search(_visible_text(html))
    return to_int(m.group(1)) if m else None


def _visible_text(html, limit=400000):
    """Il testo che si vede nella pagina, senza programmi e stili (dove le stesse frasi compaiono come testi di riserva)."""
    t = re.sub(r'(?is)<(script|style|noscript|template|svg|select)\b.*?</\1\s*>', ' ', html[:limit])
    return ' '.join(re.sub(r'(?s)<[^>]+>', ' ', t).split())
CHALLENGE_RE = re.compile(r'captcha|datadome|cf-chl|just a moment|access denied|unusual traffic|are you a robot|pardon our interruption', re.I)


def _diag(job, task, url, code, html, note=''):
    """Conserva la pagina letta: serve a capire, dopo, perche' un sito e' stato letto male."""
    if job is None:
        return
    with JOBS_LOCK:
        size = sum(len(d['html']) for d in job['diag'])
        job['diag'].append({'site': task.get('site', ''), 'country': task.get('country', ''), 'url': url, 'code': code, 'note': note,
                            'html': (html or '')[:DIAG_MAX_PAGE] if size < DIAG_MAX_TOTAL else ''})


def _page_url(url, n, param):
    if n <= 1 or not param:
        return url
    base, _, frag = url.partition('#')
    pat = re.compile(r'([?&])' + re.escape(param) + r'=\d*(?=&|$)')
    if pat.search(base):  # l'indirizzo porta gia' il numero di pagina ("?page=1&..."): lo si sostituisce
        base = pat.sub(lambda m: m.group(1) + param + '=' + str(n), base, count=1)
    else:
        base = base + ('&' if '?' in base else '?') + param + '=' + str(n)
    return base + (('#' + frag) if frag else '')


def _cand_page_url(cand, n, param):
    """Indirizzo della pagina n di un indirizzo candidato. Dove il numero di pagina sta nel percorso (Kleinanzeigen: ".../seite:2/...",
    Marktplaats: ".../p/2/") la pagina manda il modello dell'indirizzo ("p", con {n}); altrove basta il nome del parametro."""
    tpl = cand.get('p')
    if isinstance(tpl, str) and '{n}' in tpl and tpl.startswith('http') and urlparse(tpl).netloc == urlparse(cand['u']).netloc:
        return tpl.replace('{n}', str(n))
    return _page_url(cand['u'], n, param) if param else ''


def _unk_n(items):
    """Quanti annunci tenuti non dichiarano tutti i dati richiesti."""
    return sum(1 for x in items if x.get('unk'))


def _unglue(title, crit):
    """"VolkswagenGolf R" -> "Volkswagen Golf R": solo dopo la marca cercata e solo se segue una maiuscola o una cifra."""
    for mk in [crit.get('make')] + list(crit.get('makeAliases') or []):
        mk = str(mk or '').strip()
        if len(mk) >= 3:
            title = re.sub(r'(?<![A-Za-z0-9])((?i:' + re.escape(mk) + r'))(?=[A-Z0-9])', r'\1 ', title or '')
        elif len(mk) == 2:  # sigle di due lettere ("VWGolf"): solo scritte in maiuscolo e seguite da una parola, per non spezzare "DSG"
            title = re.sub(r'(?<![A-Za-z0-9])(' + re.escape(mk.upper()) + r')(?=[A-Z][a-z])', r'\1 ', title or '')
    return title


def _judge_items(task, crit, items):
    for it in items:
        if it.get('title'):
            it['title'] = _unglue(it['title'], crit)
    kept, dropped = judge_all(items, crit, tuple(task.get('trust') or ()))
    only = [c for c in (crit.get('countries') or []) if c in CC]
    out = []
    for x in kept:
        x['site'] = task['site']
        x['country'] = x.pop('cc', '') or task['country']
        if only and x['country'] in TLD_CC.values() and x['country'] not in only:
            dropped += 1  # l'annuncio dichiara un paese diverso da quelli richiesti
            continue
        out.append(x)
    return out, dropped


def _judge_page(task, crit, html, final_url):
    found = extract_listings(html, final_url)
    kept, dropped = _judge_items(task, crit, found)
    return found, kept, dropped


def _summary(read, kept, dropped):
    unk = sum(1 for x in kept if x.get('unk'))
    good = len(kept) - unk
    msg = '%d letti: %d %s' % (read, good, 'valido' if good == 1 else 'validi')
    if unk:
        msg += ', %d con dati mancanti' % unk
    if dropped:
        msg += ', %d fuori dai filtri' % dropped
    return msg


def scan_site(task, crit, job, fetch, challenge=True):
    """Legge un sito. fetch(url) restituisce ('ok', html, indirizzo finale) oppure (stato, messaggio, None) con stato
    'regole' (indirizzo escluso da robots.txt), 'bloccato' (richiesta rifiutata), 'assente' (pagina inesistente) o 'errore'.
    Gli indirizzi segnati "also" si leggono tutti (lo stesso modello puo' stare sotto due nomi); gli altri, dopo il primo,
    sono di riserva e servono solo se fin li' non e' uscito nessun annuncio."""
    cands = [c for c in (task.get('urls') or []) if isinstance(c, dict) and str(c.get('u', '')).startswith('http')]
    if not cands:
        cands = [{'u': task['url']}] + ([{'u': task['alt']}] if task.get('alt') else [])
    status, last, why = 'vuoto', '', ''
    paged = bool(task.get('pageParam')) or any(_cand_page_url(c, 2, '') for c in cands)
    pages = max(1, min(MAX_PAGES_PER_SITE, int(task.get('pages') or 1))) if paged else 1
    keys, all_kept, read, all_dropped, got = set(), [], 0, 0, False
    first_page = ['']

    def take(html, final, note):
        nonlocal read, all_dropped
        found, here = [], set()
        shots = html if isinstance(html, list) else [html]  # il browser puo' dare la pagina prima e dopo averla scorsa
        for shot in shots:
            for x in extract_listings(shot, final):
                k = url_key(x['url'])
                if k not in here:
                    here.add(k)
                    found.append(x)
        fresh = [x for x in found if url_key(x['url']) not in keys]
        keys.update(url_key(x['url']) for x in fresh)
        kept, dropped = _judge_items(task, crit, fresh)
        _diag(job, task, final, 200, shots[-1], note % len(found))
        all_kept.extend(kept)
        read += len(fresh)
        all_dropped += dropped
        return len(found), len(fresh)

    for n_cand, cand in enumerate(cands):
        if got and not cand.get('also'):
            continue
        u = cand['u']
        st, html, final = fetch(u)
        if st != 'ok':
            _diag(job, task, u, st, '', html)
            if not got:
                status, last, why = {'assente': 'errore', 'regole': 'bloccato'}.get(st, st), html, st
            if st in ('assente', 'regole'):
                continue  # pagina inesistente, oppure indirizzo escluso dalle regole del sito: un altro puo' essere ammesso
            break  # il sito ha rifiutato la richiesta: non si insiste
        n_found, n_fresh = take(html, final, '%d annunci letti')
        if n_found and not first_page[0]:
            first_page[0] = html[-1] if isinstance(html, list) else html
        if not n_found:
            if challenge and CHALLENGE_RE.search((html[-1] if isinstance(html, list) else html)[:30000]):
                if not got:
                    status, last, why = 'bloccato', REFUSED, 'bloccato'
                break
            if not got:
                status, last, why = 'vuoto', 'Pagina letta, nessun annuncio riconosciuto.', 'vuoto'
                # solo dove si sa che la pagina arriva gia' completa (o l'ha composta un browser): altrove "0 annunci" puo' essere un testo provvisorio
                if (task.get('st') or isinstance(html, list)) and NO_RESULTS_RE.search(_visible_text(html[-1] if isinstance(html, list) else html)):
                    last, why = 'Il sito dice di non avere annunci per questa ricerca.', 'zero'
            continue
        got = True
        for n in range(2, pages + 1):  # pagine successive dello stesso indirizzo
            if n_found < 10:
                break
            pu = _cand_page_url(cand, n, task.get('pageParam'))
            if not pu:
                break
            st, html, final = fetch(pu)
            if st != 'ok':
                break  # pagina che il sito non da' (o che le sue regole escludono): ci si ferma a quelle lette
            n_found, n_fresh = take(html, final, 'pagina ' + str(n) + ': %d annunci letti')
            if not n_fresh:
                break
    if got:
        stats = {'read': read, 'drop': all_dropped}
        if read < THIN_PAGE:  # pochi annunci letti: se la pagina ne dichiara molti di piu', e' una pagina arrivata a meta'
            stats['total'] = _stated_total(first_page[0]) or 0
        return ('ok' if all_kept else 'vuoto'), all_kept, _summary(read, all_kept, all_dropped), stats
    return status, [], last, {'read': 0, 'drop': 0, 'why': why}


def fetch_direct(url, jar=None, net=None):
    """net = contatore della scansione: quante risposte sono arrivate e quali problemi di rete ci sono stati."""
    try:
        for _hop in range(6):
            allowed = robots_allows(url)
            if net is not None:
                net['ok'] = net.get('ok', 0) + 1  # il sito ha risposto (anche solo con le sue regole): la rete funziona
            if not allowed:
                return 'regole', RULES, None
            code, html, final, loc = http_get(url, jar=jar)
            if code in (301, 302, 303, 307, 308) and loc:
                url = urljoin(url, loc)  # il sito rimanda a un altro indirizzo: prima di leggerlo si ricontrollano le regole
                continue
            break
        else:
            return 'errore', 'Il sito rimanda da un indirizzo all\'altro senza fine.', None
    except FetchError as e:
        if net is not None:
            net[e.kind] = net.get(e.kind, 0) + 1
        return 'errore', str(e), None
    if code in (401, 403, 407, 429, 451):
        return 'bloccato', REFUSED, None
    if code in (404, 410):
        return 'assente', 'Pagina non trovata sul sito.', None
    if code >= 400:
        return 'errore', 'Il sito ha risposto con un errore (%d).' % code, None
    return 'ok', html, final


def make_fetch_direct(job):
    """Lettura diretta per una scansione: stessi cookie per tutta la scansione, e conteggio dei problemi di rete."""
    jar = http.cookiejar.CookieJar()
    net = job.setdefault('net', {})
    return lambda url: fetch_direct(url, jar, net)


def make_fetch_bd(cfg, country, usage=None):
    """Lettura tramite Bright Data. Con "usage" (conteggio condiviso della ricerca) tiene il conto delle pagine chieste e
    si ferma da sola quando il problema riguarda l'account (chiave rifiutata, credito finito, servizio non raggiungibile)
    oppure quando le prime richieste falliscono tutte: inutile insistere con gli altri siti."""
    def fetch(url):
        if usage is not None:
            with JOBS_LOCK:
                if usage.get('fail'):
                    return 'errore', usage['fail'], None
                usage['n'] += 1
        try:
            html = bd_request(cfg, url, country=CC.get(country))
        except BDError as e:
            msg = str(e)
            if usage is not None:
                with JOBS_LOCK:
                    usage['err'] += 1
                    if e.code in (401, 402, -1) or (usage['ok'] == 0 and usage['err'] >= 4 and e.code in (400, 403, 407)):
                        usage['fail'] = msg
            return ('assente' if e.code == 404 or '404' in msg else 'errore'), msg, None
        if usage is not None:
            with JOBS_LOCK:
                usage['ok'] += 1
        return 'ok', html, url
    return fetch


def scan_discover(cfg, d, known):
    zone = cfg['serpZone'] or cfg['zone']
    try:
        txt = bd_request(cfg, d['url'], zone=zone)
        data = json.loads(txt)
    except BDError as e:
        return 'errore', [], str(e)
    except ValueError:
        return 'errore', [], 'La zona non restituisce i risultati di Google come dati. Crea una zona SERP API e scrivila nelle impostazioni.'
    out = []
    for r in data.get('organic') or []:
        link = r.get('link') or r.get('url') or ''
        dom = urlparse(link).netloc.lower().replace('www.', '')
        if not link or any(dom == k or dom.endswith('.' + k) for k in known):
            continue
        out.append({'title': (r.get('title') or dom)[:140], 'link': link, 'domain': dom, 'country': d['country']})
    return 'ok', out, '%d siti nuovi' % len(out)


def _host(u):
    return urlparse(u or '').netloc.lower().replace('www.', '')


def _exact_km(x):
    """Chilometri precisi (non tondi): insieme al prezzo identificano la stessa auto anche quando il titolo e' scritto diversamente."""
    km = x.get('km')
    return km is not None and km >= 1000 and km % 500 != 0


# ---- annunci nascosti, interessanti e gia' visti: restano su questo computer, nella cartella dei dati ----------
MARKS_PATH = os.path.join(data_dir(), 'annunci.json')
MARKS_LOCK = threading.RLock()
MARKS = {'data': None, 'dirty': False}
SEEN_MAX = 80000
MARK_FIELDS = ('title', 'price', 'km', 'year', 'site', 'country', 'url', 'img', 'gear', 'fuel')


def mark_key(url):
    return hashlib.sha1(url_key(str(url or '')).encode('utf-8')).hexdigest()[:16]


def car_sig(x):
    """La stessa auto anche su un altro sito: prezzo, anno e chilometri precisi."""
    km, price, year = x.get('km'), x.get('price'), x.get('year')
    if type(km) is not int or type(price) is not int or not _exact_km(x):
        return ''
    return 'c' + hashlib.sha1(('%d|%s|%d' % (km, year if type(year) is int else '', price)).encode('utf-8')).hexdigest()[:15]


def _marks():
    with MARKS_LOCK:
        if MARKS['data'] is None:
            d = load_json(MARKS_PATH, {})
            d = d if isinstance(d, dict) else {}
            MARKS['data'] = dict((k, d.get(k) if isinstance(d.get(k), dict) else {}) for k in ('hidden', 'fav', 'seen'))
        return MARKS['data']


def marks_flush():
    with MARKS_LOCK:
        m = MARKS['data']
        if m is None or not MARKS['dirty']:
            return
        if len(m['seen']) > SEEN_MAX:  # restano i visti piu' di recente
            m['seen'] = dict(sorted(m['seen'].items(), key=lambda kv: kv[1])[-int(SEEN_MAX * 0.8):])
        save_json(MARKS_PATH, m)
        MARKS['dirty'] = False


def marks_note_seen(job, x):
    """Segna l'annuncio come visto. True se e' nuovo, cioe' mai uscito prima di questa ricerca (nemmeno su un altro sito)."""
    with MARKS_LOCK:
        seen, now, fresh = _marks()['seen'], int(time.time()), job.setdefault('fresh', set())
        keys = [k for k in (x.get('k'), x.get('sg')) if k]
        old = any(k in seen and k not in fresh for k in keys)  # "fresh" = visti per la prima volta in questa stessa ricerca
        for k in keys:
            if k not in seen:
                seen[k] = now
                fresh.add(k)
                MARKS['dirty'] = True
        return not old


def item_keys(x):
    return [k for k in [x.get('k')] + list(x.get('ks') or []) + [x.get('sg')] if k]


def hidden_keys():
    with MARKS_LOCK:
        return set(k for v in _marks()['hidden'].values() for k in (v.get('keys') or []))


def marks_public():
    with MARKS_LOCK:
        m = _marks()
        def rows(d):
            out = [dict([('k', k), ('t', v.get('t') or 0), ('keys', v.get('keys') or [])] + [(f, v.get(f)) for f in MARK_FIELDS if v.get(f) not in (None, '')]) for k, v in d.items()]
            return sorted(out, key=lambda r: -r['t'])
        keys = lambda d: sorted(set(k for v in d.values() for k in (v.get('keys') or [])))
        return {'hidden': rows(m['hidden'])[:500], 'hiddenKeys': keys(m['hidden']), 'hiddenN': len(m['hidden']),
                'fav': rows(m['fav'])[:500], 'favKeys': keys(m['fav']), 'seen': len(m['seen'])}


def marks_op(data):
    """Nascondi, ripristina, segna interessante, togli il segno."""
    data = data if isinstance(data, dict) else {}
    op, it = str(data.get('op') or ''), data.get('item') if isinstance(data.get('item'), dict) else {}
    with MARKS_LOCK:
        m = _marks()
        if op in ('hide', 'fav'):
            url = str(it.get('url') or '')
            if not re.match(r'https?://', url) or len(url) > 1500:
                raise ValueError('Annuncio non valido.')
            k = mark_key(url)
            keys = [k] + [mark_key(u) for u in (it.get('alsoUrl') or [])[:12] if isinstance(u, str) and re.match(r'https?://', u)]
            sg = car_sig(it)
            if sg:
                keys.append(sg)
            rec = {'t': int(time.time()), 'keys': keys}
            for f in MARK_FIELDS:
                v = it.get(f)
                if (type(v) is int and 0 <= v < 10 ** 8) if f in ('price', 'km', 'year') else (isinstance(v, str) and 0 < len(v) <= 1500):
                    rec[f] = v
            mine, other = (m['hidden'], m['fav']) if op == 'hide' else (m['fav'], m['hidden'])
            for old in [o for o, v in other.items() if set(keys) & set(v.get('keys') or [])]:
                del other[old]  # un annuncio nascosto non e' piu' tra gli interessanti, e viceversa
            mine[k] = rec
            for d, cap in ((m['hidden'], 6000), (m['fav'], 1500)):
                if len(d) > cap:
                    for old in sorted(d, key=lambda o: d[o].get('t') or 0)[:len(d) - cap]:
                        del d[old]
        elif op in ('unhide', 'unfav'):
            keys = set(str(x) for x in (data.get('keys') or [])[:40] if isinstance(x, str))
            d = m['hidden'] if op == 'unhide' else m['fav']
            for old in [o for o, v in d.items() if o in keys or keys & set(v.get('keys') or [])]:
                del d[old]
        elif op == 'unhideAll':
            m['hidden'] = {}
        elif op == 'forgetSeen':
            m['seen'] = {}
        else:
            raise ValueError('Operazione non valida.')
        MARKS['dirty'] = True
        marks_flush()
        return marks_public()


def _add_results(job, items):
    """Aggiunge gli annunci senza doppioni: stesso indirizzo, oppure la stessa auto pubblicata su due siti. E' la stessa auto se
    titolo, prezzo, chilometri e anno coincidono, oppure se coincidono prezzo, anno e chilometri precisi (non tondi) anche con un
    titolo diverso. In quel caso resta il primo annuncio, con l'elenco degli altri siti e i loro indirizzi."""
    keys = set(url_key(x['url']) for x in job['results'])
    for x in job['results']:
        keys.update(url_key(u) for u in (x.get('alsoUrl') or []))
    sig_of = lambda x: (_compact(x.get('title'))[:60], x.get('price'), x.get('km'), x.get('year'))
    twins = dict((sig_of(x), x) for x in job['results'] if x.get('km') is not None)
    cars = {}
    for x in job['results']:
        if _exact_km(x):
            cars.setdefault((x.get('price'), x.get('km')), []).append(x)
    for x in items:
        k = url_key(x['url'])
        if k in keys:
            continue
        keys.add(k)
        x['k'] = mark_key(x['url'])
        car = car_sig(x)
        if car:
            x['sg'] = car
        fresh = marks_note_seen(job, x)
        sig = sig_of(x)
        first = twins.get(sig) if x.get('km') is not None else None
        if first is not None and (first.get('site'), _host(first.get('url'))) == (x.get('site'), _host(x.get('url'))):
            first = None  # stesso sito e stesso titolo: due auto uguali dello stesso venditore
        if first is None and _exact_km(x):
            first = next((c for c in cars.get((x.get('price'), x.get('km')), [])
                          if _host(c.get('url')) != _host(x.get('url')) and (c.get('year') == x.get('year') or None in (c.get('year'), x.get('year')))), None)
        if first is not None:
            label = x.get('site') or _host(x.get('url'))
            if label == first.get('site'):
                label = '%s %s' % (label, x.get('country') or '')  # lo stesso sito in un altro paese
            if label.strip() not in (first.get('also') or []):
                first.setdefault('also', []).append(label.strip())
                first.setdefault('alsoUrl', []).append(x['url'])
            if x['k'] not in (first.get('ks') or []):
                first.setdefault('ks', []).append(x['k'])
            if not fresh:
                first['new'] = False  # la stessa auto era gia' uscita su quest'altro sito
            if first.get('unk') and not x.get('unk'):
                first['unk'] = []  # l'altro sito dichiara anche i dati che qui mancavano
            for f in ('year', 'gear', 'fuel', 'power', 'seller'):
                if first.get(f) in (None, '') and x.get(f) not in (None, ''):
                    first[f] = x[f]
            if first.get('iva') is None and x.get('iva') is not None:
                first['iva'] = x['iva']
            if not first.get('img') and x.get('img'):
                first['img'], first['imgs'] = x['img'], x.get('imgs') or [x['img']]
            continue
        if x.get('km') is not None:
            twins.setdefault(sig, x)
        if _exact_km(x):
            cars.setdefault((x.get('price'), x.get('km')), []).append(x)
        x['new'] = fresh
        job['results'].append(x)


def run_job(job_id, payload):
    cfg = get_config()
    job = JOBS[job_id]
    crit = payload.get('criteria') or {}
    known = [str(k).lower().replace('www.', '') for k in (payload.get('known') or [])]
    direct = make_fetch_direct(job)
    use_browser = bool(payload.get('browser')) and payload.get('mode') != 'bd'
    # modo misto: la lettura diretta (gratuita) dove il sito la ammette, Bright Data solo per i siti che non rispondono
    use_bd = bool(payload.get('bdFallback')) and payload.get('mode') != 'bd' and bool(cfg['apiKey'] and cfg['zone'])
    usage = {'n': 0, 'ok': 0, 'err': 0, 'fail': ''}
    if use_bd:
        with JOBS_LOCK:
            job['bd'] = usage
    def bd_scan(task):
        """La stessa lettura fatta da Bright Data, con le pagine scelte dall'utente (ogni pagina e' una richiesta)."""
        t2 = dict(task)
        if task.get('urls'):
            t2['urls'] = [c for c in task['urls'] if isinstance(c, dict)][:3]
        try:
            return scan_site(t2, crit, job, make_fetch_bd(cfg, task.get('country'), usage))
        except Exception as e:
            log_error('lettura con Bright Data di %s' % task.get('site', '?'), e)
            return 'errore', [], 'Errore imprevisto (%s).' % type(e).__name__, {'read': 0, 'drop': 0, 'why': 'errore'}

    def bd_after(task):
        """Per le pagine composte dal browser: se il browser del computer non ce l'ha fatta, ci prova Bright Data."""
        if not use_bd or job.get('cancel') or usage.get('fail'):
            return None
        return bd_scan(task)

    bq, worker = queue.Queue(), None
    if use_browser:
        worker = threading.Thread(target=browser_worker, args=(job, crit, bq, bd_after), daemon=True)
        worker.start()

    def do_site(i, task):
        try:
            fetch = make_fetch_bd(cfg, task.get('country')) if payload.get('mode') == 'bd' else direct
            status, items, msg, stats = scan_site(task, crit, job, fetch)
        except Exception as e:  # una pagina strana non deve fermare le altre
            log_error('lettura di %s' % task.get('site', '?'), e)
            status, items, msg, stats = 'errore', [], 'Errore imprevisto (%s: %s). Dettagli nel file errore.txt.' % (type(e).__name__, str(e)[:100]), {'read': 0, 'drop': 0}
        note = ''
        need = stats.get('why') in ('regole', 'bloccato', 'errore', 'vuoto')
        # pagina composta dal browser: la legge prima il browser del computer, che non costa nulla; Bright Data solo se il browser non riesce
        js_first = need and bool(task.get('js')) and use_browser
        # pagina letta con pochissimi annunci, mentre la pagina stessa ne dichiara almeno dieci: e' arrivata a meta'
        thin = (not need and 'why' not in stats and 0 < stats.get('read', 0) < THIN_PAGE and stats.get('total', 0) >= 10 and payload.get('mode') != 'bd')
        if use_bd and thin and not job.get('cancel') and not usage.get('fail'):
            with JOBS_LOCK:
                job['tasks'][i].update({'status': 'bd', 'n': len(items), 'msg': 'Pochi annunci: la rilegge Bright Data.'})
            s2, items2, msg2, stats2 = bd_scan(task)
            if 'why' not in stats2 and stats2.get('read', 0) > stats.get('read', 0):
                have = set(url_key(x['url']) for x in items2)
                merged = items2 + [x for x in items if url_key(x['url']) not in have]
                with JOBS_LOCK:
                    job['tasks'][i].update({'status': 'ok' if merged else 'vuoto', 'n': len(merged), 'unk': _unk_n(merged), 'msg': msg2, 'read': stats2['read'], 'drop': stats2['drop'], 'via': 'brightdata',
                                            'note': 'La lettura diretta aveva dato solo %d annunci.' % stats.get('read', 0)})
                    _add_results(job, merged)
                return
        if use_bd and need and not js_first and not job.get('cancel') and not usage.get('fail'):
            with JOBS_LOCK:
                job['tasks'][i].update({'status': 'bd', 'n': 0, 'msg': 'Lo sta leggendo Bright Data.'})
            s2, items2, msg2, stats2 = bd_scan(task)
            if 'why' not in stats2:  # pagina letta e annunci riconosciuti (validi o fuori dai filtri): il sito e' a posto
                with JOBS_LOCK:
                    job['tasks'][i].update({'status': s2, 'n': len(items2), 'unk': _unk_n(items2), 'msg': msg2, 'read': stats2['read'], 'drop': stats2['drop'], 'via': 'brightdata'})
                    _add_results(job, items2)
                return
            if stats2.get('why') == 'zero':  # la pagina e' arrivata e dice che per questa ricerca non c'e' nulla: inutile aprirla anche con il browser
                with JOBS_LOCK:
                    job['tasks'][i].update({'status': 'vuoto', 'n': 0, 'msg': msg2, 'read': 0, 'drop': 0, 'via': 'brightdata'})
                return
            note = 'Bright Data: ' + (msg2 or 'nessun annuncio.')
            if stats2.get('why') == 'vuoto' and stats.get('why') != 'vuoto':
                status, msg, stats = s2, msg2, dict(stats2)  # pagina ottenuta ma senza annunci riconoscibili: resta questo l'esito, se il browser non fa meglio
        # ...poi, se e' attiva, la lettura con il browser del computer (che compone anche le pagine fatte da programmi)
        if use_browser and stats.get('why') in ('regole', 'bloccato', 'errore', 'vuoto') and not job.get('cancel'):
            with JOBS_LOCK:
                job['tasks'][i].update({'status': 'coda', 'n': 0, 'msg': 'In attesa della lettura con il browser.', 'first': msg, 'why': stats['why'], 'note': note})
            bq.put((i, task))
            return
        with JOBS_LOCK:
            job['tasks'][i].update({'status': status, 'n': len(items), 'unk': _unk_n(items), 'msg': msg, 'read': stats['read'], 'drop': stats['drop'], 'note': note})
            _add_results(job, items)

    def do_disc(i, d):
        status, items, msg = scan_discover(cfg, d, known)
        with JOBS_LOCK:
            job['tasks'][i].update({'status': status, 'n': len(items), 'msg': msg})
            have = set(f['domain'] for f in job['found'])
            for f in items:
                if f['domain'] not in have:
                    have.add(f['domain'])
                    job['found'].append(f)

    with ThreadPoolExecutor(max_workers=6) as ex:  # siti diversi in parallelo; sullo stesso sito le letture restano una alla volta, con la pausa
        n = len(payload['jobs'])
        for i, task in enumerate(payload['jobs']):
            ex.submit(do_site, i, task)
        for j, d in enumerate(payload.get('discover') or []):
            ex.submit(do_disc, n + j, d)
    if worker:
        bq.put(None)
        worker.join()
    with JOBS_LOCK:
        net = job.get('net') or {}
        read_any = any(t.get('status') in ('ok', 'vuoto') for t in job['tasks'])
        if payload.get('mode') != 'bd' and not net.get('ok') and not read_any:  # nessuna risposta da nessun sito: il problema e' del collegamento, non dei siti
            kinds = sorted((k for k in net if k != 'ok'), key=lambda k: -net[k])
            if kinds:
                job['hint'] = NET_HINTS.get(kinds[0], NET_HINTS['altro'])
        job['done'] = True
    marks_flush()


def browser_worker(job, crit, bq, bd_after=None):
    """Legge con il browser del computer i siti in coda, uno alla volta. Si ferma se parte una ricerca nuova.
    bd_after(task) = lettura di riserva con Bright Data per le pagine composte dal browser, quando il browser non riesce."""
    def reserve(i, task):
        if not (bd_after and task.get('js')):
            return False
        with JOBS_LOCK:
            job['tasks'][i].update({'status': 'bd', 'n': 0, 'msg': 'Lo sta leggendo Bright Data.'})
        res = bd_after(task)
        if not res or 'why' in res[3]:
            return False
        s2, items2, msg2, stats2 = res
        with JOBS_LOCK:
            job['tasks'][i].update({'status': s2, 'n': len(items2), 'unk': _unk_n(items2), 'msg': msg2, 'read': stats2['read'], 'drop': stats2['drop'], 'via': 'brightdata'})
            _add_results(job, items2)
        return True

    opened, fail, reopened = False, '', 0
    try:
        while True:
            item = bq.get()
            if item is None:
                break
            i, task = item
            if job.get('cancel') and not fail:
                fail = 'Lettura interrotta: e\' partita una ricerca nuova.'
            if not fail and not opened:
                with JOBS_LOCK:
                    job['reader'] = {'state': 'avvio'}
                READER.lock.acquire()
                try:
                    READER.hidden = not job.get('showReader')  # di norma nascosto; con finestra solo se l'utente l'ha chiesto
                    READER.open()
                    opened = True
                    with JOBS_LOCK:
                        job['reader'] = {'state': 'attivo', 'name': READER.name, 'hidden': READER.hidden}
                except ReaderError as e:
                    READER.lock.release()
                    fail = str(e)
                    with JOBS_LOCK:
                        job['reader'] = {'state': 'assente', 'msg': fail}
            if fail:
                if reserve(i, task):
                    continue
                with JOBS_LOCK:
                    t = job['tasks'][i]
                    t.update({'status': 'errore' if t.get('why') == 'errore' else ('vuoto' if t.get('why') == 'vuoto' else 'bloccato'),
                              'msg': t.get('first') or REFUSED, 'note': ((t.get('note') + ' ') if t.get('note') else '') + fail})
                continue
            with JOBS_LOCK:
                job['tasks'][i].update({'status': 'browser', 'msg': 'Il browser sta leggendo il sito.'})
            for attempt in (1, 2):
                try:
                    status, items, msg, stats = scan_site(dict(task, pages=min(BROWSER_PAGES, int(task.get('pages') or 1))), crit, job, READER.fetch, challenge=False)
                except Exception as e:
                    log_error('lettura con il browser di %s' % task.get('site', '?'), e)
                    status, items, msg, stats = 'errore', [], 'Errore imprevisto (%s: %s). Dettagli nel file errore.txt.' % (type(e).__name__, str(e)[:100]), {'read': 0, 'drop': 0}
                if not READER.broken or attempt == 2 or reopened:
                    break
                reopened += 1  # la finestra e' stata chiusa a meta' lettura: la si riapre una volta sola
                try:
                    READER.close()
                    READER.open()
                except ReaderError as e:
                    fail = str(e)
                    break
            if READER.broken and not fail:
                fail = msg
            if stats.get('why') in ('regole', 'bloccato', 'errore', 'vuoto') and reserve(i, task):
                continue
            with JOBS_LOCK:
                job['tasks'][i].update({'status': status, 'n': len(items), 'unk': _unk_n(items), 'msg': msg, 'read': stats['read'], 'drop': stats['drop'], 'via': 'browser'})
                _add_results(job, items)
    finally:
        if opened:
            try:
                pending = bool(READER.pending) and not READER.broken
                READER.finish()
            except Exception as e:
                pending = False
                log_error('chiusura del browser', e)
            READER.lock.release()
            with JOBS_LOCK:
                job['reader'] = {'state': 'verifica' if pending else 'chiuso', 'name': READER.name}


def retry_job(job_id):
    """Rilegge con il browser i siti che avevano chiesto una verifica, dopo che l'utente ha risposto nella finestra."""
    job = JOBS.get(job_id)
    if not job:
        raise ValueError('Ricerca non trovata.')
    with JOBS_LOCK:
        if not job['done']:
            raise ValueError('La ricerca e\' ancora in corso.')
        specs = job.get('specs') or []
        todo = [(i, specs[i]) for i, t in enumerate(job['tasks']) if t.get('status') == 'verifica' and i < len(specs)]
        if not todo:
            raise ValueError('Non ci sono siti da rileggere.')
        job['done'], job['cancel'] = False, False
        for i, _ in todo:
            job['tasks'][i].update({'status': 'coda', 'msg': 'In attesa della lettura con il browser.'})

    def run():
        bq = queue.Queue()
        for it in todo:
            bq.put(it)
        bq.put(None)
        try:
            browser_worker(job, job.get('criteria') or {}, bq)
        finally:
            with JOBS_LOCK:
                job['done'] = True
            marks_flush()
    threading.Thread(target=run, daemon=True).start()
    return len(todo)


def _new_job(tasks, criteria, mode, done=False):
    job_id = uuid.uuid4().hex[:12]
    with JOBS_LOCK:
        for old in sorted(JOBS, key=lambda k: JOBS[k]['at'])[:-5]:  # si tengono solo le ultime scansioni
            JOBS.pop(old, None)
        for other in JOBS.values():  # le pagine lette si conservano solo per la scansione in corso
            other['diag'] = []
        JOBS[job_id] = {'tasks': tasks, 'results': [], 'found': [], 'done': done, 'diag': [], 'criteria': criteria, 'mode': mode, 'at': time.time()}
    return job_id


def start_job(payload):
    cfg = get_config()
    mode = 'bd' if payload.get('mode') == 'bd' else 'direct'
    if mode == 'bd' and (not cfg['apiKey'] or not cfg['zone']):
        raise ValueError('Manca la chiave Bright Data o il nome della zona: apri le impostazioni.')
    jobs = [j for j in (payload.get('jobs') or []) if isinstance(j, dict) and (str(j.get('url', '')).startswith('http') or j.get('urls'))]
    disc = [d for d in (payload.get('discover') or []) if isinstance(d, dict) and str(d.get('url', '')).startswith('https://www.google.')]
    if mode != 'bd':
        disc = []  # la ricerca su Google passa solo da Bright Data
    if not jobs:
        raise ValueError('Nessun sito da scansionare.')
    if len(jobs) + len(disc) > MAX_PAGES_PER_SCAN:
        raise ValueError('Troppe pagine in una sola scansione (massimo %d).' % MAX_PAGES_PER_SCAN)
    payload = dict(payload, jobs=jobs, discover=disc, mode=mode)
    tasks = [{'site': j.get('site', ''), 'country': j.get('country', ''), 'status': 'attesa', 'n': 0, 'msg': '', 'read': 0, 'drop': 0} for j in jobs]
    tasks += [{'site': 'Google', 'country': d.get('country', ''), 'status': 'attesa', 'n': 0, 'msg': ''} for d in disc]
    with JOBS_LOCK:
        for other in JOBS.values():  # una ricerca nuova ferma la lettura con il browser di quella precedente
            if not other.get('done'):
                other['cancel'] = True
    job_id = _new_job(tasks, payload.get('criteria') or {}, mode)
    JOBS[job_id]['specs'] = jobs
    JOBS[job_id]['showReader'] = bool(payload.get('showReader'))
    threading.Thread(target=run_job, args=(job_id, payload), daemon=True).start()
    return job_id


def import_page(payload):
    """Annunci da una pagina che l'utente ha aperto e copiato a mano (Ctrl+A, Ctrl+C, Ctrl+V)."""
    html = str(payload.get('html') or '')
    if len(html) < 200:
        raise ValueError('Non vedo una pagina copiata. Sulla pagina dei risultati premi Ctrl+A e poi Ctrl+C, torna qui e premi Ctrl+V nel riquadro.')
    hosts = {}
    for h in re.findall(r'href=["\'](https?://[^"\'>\s]+)', html):
        net = urlparse(h).netloc.lower()
        if net and not any(w in net for w in ('facebook.', 'instagram.', 'twitter.', 'youtube.', 'linkedin.', 'google.', 'apple.', 'x.com')):
            hosts[net] = hosts.get(net, 0) + 1
    if not hosts:
        raise ValueError('Nel testo incollato non ci sono link agli annunci. Copia la pagina direttamente dal browser (Ctrl+A, Ctrl+C sulla pagina dei risultati).')
    host = max(hosts, key=hosts.get)
    base = 'https://' + host + '/'
    bare = host.replace('www.', '')
    name, country = bare, TLD_CC.get(bare.rsplit('.', 1)[-1], '')
    for k in payload.get('known') or []:
        d = str(k.get('d') or '').lower().split('/')[0].replace('www.', '')
        if d and (bare == d or bare.endswith('.' + d) or d.endswith('.' + bare)):
            name, country = str(k.get('n') or bare), str(k.get('c') or country)
            break
    if bare.startswith('autoscout24.'):
        name = 'AutoScout24'  # il paese di ogni annuncio e' scritto nella sua scheda
    crit = payload.get('criteria') or {}
    task = {'site': name, 'country': country, 'trust': []}
    found, kept, dropped = _judge_page(task, crit, html, base)
    job_id = str(payload.get('job') or '')
    if job_id not in JOBS:
        job_id = _new_job([], crit, 'manuale', done=True)
    job = JOBS[job_id]
    _diag(job, task, base, 'incollata', html, '%d annunci letti' % len(found))
    with JOBS_LOCK:
        job['tasks'].append({'site': name, 'country': country, 'status': 'ok' if kept else 'vuoto', 'n': len(kept), 'unk': _unk_n(kept), 'manual': True,
                             'msg': _summary(len(found), kept, dropped) if found else 'Nessun annuncio riconosciuto nella pagina incollata.', 'read': len(found), 'drop': dropped})
        _add_results(job, kept)
    marks_flush()
    unk = sum(1 for x in kept if x.get('unk'))
    return {'job': job_id, 'site': name, 'read': len(found), 'ok': len(kept) - unk, 'unk': unk, 'drop': dropped}


def export_csv(job):
    buf = io.StringIO()
    w = csv.writer(buf, delimiter=';', lineterminator='\r\n')
    w.writerow(['Veicolo', 'Prezzo EUR', 'Km', 'Anno', 'Cambio', 'Alimentazione', 'Potenza CV', 'Paese', 'Sito', 'Venditore', 'IVA detraibile', 'Dati mancanti', 'Link', 'Interessante', 'Nuovo'])
    pub = marks_public()
    hid, fav = set(pub['hiddenKeys']), set(pub['favKeys'])
    for r in sorted(job['results'], key=lambda x: (bool(x.get('unk')), x.get('price') is None, x.get('price') or 0)):
        if hid & set(item_keys(r)):
            continue  # annuncio nascosto dall'utente
        w.writerow([r.get('title', ''), r.get('price') or '', r.get('km') if r.get('km') is not None else '', r.get('year') or '',
                    GEAR_LABEL.get(r.get('gear'), ''), FUEL_LABEL.get(r.get('fuel'), ''), r.get('power') or '', r.get('country', ''), r.get('site', ''), r.get('seller', ''),
                    'si' if r.get('iva') else '', ', '.join(r.get('unk') or []), r.get('url', ''), 'si' if fav & set(item_keys(r)) else '', 'si' if r.get('new') else ''])
    return ('﻿' + buf.getvalue()).encode('utf-8')


def diag_zip(job):
    """Archivio con le pagine lette nell'ultima scansione e il riepilogo: non contiene chiavi ne' dati personali."""
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as z:
        pages = []
        for i, d in enumerate(job['diag']):
            name = '%02d_%s_%s.html' % (i + 1, re.sub(r'[^a-z0-9]+', '-', d['site'].lower()).strip('-') or 'sito', d['country'] or 'xx')
            pages.append({'file': name if d['html'] else '', 'site': d['site'], 'country': d['country'], 'url': d['url'], 'code': d['code'], 'note': d['note']})
            if d['html']:
                z.writestr(name, d['html'])
        summary = {'programma': VERSION, 'presentazione': UA, 'modo': job.get('mode'), 'filtri': job.get('criteria'), 'siti': job['tasks'], 'pagine': pages, 'annunci': job['results']}
        z.writestr('riepilogo.json', json.dumps(summary, ensure_ascii=False, indent=1))
    return buf.getvalue()


# --------------------------------------------------------------------------
# Lettura con il browser del computer
#
# Alcuni siti rispondono solo a un browser e non a un programma. Per questi il
# programma apre una finestra di Chrome o Edge sul computer dell'utente, con un
# profilo separato da quello di tutti i giorni, le fa visitare la pagina dei
# risultati e legge gli annunci che vi compaiono.
# Limiti voluti: solo quando l'utente avvia una ricerca; una pagina per sito;
# un sito alla volta. Il browser si presenta per quello che e' (nessuna modifica
# a nome, impronte o segnali) e il programma non risponde alle verifiche
# ("sei un umano?") ne' ai riquadri dei cookie: se un sito chiede qualcosa, la
# pagina resta aperta e decide l'utente.
# --------------------------------------------------------------------------
READER_WAIT = float(os.environ.get('CV_READER_WAIT') or 20)  # secondi al massimo per pagina
READER_GAP = float(os.environ.get('CV_READER_GAP') or 1.5)   # secondi tra due pagine dello stesso sito
READER_ARGS = [a for a in (os.environ.get('CV_BROWSER_ARGS') or '').split(' ') if a]  # solo per le prove
SERVER_URL = ''  # indirizzo del programma, noto dopo l'avvio
NEEDS_BROWSER = ('Per leggere in automatico i siti che rispondono solo a un browser serve Google Chrome oppure Microsoft Edge '
                 'installato su questo computer (sono gratuiti).')
ASKS_CHECK = 'Il sito ha chiesto una verifica prima di mostrare gli annunci: la pagina resta aperta nella finestra del browser.'


def find_browsers():
    """Browser adatti presenti sul computer: [(nome, percorso)], il preferito per primo."""
    out = []

    def add(name, path):
        path = (path or '').strip().strip('"')
        if path and os.path.isfile(path) and all(os.path.normcase(p) != os.path.normcase(path) for _, p in out):
            out.append((name, path))

    add('Browser', os.environ.get('CV_BROWSER') or '')
    if sys.platform.startswith('win'):
        roots = [os.environ.get(k) for k in ('PROGRAMFILES', 'PROGRAMFILES(X86)', 'PROGRAMW6432', 'LOCALAPPDATA')]
        table = (('Google Chrome', 'Google\\Chrome\\Application\\chrome.exe', 'chrome.exe'),
                 ('Microsoft Edge', 'Microsoft\\Edge\\Application\\msedge.exe', 'msedge.exe'),
                 ('Brave', 'BraveSoftware\\Brave-Browser\\Application\\brave.exe', 'brave.exe'),
                 ('Vivaldi', 'Vivaldi\\Application\\vivaldi.exe', 'vivaldi.exe'),
                 ('Chromium', 'Chromium\\Application\\chrome.exe', ''))
        try:
            import winreg
        except ImportError:
            winreg = None
        for name, rel, exe in table:
            for r in roots:
                if r:
                    add(name, os.path.join(r, rel))
            if winreg and exe:
                for hive in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
                    try:
                        with winreg.OpenKey(hive, 'SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\App Paths\\' + exe) as k:
                            add(name, winreg.QueryValue(k, None))
                    except OSError:
                        pass
    elif sys.platform == 'darwin':
        for name, app, exe in (('Google Chrome', 'Google Chrome.app', 'Google Chrome'), ('Microsoft Edge', 'Microsoft Edge.app', 'Microsoft Edge'),
                               ('Brave', 'Brave Browser.app', 'Brave Browser'), ('Vivaldi', 'Vivaldi.app', 'Vivaldi'), ('Chromium', 'Chromium.app', 'Chromium')):
            for root in ('/Applications', os.path.expanduser('~/Applications')):
                add(name, os.path.join(root, app, 'Contents', 'MacOS', exe))
    else:
        for name, exe in (('Google Chrome', 'google-chrome'), ('Google Chrome', 'google-chrome-stable'), ('Chromium', 'chromium'),
                          ('Chromium', 'chromium-browser'), ('Microsoft Edge', 'microsoft-edge'), ('Brave', 'brave-browser')):
            add(name, shutil.which(exe) or '')
    return out


class ReaderError(Exception):
    pass


class _WS(object):
    """Collegamento WebSocket essenziale (solo testo), quanto basta per parlare con il browser del computer."""

    def __init__(self, url, timeout=10):
        u = urlparse(url)
        self.sock = socket.create_connection((u.hostname, u.port), timeout=timeout)
        key = base64.b64encode(os.urandom(16)).decode('ascii')
        self.sock.sendall(('GET %s HTTP/1.1\r\nHost: %s:%d\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n'
                           'Sec-WebSocket-Key: %s\r\nSec-WebSocket-Version: 13\r\n\r\n' % (u.path, u.hostname, u.port, key)).encode('ascii'))
        self.buf = bytearray()
        self.parts = []
        self.next_id = 0
        deadline = time.time() + timeout
        while b'\r\n\r\n' not in self.buf:
            self._more(deadline)
        head, _, rest = bytes(self.buf).partition(b'\r\n\r\n')
        if b' 101' not in head.split(b'\r\n', 1)[0]:
            raise ConnectionError('il browser ha rifiutato il collegamento')
        self.buf = bytearray(rest)

    def _more(self, deadline):
        left = deadline - time.time()
        if left <= 0:
            raise TimeoutError()
        self.sock.settimeout(max(left, 0.05))
        try:
            chunk = self.sock.recv(262144)
        except socket.timeout:
            raise TimeoutError()
        if not chunk:
            raise ConnectionError('il browser ha chiuso il collegamento')
        self.buf += chunk

    def _frame(self, deadline):
        """Un frame intero, oppure TimeoutError senza aver consumato nulla (si potra' riprovare)."""
        while len(self.buf) < 2:
            self._more(deadline)
        b0, b1 = self.buf[0], self.buf[1]
        ln, pos = b1 & 0x7F, 2
        if ln == 126:
            while len(self.buf) < 4:
                self._more(deadline)
            ln, pos = struct.unpack('>H', bytes(self.buf[2:4]))[0], 4
        elif ln == 127:
            while len(self.buf) < 10:
                self._more(deadline)
            ln, pos = struct.unpack('>Q', bytes(self.buf[2:10]))[0], 10
        mask = None
        if b1 & 0x80:
            while len(self.buf) < pos + 4:
                self._more(deadline)
            mask, pos = bytes(self.buf[pos:pos + 4]), pos + 4
        while len(self.buf) < pos + ln:
            self._more(deadline)
        data = bytes(self.buf[pos:pos + ln])
        del self.buf[:pos + ln]
        if mask:
            data = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
        return b0 & 0x80, b0 & 0x0F, data

    def _send(self, opcode, data):
        n = len(data)
        head = bytearray([0x80 | opcode])
        if n < 126:
            head.append(0x80 | n)
        elif n < 65536:
            head.append(0x80 | 126)
            head += struct.pack('>H', n)
        else:
            head.append(0x80 | 127)
            head += struct.pack('>Q', n)
        mask = os.urandom(4)
        head += mask
        body = bytes(b ^ mask[i % 4] for i, b in enumerate(data))
        self.sock.settimeout(10)
        self.sock.sendall(bytes(head) + body)

    def recv(self, timeout):
        deadline = time.time() + timeout
        while True:
            fin, op, data = self._frame(deadline)
            if op == 0x8:
                raise ConnectionError('il browser ha chiuso il collegamento')
            if op == 0x9:
                self._send(0xA, data)
                continue
            if op == 0xA:
                continue
            self.parts.append(data)
            if fin:
                text = b''.join(self.parts).decode('utf-8', 'replace')
                self.parts = []
                return text

    def call(self, method, params=None, timeout=15):
        """Un comando al browser e la sua risposta. Gli avvisi a comparsa della pagina vengono chiusi, cosi' non la bloccano."""
        self.next_id += 1
        mid = self.next_id
        self._send(0x1, json.dumps({'id': mid, 'method': method, 'params': params or {}}).encode('utf-8'))
        deadline = time.time() + timeout
        while True:
            left = deadline - time.time()
            if left <= 0:
                raise TimeoutError(method)
            msg = json.loads(self.recv(left))
            if msg.get('id') == mid:
                if 'error' in msg:
                    raise ReaderError(str((msg['error'] or {}).get('message') or 'errore del browser'))
                return msg.get('result') or {}
            if msg.get('method') == 'Page.javascriptDialogOpening':
                self.next_id += 1
                kind = (msg.get('params') or {}).get('type')
                self._send(0x1, json.dumps({'id': self.next_id, 'method': 'Page.handleJavaScriptDialog',
                                            'params': {'accept': kind == 'beforeunload'}}).encode('utf-8'))

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass


def _cdp_http(port, path, method='GET', timeout=4):
    c = http.client.HTTPConnection('127.0.0.1', port, timeout=timeout)
    try:
        c.request(method, path)
        r = c.getresponse()
        return r.status, r.read().decode('utf-8', 'replace')
    finally:
        c.close()


def _free_port():
    s = socket.socket()
    try:
        s.bind(('127.0.0.1', 0))
        return s.getsockname()[1]
    finally:
        s.close()


PROBE_JS = ("(function(){try{var d=document,b=d.body,p=(performance.getEntriesByType?performance.getEntriesByType('navigation')[0]:null)||{};"
            "return JSON.stringify({rs:d.readyState,n:d.documentElement?d.documentElement.outerHTML.length:0,a:d.links.length,"
            "t:(d.title||'').slice(0,200),u:location.href,code:p.responseStatus||0,tx:b?(b.innerText||'').length:0});}catch(e){return ''}})()")
SCROLL_JS = ("(function(){var e=document.documentElement,b=document.body||e,h=Math.max(e.scrollHeight,b.scrollHeight);"
             "window.scrollBy(0,Math.round(window.innerHeight*0.85));return JSON.stringify({y:window.scrollY,h:h,ih:window.innerHeight});})()")
CH_TITLE = re.compile(r'just a moment|attention required|access denied|zugriff verweigert|acc[eè]s refus|acceso denegado|accesso negato|are you (?:a )?(?:human|robot)|'
                      r'captcha|robot check|pardon our interruption|unusual traffic|security check|sicherheits(?:pr|ab)|bist du ein mensch|sei un umano|'
                      r'(?:^|\W)(?:un instant|einen moment|un momento)\W*$|\bblocked\b|\bbloqu', re.I)
CH_MARK = re.compile(r'captcha-delivery\.com|challenges\.cloudflare\.com|cf-challenge|cf_chl_|px-captcha|perimeterx|hcaptcha\.com/1|/recaptcha/api2/bframe|'
                     r'geetest|arkoselabs|_Incapsula_Resource|distil_r_captcha|datadome\.co/captcha', re.I)
WALL_MARK = re.compile(r'sp_message_container|didomi-popup|didomi-notice|onetrust-banner|usercentrics|CybotCookiebot|cmp-container|consent-wall|cookie-wall|privacy-wall', re.I)


class Reader(object):
    """La finestra del browser usata per leggere. Una sola per volta: chi la usa tiene il lucchetto."""

    def __init__(self):
        self.lock = threading.Lock()
        self.proc = None
        self.port = 0
        self.ws = None
        self.tab = ''
        self.name = ''
        self.pending = []  # indirizzi che hanno chiesto una verifica, da lasciare aperti all'utente
        self.last = {}     # ultima visita per sito
        self.broken = False  # la finestra non risponde piu' (chiusa a mano, per esempio)
        self.hidden = True   # di norma legge senza aprire nessuna finestra; diventa False solo se l'utente chiede di vederla

    # ---- avvio e chiusura ----
    def profile_dir(self):
        return os.path.join(data_dir(), 'profilo-browser')

    def _alive(self, port):
        try:
            return _cdp_http(port, '/json/version', timeout=1.5)[0] == 200
        except (OSError, http.client.HTTPException):
            return False

    def _state_path(self):
        return os.path.join(data_dir(), 'lettore.json')

    @staticmethod
    def _close_port(port):
        """Chiude un browser di lettura rimasto aperto, data la sua porta."""
        try:
            ws = _WS(json.loads(_cdp_http(port, '/json/version')[1])['webSocketDebuggerUrl'], timeout=4)
            try:
                ws.call('Browser.close', timeout=4)
            except (ReaderError, TimeoutError, OSError):
                pass
            ws.close()
        except (OSError, ValueError, KeyError, http.client.HTTPException, TimeoutError):
            pass

    def _running_port(self):
        """Porta di un browser di lettura rimasto aperto da prima, se e' dello stesso tipo (nascosto o con finestra)."""
        st = load_json(self._state_path(), {}) if os.path.exists(self._state_path()) else {}
        try:
            port = int(st.get('port') or 0)
        except (TypeError, ValueError):
            port = 0
        if not port or not self._alive(port):
            return 0
        if bool(st.get('hidden', False)) != bool(self.hidden):
            self._close_port(port)  # era aperto nell'altro modo (finestra <-> nascosto): lo chiudo e riparto
            return 0
        return port

    def open(self):
        """Apre (o ritrova) la finestra di lettura. ReaderError con un messaggio per l'utente se non e' possibile."""
        self.pending, self.broken = [], False
        port = self.port if self.port and self._alive(self.port) else self._running_port()
        if port and not self.name:
            self.name = str(load_json(self._state_path(), {}).get('browser') or 'browser')
        if not port:
            browsers = find_browsers()
            if not browsers:
                raise ReaderError(NEEDS_BROWSER)
            prof = self.profile_dir()
            try:
                os.makedirs(prof, exist_ok=True)
            except OSError as e:
                raise ReaderError('Non riesco a preparare la cartella per il browser (%s).' % e)
            err = ''
            for name, exe in browsers:
                port = _free_port()
                args = [exe, '--remote-debugging-port=%d' % port, '--user-data-dir=' + prof, '--no-first-run', '--no-default-browser-check',
                        '--window-size=1200,900', '--mute-audio', '--deny-permission-prompts', '--hide-crash-restore-bubble']
                if self.hidden:
                    args.append('--headless=new')  # legge le pagine senza aprire nessuna finestra sullo schermo
                else:
                    args += ['--new-window', '--window-position=60,40']
                if sys.platform == 'darwin':
                    args.append('--use-mock-keychain')
                elif not sys.platform.startswith('win'):
                    args.append('--password-store=basic')
                args += READER_ARGS + [(SERVER_URL or 'about:blank') + ('lettore' if SERVER_URL else '')]
                try:
                    self.proc = subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, close_fds=True)
                except OSError as e:
                    err, port = str(e), 0
                    continue
                t0 = time.time()
                while time.time() - t0 < 25 and not self._alive(port):
                    if self.proc.poll() is not None and time.time() - t0 > 2 and not self._running_port():
                        break  # il browser si e' chiuso subito
                    time.sleep(0.3)
                if self._alive(port):
                    self.name = name
                    try:
                        save_json(self._state_path(), {'port': port, 'browser': name, 'hidden': self.hidden})
                    except OSError:
                        pass
                    break
                other = self._running_port()  # la finestra era gia' aperta: il nuovo avvio le ha solo passato l'indirizzo
                if other:
                    port, self.name = other, name
                    break
                err, port = 'il browser non ha accettato il collegamento', 0
                try:
                    self.proc.terminate()
                except OSError:
                    pass
            if not port:
                raise ReaderError('Non sono riuscito ad aprire il browser per la lettura (%s).' % (err or 'nessuna risposta'))
        self.port = port
        self._attach()

    def _attach(self):
        """Si collega alla scheda di lavoro; le altre schede rimaste da prima vengono chiuse."""
        if self.ws:
            self.ws.close()
            self.ws = None
        try:
            pages = [t for t in json.loads(_cdp_http(self.port, '/json/list')[1]) if t.get('type') == 'page' and t.get('webSocketDebuggerUrl')]
            if not pages:
                pages = [json.loads(_cdp_http(self.port, '/json/new?about:blank', 'PUT')[1])]
            main = pages[0]
            for t in pages[1:]:
                _cdp_http(self.port, '/json/close/' + t['id'])
            self.tab = main['id']
            self.ws = _WS(main['webSocketDebuggerUrl'])
            self.ws.call('Page.enable')
        except (OSError, ValueError, KeyError, http.client.HTTPException, TimeoutError) as e:
            raise ReaderError('Non riesco a collegarmi alla finestra del browser (%s).' % (e or type(e).__name__))

    def close(self):
        """Chiude la finestra di lettura."""
        port, self.port = self.port, 0
        if self.ws:
            self.ws.close()
            self.ws = None
        if port:
            try:
                ws = _WS(json.loads(_cdp_http(port, '/json/version')[1])['webSocketDebuggerUrl'], timeout=4)
                try:
                    ws.call('Browser.close', timeout=4)
                except (ReaderError, TimeoutError, OSError):
                    pass
                ws.close()
            except (OSError, ValueError, KeyError, http.client.HTTPException, TimeoutError):
                pass
        if self.proc is not None:
            try:
                self.proc.wait(timeout=6)
            except (subprocess.TimeoutExpired, OSError):
                pass
            self.proc = None

    def finish(self):
        """A fine lettura: se qualche sito ha chiesto una verifica le sue pagine restano aperte, altrimenti la finestra si chiude."""
        if not self.pending or not self.port:
            self.close()
            return
        try:
            first = True
            for u in self.pending[:6]:
                if first:
                    self.ws.call('Page.navigate', {'url': u}, timeout=10)
                    first = False
                else:
                    _cdp_http(self.port, '/json/new?' + u, 'PUT')
        except (ReaderError, OSError, TimeoutError, http.client.HTTPException):
            pass
        if self.ws:
            self.ws.close()
            self.ws = None

    # ---- lettura di una pagina ----
    def _eval(self, expr, timeout=12):
        try:
            r = self.ws.call('Runtime.evaluate', {'expression': expr, 'returnByValue': True}, timeout)
        except ReaderError:
            return None  # la pagina sta cambiando: si riprova al giro dopo
        if r.get('exceptionDetails'):
            return None
        return (r.get('result') or {}).get('value')

    def _probe(self):
        raw = self._eval(PROBE_JS)
        try:
            return json.loads(raw) if raw else None
        except ValueError:
            return None

    def read(self, url):
        """Apre l'indirizzo nella scheda di lavoro e aspetta che la pagina sia ferma. Restituisce (dati della pagina, html)."""
        p = urlparse(url)
        host = p.netloc.lower()
        if p.scheme not in ('http', 'https') or (_private_host(host) and not TEST_ORIGIN):
            raise ReaderError('Indirizzo non valido.')
        target = url
        if TEST_ORIGIN:
            target = TEST_ORIGIN + '/' + host + (p.path or '/') + ('?' + p.query if p.query else '')
        wait = self.last.get(host, 0) + READER_GAP - time.time()
        if wait > 0:
            time.sleep(wait)
        try:
            try:
                r = self.ws.call('Page.navigate', {'url': target}, timeout=30)
            finally:
                self.last[host] = time.time()
            if r.get('errorText'):
                raise ReaderError('Il browser non e\' riuscito ad aprire la pagina (%s).' % r['errorText'].replace('net::', ''))
            t0, last, still, calm, info = time.time(), None, 0, 0, None
            while time.time() - t0 < READER_WAIT:
                time.sleep(0.6)
                now = self._probe()
                if not now or now.get('u', '').startswith(('about:', 'chrome-error:')):
                    continue
                info = now
                sig = (now['n'] // 3000, now['a'])
                still = still + 1 if (now['rs'] == 'complete' and sig == last) else 0
                calm = calm + 1 if sig == last else 0
                last = sig
                if still >= 2 and time.time() - t0 >= 2.4:
                    break
                if calm >= 5 and time.time() - t0 >= 6:  # la pagina non cambia piu', anche se qualche elemento secondario sta ancora caricando
                    break
            if not info:
                raise ReaderError('La pagina non si e\' caricata nel browser.')
            html = self._eval('document.documentElement.outerHTML', timeout=20) or ''
        except (OSError, TimeoutError) as e:
            self.broken = True
            raise ReaderError('La finestra del browser non risponde piu\' (%s): forse e\' stata chiusa.' % (e or type(e).__name__))
        if TEST_ORIGIN:
            info['u'] = url
        return info, html

    def scrolled(self):
        """Scorre la pagina fino in fondo, come farebbe una persona, e la rilegge: molti siti mostrano gli annunci man mano."""
        try:
            for _ in range(8):
                raw = self._eval(SCROLL_JS)
                pos = json.loads(raw) if raw else None
                time.sleep(0.3)
                if not pos or pos['y'] + pos['ih'] >= pos['h'] - 40:
                    break
            time.sleep(0.8)
            return self._eval('document.documentElement.outerHTML', timeout=20) or ''
        except (OSError, TimeoutError, ValueError, KeyError):
            return ''

    def fetch(self, url):
        """Per scan_site: ('ok', [pagine], indirizzo) oppure ('verifica' | 'assente' | 'errore', messaggio, None)."""
        try:
            info, html = self.read(url)
        except ReaderError as e:
            return 'errore', str(e), None
        final, code = info.get('u') or url, int(info.get('code') or 0)
        if code in (404, 410):
            return 'assente', 'Pagina non trovata sul sito.', None
        pages = [html]
        n = len(extract_listings(html, final))
        if n < 12 and code < 400:
            more = self.scrolled()
            if more:
                m = len(extract_listings(more, final))
                if m:
                    pages.append(more)
                n = max(n, m)
        if n == 0:
            few = int(info.get('a') or 0) < 25
            if code in (401, 403, 429, 503) or CH_TITLE.search(info.get('t') or '') or (few and CH_MARK.search(html)) \
                    or (few and int(info.get('tx') or 0) < 1500 and WALL_MARK.search(html)):
                if self.hidden:  # leggendo in nascosto non c'e' una pagina da mostrare: il sito resta tra quelli da aprire a mano
                    return 'bloccato', 'Il sito chiede una verifica: aprilo tu dai link qui sotto.', None
                self.pending.append(url)
                return 'verifica', ASKS_CHECK, None
            if code >= 500:
                return 'errore', 'Il sito ha risposto con un errore (%d).' % code, None
        return 'ok', pages, final


READER = Reader()


def reader_status():
    b = find_browsers()
    return {'found': bool(b), 'name': b[0][0] if b else ''}


LETTORE_PAGE = """<!DOCTYPE html><html lang="it"><head><meta charset="utf-8"><title>Cercaveicoli: lettura dei siti</title>
<style>body{font-family:system-ui,-apple-system,"Segoe UI",sans-serif;background:#eef0ec;color:#17211d;margin:0;display:flex;min-height:100vh;align-items:center;justify-content:center}
div{max-width:560px;padding:32px;background:#fff;border:1px solid #d3d9d2;border-radius:10px}h1{font-size:24px;margin:0 0 12px}p{font-size:16px;line-height:1.5;margin:0 0 10px}</style></head>
<body><div><h1>Cercaveicoli sta leggendo i siti</h1>
<p>Questa finestra visita le pagine dei risultati, una alla volta, e legge gli annunci. Non serve fare nulla: a fine lettura si chiude da sola.</p>
<p>Se un sito chiede una verifica o una scelta sui cookie, la sua pagina resta aperta qui: rispondi tu, poi nel programma premi "Rileggi".</p></div></body></html>"""


# --------------------------------------------------------------------------
# Server locale
# --------------------------------------------------------------------------
STALE = 'Questa scheda è rimasta aperta da prima e non è più valida: premi F5 per aggiornarla, oppure chiudila e usa quella che si apre da sola quando avvii il programma.'


class Server(ThreadingHTTPServer):
    """Su Windows una porta gia' occupata va rifiutata: altrimenti due copie del programma finiscono sulla stessa porta
    e la pagina parla con quella sbagliata."""
    daemon_threads = True
    allow_reuse_address = not sys.platform.startswith('win')

    def server_bind(self):
        if sys.platform.startswith('win'):
            try:
                self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
            except (AttributeError, OSError):
                pass
        ThreadingHTTPServer.server_bind(self)


def instance_at(port):
    """Chi risponde su quella porta: None se non e' Cercaveicoli, altrimenti quello che dice di se' (versione, avvio)."""
    try:
        c = http.client.HTTPConnection('127.0.0.1', port, timeout=1.5)
        try:
            c.request('GET', '/api/ping')
            r = c.getresponse()
            body = r.read(4000)
            server = r.getheader('Server') or ''
        finally:
            c.close()
    except (OSError, http.client.HTTPException):
        return None
    if 'Cercaveicoli' not in server:
        return None
    try:
        info = json.loads(body.decode('utf-8', 'replace'))
    except ValueError:
        info = {}
    return info if isinstance(info, dict) else {}


def same_program(port):
    """Vero se su quella porta risponde questo stesso programma (stessa cartella, stessa versione)."""
    try:
        c = http.client.HTTPConnection('127.0.0.1', port, timeout=1.5)
        try:
            c.request('GET', '/api/status', headers={'X-CV-Token': TOKEN, 'X-CV-Page': VERSION})
            return c.getresponse().status == 200
        finally:
            c.close()
    except (OSError, http.client.HTTPException):
        return False


class Handler(BaseHTTPRequestHandler):
    server_version = 'Cercaveicoli/' + VERSION

    def log_message(self, fmt, *args):
        pass

    def _send(self, code, body, ctype='application/json; charset=utf-8', extra=None):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', ctype)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _host_ok(self):
        host = (self.headers.get('Host') or '').split(':')[0]
        return host in ('127.0.0.1', 'localhost')

    def _page_ok(self):
        """La pagina dice di che versione e': una scheda aperta con una versione precedente va aggiornata, non usata."""
        return (self.headers.get('X-CV-Page') or '') == VERSION

    def _auth(self, query=None):
        tok = self.headers.get('X-CV-Token') or ((query or {}).get('t') or [''])[0]
        return self._host_ok() and secrets.compare_digest(tok, TOKEN)

    def _safe(self, fn):
        """Un errore imprevisto non deve lasciare la pagina senza risposta: lo si annota e lo si dice."""
        try:
            fn()
        except (BrokenPipeError, ConnectionError):
            pass
        except Exception as e:
            log_error(self.command + ' ' + self.path.split('?')[0], e)
            try:
                self._send(500, {'error': 'Errore interno del programma (%s: %s). I dettagli sono nel file errore.txt, nella cartella del programma: mandalo a chi ti segue.'
                                 % (type(e).__name__, str(e)[:120])})
            except Exception:
                pass

    def do_GET(self):
        self._safe(self._get)

    def do_POST(self):
        self._safe(self._post)

    def _get(self):
        u = urlparse(self.path)
        q = parse_qs(u.query)
        if not self._host_ok():
            return self._send(403, {'error': 'Accesso consentito solo da questo computer.'})
        if u.path in ('/', '/index.html'):
            with open(INDEX_PATH, 'r', encoding='utf-8') as f:
                page = f.read()
            page = page.replace('<!--CV_LOCAL-->', '<script>window.CV_LOCAL=%s;</script>' % json.dumps({'token': TOKEN, 'boot': BOOT, 'version': VERSION}))
            return self._send(200, page.encode('utf-8'), 'text/html; charset=utf-8')
        if u.path == '/favicon.ico':
            return self._send(204, b'', 'image/x-icon')
        if u.path == '/lettore':  # prima pagina della finestra di lettura: spiega a che cosa serve
            return self._send(200, LETTORE_PAGE.encode('utf-8'), 'text/html; charset=utf-8')
        if not u.path.startswith('/api/'):
            return self._send(404, {'error': 'Non trovato.'})
        if u.path == '/api/ping':  # la pagina chiede ogni tanto se il programma e' ancora quello di prima
            return self._send(200, {'ok': True, 'app': 'cercaveicoli', 'version': VERSION, 'boot': BOOT}, extra={'Access-Control-Allow-Origin': '*'})
        if not self._auth(q):
            return self._send(403, {'error': STALE})
        if u.path not in ('/api/export', '/api/diag') and not self._page_ok():
            return self._send(409, {'error': STALE})
        if u.path == '/api/update':
            return self._send(200, update_status())
        if u.path == '/api/status':
            return self._send(200, public_status())
        if u.path == '/api/sites':
            return self._send(200, load_json(SITES_PATH, []))
        if u.path == '/api/marks':
            return self._send(200, marks_public())
        if u.path.startswith('/api/scan/'):
            job = JOBS.get(u.path.rsplit('/', 1)[1])
            if not job:
                return self._send(404, {'error': 'Scansione non trovata.'})
            with JOBS_LOCK:
                return self._send(200, {'tasks': job['tasks'], 'results': job['results'], 'found': job['found'], 'done': job['done'], 'hint': job.get('hint', ''),
                                        'reader': job.get('reader') or {}, 'bd': job.get('bd') or None})
        if u.path == '/api/export':
            job = JOBS.get((q.get('job') or [''])[0])
            if not job:
                return self._send(404, {'error': 'Scansione non trovata.'})
            name = 'cercaveicoli_%s.csv' % time.strftime('%Y-%m-%d_%H%M')
            return self._send(200, export_csv(job), 'text/csv; charset=utf-8', {'Content-Disposition': 'attachment; filename="%s"' % name})
        if u.path == '/api/diag':
            job = JOBS.get((q.get('job') or [''])[0])
            if not job:
                return self._send(404, {'error': 'Scansione non trovata.'})
            name = 'cercaveicoli_diagnostica_%s.zip' % time.strftime('%Y-%m-%d_%H%M')
            return self._send(200, diag_zip(job), 'application/zip', {'Content-Disposition': 'attachment; filename="%s"' % name})
        return self._send(404, {'error': 'Non trovato.'})

    def _post(self):
        u = urlparse(self.path)
        if not self._auth():
            return self._send(403, {'error': STALE})
        if not self._page_ok():
            return self._send(409, {'error': STALE})
        try:
            n = int(self.headers.get('Content-Length') or 0)
            limit = 40000000 if u.path == '/api/import' else 2000000
            data = json.loads(self.rfile.read(n).decode('utf-8') or 'null') if 0 < n < limit else None
        except ValueError:
            return self._send(400, {'error': 'Dati non validi.'})
        if u.path == '/api/config':
            data = data or {}
            cfg = load_json(CONFIG_PATH, {})
            new_key = str(data.get('apiKey') or '').strip()
            cfg['zone'] = str(data.get('zone') or '').strip()
            cfg['serpZone'] = str(data.get('serpZone') or '').strip()
            check = bd_check(dict(get_config(), apiKey=new_key or get_config()['apiKey']))
            if new_key and not check.get('badKey'):
                cfg['apiKey'] = new_key
            if check.get('ok'):
                if not cfg['zone'] and check.get('unlocker'):
                    cfg['zone'] = check['unlocker'][0]
                if not cfg['serpZone'] and check.get('serp'):
                    cfg['serpZone'] = check['serp'][0]
                if cfg['zone'] and check.get('zones') and cfg['zone'] not in [z[0] for z in check['zones']]:
                    check['ok'] = False
                    check['msg'] += ' Attenzione: la zona "%s" non è tra queste.' % cfg['zone']
                elif not cfg['zone']:
                    check['ok'] = False
                    check['msg'] += ' Non vedo una zona Web Unlocker: creala nel pannello Bright Data e scrivi qui il nome.'
            save_json(CONFIG_PATH, cfg)
            return self._send(200, public_status({'check': {'ok': check.get('ok'), 'msg': check.get('msg')}}))
        if u.path == '/api/update':
            data = data or {}
            if 'auto' in data:  # la scelta "aggiorna da solo" resta nelle impostazioni
                cfg = load_json(CONFIG_PATH, {})
                cfg['autoUpdate'] = bool(data['auto'])
                save_json(CONFIG_PATH, cfg)
            if data.get('check') and not os.environ.get('CV_NO_UPDATE'):
                threading.Thread(target=update_worker, args=(0,), daemon=True).start()
                time.sleep(0.2)
            if data.get('install'):
                threading.Thread(target=apply_update, daemon=True).start()
                time.sleep(0.3)
            return self._send(200, update_status())
        if u.path == '/api/sites':
            if not isinstance(data, list):
                return self._send(400, {'error': 'Elenco non valido.'})
            clean = [{'name': str(s.get('name', ''))[:80], 'country': str(s.get('country', ''))[:3], 'url': str(s.get('url', ''))[:400]}
                     for s in data[:200] if isinstance(s, dict)]
            save_json(SITES_PATH, clean)
            return self._send(200, clean)
        if u.path == '/api/marks':
            try:
                return self._send(200, marks_op(data))
            except ValueError as e:
                return self._send(400, {'error': str(e)})
        if u.path == '/api/scan':
            try:
                return self._send(200, {'job': start_job(data or {})})
            except ValueError as e:
                return self._send(400, {'error': str(e)})
        if u.path == '/api/retry':
            try:
                return self._send(200, {'n': retry_job(str((data or {}).get('job') or ''))})
            except ValueError as e:
                return self._send(400, {'error': str(e)})
        if u.path == '/api/import':
            if not isinstance(data, dict):
                return self._send(400, {'error': 'La pagina incollata e\' troppo grande o non valida.'})
            try:
                return self._send(200, import_page(data))
            except ValueError as e:
                return self._send(400, {'error': str(e)})
        return self._send(404, {'error': 'Non trovato.'})


def _flag(name, max_age):
    """Legge e cancella un appunto lasciato dall'avvio precedente (riavvio dopo un aggiornamento); None se non c'e' o e' vecchio."""
    path = os.path.join(data_dir(), name)
    d = load_json(path, None) if os.path.exists(path) else None
    try:
        os.remove(path)
    except OSError:
        pass
    return d if isinstance(d, dict) and time.time() - float(d.get('when') or 0) < max_age else None


def main():
    global SERVER_URL
    try:
        sys.stdout.reconfigure(errors='replace')  # un carattere che la finestra non sa mostrare non deve fermare il programma
    except Exception:
        pass
    if '--prova' in sys.argv:
        sys.exit(self_test())
    # un aggiornamento gia' scaricato e controllato si installa adesso, prima di partire
    if auto_update_on():
        try:
            m = _pending()
            if m and install_update(m):
                print('Installata la versione %s: riavvio.' % m['version'])
                save_json(os.path.join(data_dir(), 'riavvio.json'), {'when': time.time(), 'open': True})
                restart_program()
        except Exception as e:
            log_error('installazione dell\'aggiornamento all\'avvio', e)
    again = _flag('riavvio.json', 90)       # riavviato da solo dopo un aggiornamento: la pagina e' gia' aperta e si ricollega
    done = _flag('aggiornato.json', 3600)
    if done and done.get('to') == VERSION:
        UPD['from'] = str(done.get('from') or '')
    port = int(os.environ.get('CV_PORT') or 8765)
    httpd, old = None, 0
    for p in range(port, port + 20):
        try:
            httpd = Server(('127.0.0.1', p), Handler)
            break
        except OSError:
            other = instance_at(p)
            if other is not None and other.get('version') == VERSION and same_program(p):
                print('Il programma era gia\' in funzione: riapro la sua scheda nel browser.')
                print('(Puoi chiudere questa finestra.)')
                sys.stdout.flush()
                if not os.environ.get('CV_NO_BROWSER'):
                    webbrowser.open('http://127.0.0.1:%d/' % p)
                    time.sleep(3)
                return
            if other is not None:
                old += 1
            continue
    if httpd is None:
        print('Non trovo una porta libera per avviare il programma.')
        sys.exit(1)
    url = 'http://127.0.0.1:%d/' % httpd.server_address[1]
    SERVER_URL = url
    atexit.register(_shutdown_reader)
    atexit.register(marks_flush)
    try:
        if adopt_old_config():
            print('Ho ripreso la chiave Bright Data salvata nella versione precedente.')
    except Exception as e:
        log_error('ripresa delle impostazioni precedenti', e)
    print('Cercaveicoli Import %s in funzione.' % VERSION)
    if old:
        print('Nota: c\'e\' ancora aperta un\'altra finestra nera del programma, di prima.')
        print('      Puoi chiuderla: questa nuova non ne ha bisogno.')
    print('Apri il browser su: ' + url)
    print('Per chiudere il programma chiudi questa finestra.')
    sys.stdout.flush()
    if not os.environ.get('CV_NO_BROWSER') and (not again or again.get('open')):
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    if not os.environ.get('CV_NO_UPDATE'):
        threading.Thread(target=update_worker, daemon=True).start()
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass


def _shutdown_reader():
    try:
        if READER.port:
            READER.close()
    except Exception:
        pass


if __name__ == '__main__':
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:  # qualunque cosa impedisca l'avvio resta scritta, invece di una finestra che si chiude
        log_error('avvio', exc)
        print('')
        print('Il programma non e\' riuscito a partire: %s: %s' % (type(exc).__name__, exc))
        print('I dettagli sono nel file errore.txt, in questa cartella: mandalo a chi ti segue il programma.')
        sys.exit(1)
