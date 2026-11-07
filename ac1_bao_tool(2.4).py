#!/usr/bin/env python3
"""
AC1 BAO Tool v2 (PC) - extraccion rapida en espanol + importar/encodear

Flujo:
  1) Extraer espanol rapido : usa el plan (ac1_spanish_plan.json.gz o los CSV de data.zip) y descomprime solo
                              las entradas de los .forge que contienen headers espanoles. Crea spanish_map.csv.
  2) WAV                    : decodifica los streams Spanish_BAO_0x... (IMA Ubi) con decodificador interno.
  3) Importar               : WAV editado -> IMA -> mismo hueco del forge (tamano y header intactos).
Conserva el escaneo completo anterior (pestana Avanzado / comando 'full').

CLI: python ac1_bao_tool.py fast|wav|import|check|full ...   (sin argumentos abre la GUI)
Dependencias: customtkinter (GUI). Opcionales: numpy (remuestreo mejor), python-lzo (mas rapido).
"""
import os, re, sys, csv, mmap, struct, shutil, subprocess, threading, wave, argparse, tempfile, zlib
from concurrent.futures import ThreadPoolExecutor

try:
    import lzo as _lzo
except Exception:
    _lzo = None

FORGE_MAGIC = b'scimitar\x00'
FILEDATA_HDR = 440
BAO_VER = b'\x01\x1b\x01\x00'
COMP_SIG = b'\x33\xaa\xfb\x57\x99\xfa\x04\x10'
NAME_RE = re.compile(r'^(?P<lang>.+?)_BAO_0x(?P<id>[0-9a-fA-F]{8})$')
BAO_RE = re.compile(r'^BAO_0x(?P<id>[0-9a-fA-F]{8})$')
HEADER_RE = re.compile(r'^BAO_0x20[0-9a-fA-F]{6}$')
TYPE_NAMES = {1: 'Audio', 2: 'Random', 3: 'Selector', 5: 'Sequence', 6: 'Layer', 8: 'Silence'}


# ------------------------------------------------------------------ LZO1X
def lzo1x_decompress(src, expected=None):
    """Descompresor LZO1X puro Python (formato minilzo, sin cabecera)."""
    if _lzo is not None:
        return _lzo.decompress(bytes(src), False, expected or len(src) * 8)
    out = bytearray()
    ip, n = 0, len(src)
    t = src[ip]
    state = 'top'
    if t > 17:
        ip += 1
        t -= 17
        out += src[ip:ip + t]; ip += t
        state = 'match_next' if t < 4 else 'first_literal'
    while True:
        if state == 'top':
            t = src[ip]; ip += 1
            if t >= 16:
                state = 'match'
            else:
                if t == 0:
                    while src[ip] == 0:
                        t += 255; ip += 1
                    t += 15 + src[ip]; ip += 1
                t += 3
                out += src[ip:ip + t]; ip += t
                state = 'first_literal'
        if state == 'first_literal':
            t = src[ip]; ip += 1
            if t >= 16:
                state = 'match'
            else:  # M1 tras literales: copia 3 bytes
                m = len(out) - (1 + 0x0800) - (t >> 2) - (src[ip] << 2); ip += 1
                for k in range(3):
                    out.append(out[m + k])
                state = 'match_done'
        if state == 'match':
            if t >= 64:      # M2
                m = len(out) - 1 - ((t >> 2) & 7) - (src[ip] << 3); ip += 1
                cnt = (t >> 5) - 1 + 2
            elif t >= 32:    # M3
                cnt = t & 31
                if cnt == 0:
                    while src[ip] == 0:
                        cnt += 255; ip += 1
                    cnt += 31 + src[ip]; ip += 1
                m = len(out) - 1 - ((src[ip] >> 2) + (src[ip + 1] << 6)); ip += 2
                cnt += 2
            elif t >= 16:    # M4 / fin
                m = len(out) - ((t & 8) << 11)
                cnt = t & 7
                if cnt == 0:
                    while src[ip] == 0:
                        cnt += 255; ip += 1
                    cnt += 7 + src[ip]; ip += 1
                m -= (src[ip] >> 2) + (src[ip + 1] << 6); ip += 2
                if m == len(out):
                    break    # EOF
                m -= 0x4000
                cnt += 2
            else:            # M1 tras match: copia 2 bytes
                m = len(out) - 1 - (t >> 2) - (src[ip] << 2); ip += 1
                cnt = 2
            if m < 0:
                raise ValueError('LZO: referencia invalida')
            for k in range(cnt):
                out.append(out[m + k])
            state = 'match_done'
        if state == 'match_done':
            t = src[ip - 2] & 3
            if t == 0:
                state = 'top'
                continue
            out += src[ip:ip + t]; ip += t
            t = src[ip]; ip += 1
            state = 'match'
            continue
        if state == 'match_next':
            t = src[ip]; ip += 1
            state = 'match'
    return bytes(out)


# ------------------------------------------------------------------ FORGE
class ForgeEntry:
    __slots__ = ('name', 'offset', 'size')
    def __init__(self, name, offset, size):
        self.name, self.offset, self.size = name, offset, size


def parse_forge(buf):
    """Devuelve lista de ForgeEntry (offset = inicio del dato, sin FILEDATA header)."""
    if buf[:9] != FORGE_MAGIC:
        raise ValueError('no es un forge scimitar')
    ver, info_off = struct.unpack_from('<II', buf, 9)
    if ver >= 0x1b:
        raise ValueError('forge VER 0x%X no soportado (solo < 0x1B, AC1 PC)' % ver)
    p = info_off + 12 + 4 + 8            # total, unknown, dummy9, dummy10(u32), dummy11(q)
    _files_max, chunk_count = struct.unpack_from('<II', buf, p); p += 8
    chunk_next = struct.unpack_from('<q', buf, p)[0]
    entries, guard = [], 0
    cn = chunk_next
    while cn > 0 and guard < 64:
        guard += 1
        files, _u, start, nxt, _mn, _mx, name_off, _data_off = struct.unpack_from('<IIqqIIqq', buf, cn)
        for i in range(files):
            off, _z, _h, size = struct.unpack_from('<IIII', buf, start + i * 16)
            raw = buf[name_off + i * 188 + 44: name_off + i * 188 + 44 + 0x80]
            name = bytes(raw).split(b'\0')[0].decode('latin1')
            entries.append(ForgeEntry(name, off + FILEDATA_HDR, size))
        cn = nxt
    return entries


# ------------------------------------------------------- .compressed / BAO
def decompress_chunk(ztype, raw, size):
    if ztype == 1:
        return lzo1x_decompress(raw, size)
    raise NotImplementedError('ZTYPE %d no soportado (1=LZO1X)' % ztype)


def unpack_compressed(buf, stats):
    """Replica del bloque COMPRESSED del BMS. Devuelve lista de paquetes descomprimidos."""
    packs, off, n = [], 0, len(buf)
    while off < n:
        s = buf.find(COMP_SIG, off)
        if s < 0:
            break
        p = s + 8
        _ver, ztype, _maxs, _maxz, chunks = struct.unpack_from('<HBHHH', buf, p); p += 9
        tbl = [struct.unpack_from('<HH', buf, p + 4 * i) for i in range(chunks)]; p += 4 * chunks
        out = bytearray()
        try:
            for size, zsize in tbl:
                p += 4                                   # crc
                raw = bytes(buf[p:p + zsize]); p += zsize
                out += raw if size == zsize else decompress_chunk(ztype, raw, size)
            packs.append(bytes(out))
        except NotImplementedError as e:
            stats['unsupported'] = stats.get('unsupported', 0) + 1
            stats.setdefault('unsupported_msg', str(e))
        except Exception as e:
            stats['errors'] = stats.get('errors', 0) + 1
            stats.setdefault('error_msg', repr(e))
        off = p
    return packs


def extract_baos(pack):
    """Replica EXTRACT_BAO/WRITE_BAO del BMS: itera (nombre, bytes_bao)."""
    pos = 0
    while True:
        t = pack.find(b'BAO_0', pos)
        if t < 0:
            return
        pos = t + 1
        base = t - 0x0c
        if base < 0:
            continue
        _sid, sub_size, name_size = struct.unpack_from('<III', pack, base)
        if name_size > 64:
            continue
        name = pack[t:t + name_size].split(b'\0')[0].decode('latin1')
        pos = max(t + name_size + 1 + sub_size, t + 1)
        if not name.startswith('BAO_0x'):
            continue
        v = pack.find(BAO_VER, t, t + sub_size + name_size)
        if v < 4:
            continue
        size = struct.unpack_from('<I', pack, v - 4)[0]
        if v + size > len(pack) or size < 0x24:
            continue
        yield name, pack[v:v + size]


# ------------------------------------------------------------- EXTRACCION
def list_forges(folder):
    out = []
    for root, _d, files in os.walk(folder):
        for f in files:
            if f.lower().endswith('.forge'):
                out.append(os.path.join(root, f))
    return sorted(out)


def extract_all(forge_dir, out_dir, log=print, progress=None):
    """Extrae todos los BAO a out_dir/_store. Devuelve (idiomas, stats)."""
    store = os.path.join(out_dir, '_store')
    os.makedirs(store, exist_ok=True)
    forges = list_forges(forge_dir)
    stats = {'forges': len(forges), 'streams': 0, 'baos': 0, 'dups': 0}
    langs = set()
    for fi, fp in enumerate(forges):
        log('[%d/%d] %s' % (fi + 1, len(forges), os.path.basename(fp)))
        try:
            with open(fp, 'rb') as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                entries = parse_forge(buf)
                for e in entries:
                    data = buf[e.offset:e.offset + e.size]
                    m = NAME_RE.match(e.name)
                    if m and data[:4] == BAO_VER:                    # stream directo
                        if m.group('lang').lower() != 'common':
                            langs.add(m.group('lang'))
                        _save(store, e.name, data, stats, 'streams')
                    elif data[:4] == BAO_VER and BAO_RE.match(e.name):
                        _save(store, e.name, data, stats, 'baos')
                    elif COMP_SIG in data[:256] or data.find(COMP_SIG) >= 0:
                        for pack in unpack_compressed(data, stats):
                            for name, bao in extract_baos(pack):
                                _save(store, name, bao, stats, 'baos')
        except Exception as ex:
            log('  ERROR en %s: %r' % (os.path.basename(fp), ex))
            stats['forge_errors'] = stats.get('forge_errors', 0) + 1
        if progress:
            progress(fi + 1, len(forges))
    return sorted(langs), stats


def _save(store, name, data, stats, key):
    path = os.path.join(store, name)
    if os.path.exists(path):
        stats['dups'] += 1
        return
    with open(path, 'wb') as f:
        f.write(data)
    stats[key] += 1


def _link(src, dst):
    if os.path.exists(dst):
        os.remove(dst)
    try:
        os.link(src, dst)
    except OSError:
        shutil.copy2(src, dst)


def build_language_dir(out_dir, lang):
    """Carpeta bao/<lang>: compartido + streams del idioma como Common_BAO_0x<id>."""
    store = os.path.join(out_dir, '_store')
    dst = os.path.join(out_dir, 'bao', lang)
    os.makedirs(dst, exist_ok=True)
    pref = lang + '_BAO_0x'
    lang_streams = []
    for f in os.listdir(store):
        if f.startswith(pref):
            lang_streams.append(f)
        elif f.startswith('BAO_0x') or f.startswith('Common_BAO_0x'):
            _link(os.path.join(store, f), os.path.join(dst, f))
        elif NAME_RE.match(f):
            pass  # streams de otros idiomas: no se enlazan
    for f in lang_streams:
        bid = f[len(pref):]
        _link(os.path.join(store, f), os.path.join(dst, f))
        _link(os.path.join(store, f), os.path.join(dst, 'Common_BAO_0x' + bid))
    return dst, len(lang_streams)


# ------------------------------------------------------------------- WAV
def header_info(path):
    with open(path, 'rb') as f:
        d = f.read(0x80)
    if len(d) < 0x70 or d[:4] != BAO_VER:
        return None
    cls, = struct.unpack_from('<I', d, 0x20)
    typ, = struct.unpack_from('<I', d, 0x2C)
    ch, = struct.unpack_from('<I', d, 0x6C)
    return cls, typ, ch



# Offsets del header BAO de AC1 (vgmstream ubi_bao_config.c, case 0x001B0100; relativos a header_skip=0x28)
HEADER_SKIP = 0x28
H = dict(id=0x28, type=0x2C, stream_size=0x30, stream_id=0x44, stream_flag=0x50, loop_flag=0x5C,
         channels=0x6C, sample_rate=0x70, num_samples=0x78, num_samples2=0x80, codec=0x8C, prefetch=0x9C)
CODEC_NAMES = {0: 'XMA1', 1: 'PCM', 2: 'PSX', 3: 'UBI_IMA', 4: 'OGG', 5: 'XMA1_str', 7: 'AT3'}


def read_header(path):
    """Campos del header BAO de audio (type 1). None si no es un header valido."""
    with open(path, 'rb') as f:
        d = f.read(0xB0)
    if len(d) < 0xA0 or d[:4] != BAO_VER:
        return None
    g = lambda k: struct.unpack_from('<I', d, H[k])[0]
    gs = lambda k: struct.unpack_from('<i', d, H[k])[0]
    return dict(cls=struct.unpack_from('<I', d, 0x20)[0], type=g('type'), stream_size=g('stream_size'),
                stream_id=g('stream_id'), is_stream=gs('stream_flag') & 1, loop=gs('loop_flag') & 1,
                channels=gs('channels'), sample_rate=gs('sample_rate'), num_samples=gs('num_samples'),
                codec=g('codec'), prefetch=g('prefetch'))


def lang_stream_ids(out_dir, lang):
    """ids (int) de los streams propios del idioma, segun _store."""
    pref = lang + '_BAO_0x'
    return {int(f[len(pref):], 16) for f in os.listdir(os.path.join(out_dir, '_store')) if f.startswith(pref)}


def find_stream_ref(path, ids):
    """Header de audio cuyo stream_id (0x44) es un stream del idioma. -> (0x44, id) o None."""
    h = read_header(path)
    if h and h['type'] == 1 and h['is_stream'] and h['stream_id'] in ids:
        return H['stream_id'], h['stream_id']
    return None


def vorbis_id_info(data):
    """Primera pagina Ogg -> paquete de identificacion Vorbis. Devuelve (canales, rate) o None."""
    p = data.find(b'OggS', 0, 0x400)
    if p < 0 or p + 27 > len(data):
        return None
    nseg = data[p + 26]
    b = p + 27 + nseg
    if data[b:b + 7] != b'\x01vorbis' or b + 16 > len(data):
        return None
    ch = data[b + 11]
    rate, = struct.unpack_from('<I', data, b + 12)
    return ch, rate


def find_ogg_rate(bao_dir, header_path):
    """Rate real segun la cabecera Vorbis del prefetch BAO_0x3<id> del header. -> (rate, nombre) o None."""
    h = read_header(header_path)
    if not h or h['type'] != 1:
        return None
    name = 'BAO_0x%08x' % ((h['stream_id'] & 0x0FFFFFFF) | 0x30000000)
    p = os.path.join(bao_dir, name)
    if os.path.exists(p):
        with open(p, 'rb') as f:
            info = vorbis_id_info(f.read(0x600))
        if info:
            return info[1], name
    return None


def relabel_wav_rate(path, new_rate):
    """Cambia SOLO la etiqueta de sample rate (sin remuestrear)."""
    with wave.open(path, 'rb') as w:
        params, frames = w.getparams(), w.readframes(w.getnframes())
    tmp = path + '.tmp'
    with wave.open(tmp, 'wb') as o:
        o.setnchannels(params.nchannels); o.setsampwidth(params.sampwidth)
        o.setframerate(new_rate); o.writeframes(frames)
    os.replace(tmp, path)


def parse_rate_fix(txt):
    """'16000:11025,24000:12000' -> {16000: 11025, ...}"""
    out = {}
    for part in (txt or '').split(','):
        if ':' in part:
            a, b = part.split(':')
            out[int(a)] = int(b)
    return out


def ogg_pages(d):
    """Lista de paginas Ogg: (offset, seq, flags, granule, serial, nseg, body_declarado, bytes_disponibles)."""
    out = []
    for m in re.finditer(b'OggS', d):
        p = m.start()
        if p + 27 > len(d):
            continue
        flags = d[p + 5]
        gran, = struct.unpack_from('<q', d, p + 6)
        ser, seq = struct.unpack_from('<II', d, p + 14)
        nseg = d[p + 26]
        if p + 27 + nseg > len(d):
            out.append((p, seq, flags, gran, ser, nseg, -1, len(d) - p)); continue
        body = sum(d[p + 27:p + 27 + nseg])
        out.append((p, seq, flags, gran, ser, nseg, body, len(d) - p - 27 - nseg))
    return out


def diagnose(out_dir, lang, header, log=print):
    """Informe de un header: campos, companeros resueltos y union prefetch/stream."""
    bao_dir = os.path.join(out_dir, 'bao', lang)
    hp = os.path.join(bao_dir, header)
    d = open(hp, 'rb').read()
    log('== %s (%d bytes) idioma %s' % (header, len(d), lang))
    names = set(os.listdir(bao_dir))
    ids_lang = lang_stream_ids(out_dir, lang)
    h = read_header(hp)
    if h:
        log('-- campos (offsets vgmstream AC1): tipo %d, codec %s, canales %d, rate %d, samples %d, loop %d,\n   stream_size %d, prefetch %d, stream_flag %d, stream_id 0x%08X' % (
            h['type'], CODEC_NAMES.get(h['codec'], h['codec']), h['channels'], h['sample_rate'], h['num_samples'],
            h['loop'], h['stream_size'], h['prefetch'], h['is_stream'], h['stream_id']))
    log('-- u32 no nulos (offset: valor) y archivos que existen con ese id')
    for off in range(0x24, len(d) - 3, 4):
        v, = struct.unpack_from('<I', d, off)
        if v == 0:
            continue
        hits = []
        for cand in (v, (v & 0x0FFFFFFF) | 0x30000000, (v & 0x0FFFFFFF) | 0x50000000):
            for n in ('BAO_0x%08x' % cand, 'Common_BAO_0x%08x' % cand, '%s_BAO_0x%08x' % (lang, cand)):
                if n in names or (cand in ids_lang and n.startswith(lang)):
                    hits.append('%s(%s)' % (n, os.path.getsize(os.path.join(bao_dir, n)) if n in names else '?'))
        log('  0x%03X: %-11d 0x%08X %s' % (off, v, v, ' '.join(sorted(set(hits)))))
    ref = find_stream_ref(hp, ids_lang)
    log('-- stream de idioma referenciado: %s' % (('offset 0x%X id 0x%08X' % ref) if ref else 'NINGUNO'))
    if not ref:
        return
    sid = ref[1]
    pre = 'BAO_0x%08x' % ((sid & 0x0FFFFFFF) | 0x30000000)
    st = open(os.path.join(bao_dir, '%s_BAO_0x%08x' % (lang, sid)), 'rb').read()
    pr = open(os.path.join(bao_dir, pre), 'rb').read() if pre in names else b''
    log('-- prefetch %s: %d bytes | stream: %d bytes' % (pre, len(pr), len(st)))
    for label, buf in (('PREFETCH', pr), ('STREAM', st)):
        log('-- paginas Ogg en %s (offset, seq, flags, granule, serial, nseg, cuerpo_declarado, bytes_disponibles)' % label)
        for pg in ogg_pages(buf)[:8]:
            log('   %s' % (pg,))
        if buf:
            log('   primeros 0x30 bytes: %s' % buf[:0x30].hex(' '))
    vi = vorbis_id_info(pr) if pr else None
    log('-- cabecera Vorbis del prefetch: %s' % (('canales %d, rate %d Hz' % vi) if vi else 'no encontrada'))
    pg = ogg_pages(pr)
    if pg:
        last = pg[-1]
        log('-- ultima pagina del prefetch: seq %d, declara cuerpo %d, disponible %d -> %s' %
            (last[1], last[6], last[7], 'CORTADA (continua en el stream)' if last[6] > last[7] else 'completa'))
    sp = ogg_pages(st)
    if sp:
        log('-- stream empieza con %d bytes antes de la 1a pagina (seq %d, granule %d)' % (sp[0][0] - 0x28, sp[0][1], sp[0][3]))


def plan_language_patch(bao_dir, header_path, lang, rate_fix):
    """Calcula los valores correctos de un header de audio cuyo stream es del idioma.
    El header es el de la base (ingles): su stream_size/num_samples/rate no valen para el stream espanol."""
    h = read_header(header_path)
    if not h or h['type'] != 1 or not h['is_stream']:
        return None
    st_path = os.path.join(bao_dir, '%s_BAO_0x%08x' % (lang, h['stream_id']))
    if not os.path.exists(st_path):
        return None
    with open(st_path, 'rb') as f:
        st = f.read()
    new_size = h['prefetch'] + max(len(st) - HEADER_SKIP, 0)
    rate, samples, vorbis_rate, approx = h['sample_rate'], h['num_samples'], '', False
    if h['codec'] == 4:                                   # OGG: rate y samples salen del propio Ogg
        pre_path = os.path.join(bao_dir, 'BAO_0x%08x' % ((h['stream_id'] & 0x0FFFFFFF) | 0x30000000))
        if os.path.exists(pre_path):
            with open(pre_path, 'rb') as f:
                pre = f.read(HEADER_SKIP + h['prefetch'])[HEADER_SKIP:]
            vi = vorbis_id_info(pre)
            if vi:
                rate = vorbis_rate = vi[1]
        pages = ogg_pages(st)
        if pages and not h['loop']:
            samples = max(p[3] for p in pages)
    elif h['stream_size'] > 0 and not h['loop']:          # IMA/PCM: tamano constante por muestra
        samples = int(round(h['num_samples'] * new_size / float(h['stream_size']))); approx = True
    if rate in rate_fix:
        rate = rate_fix[rate]
    return dict(h=h, new_size=new_size, rate=rate, samples=samples, vorbis_rate=vorbis_rate, approx=approx)


def apply_language_patch(header_path, plan):
    """Reescribe el header en la carpeta del idioma (rompe el hardlink, no toca _store)."""
    with open(header_path, 'rb') as f:
        d = bytearray(f.read())
    struct.pack_into('<I', d, H['stream_size'], plan['new_size'])
    struct.pack_into('<i', d, H['sample_rate'], plan['rate'])
    if not plan['h']['loop']:
        struct.pack_into('<i', d, H['num_samples'], plan['samples'])
    os.remove(header_path)
    with open(header_path, 'wb') as f:
        f.write(d)


def export_wavs(out_dir, lang, vgm, types=(1, 5, 6), log=print, workers=None, progress=None,
                rate_fix=None, only_backed=False, patch=True):
    bao_dir = os.path.join(out_dir, 'bao', lang)
    wav_dir = os.path.join(out_dir, 'wav', lang)
    os.makedirs(wav_dir, exist_ok=True)
    rate_fix = rate_fix if rate_fix is not None else {16000: 11025}
    ids_lang = lang_stream_ids(out_dir, lang)
    jobs = []
    for f in sorted(os.listdir(bao_dir)):
        if not HEADER_RE.match(f):
            continue
        info = header_info(os.path.join(bao_dir, f))
        if not info or info[0] != 0x20000000 or info[1] not in types:
            continue
        if only_backed and info[1] == 1 and not find_stream_ref(os.path.join(bao_dir, f), ids_lang):
            continue                      # audio sin stream del idioma = solo version base (ingles)
        jobs.append((f, info))
    log('%s: %d headers a exportar' % (lang, len(jobs)))
    done = [0]

    def work(job):
        f, (cls, typ, ch) = job
        hp = os.path.join(bao_dir, f)
        wav = os.path.join(wav_dir, f + '.wav')
        h = read_header(hp) if typ == 1 else None
        plan, backed = None, 'base'
        if h and find_stream_ref(hp, ids_lang):
            backed = 'idioma'
            if patch:
                plan = plan_language_patch(bao_dir, hp, lang, rate_fix)
                if plan:
                    apply_language_patch(hp, plan)
        try:
            r = subprocess.run([vgm, '-i', '-o', wav, hp], capture_output=True, text=True, timeout=120)
            ok = r.returncode == 0 and os.path.exists(wav)
            err = '' if ok else ((r.stderr or r.stdout).strip().splitlines()[-1:] or ['?'])
        except Exception as ex:
            ok, err = False, [repr(ex)]
        rate_vgm = dur = ''
        rate_final = ''
        if ok:
            try:
                with wave.open(wav, 'rb') as w:
                    rate_vgm = w.getframerate()
                rate_final = rate_vgm
                if plan is None and h and h['sample_rate'] in rate_fix and backed == 'idioma':
                    relabel_wav_rate(wav, rate_fix[rate_vgm]); rate_final = rate_fix[rate_vgm]
                with wave.open(wav, 'rb') as w:
                    dur = round(w.getnframes() / float(w.getframerate()), 3)
            except Exception:
                pass
        done[0] += 1
        if progress:
            progress(done[0], len(jobs))
        return [lang, f, TYPE_NAMES.get(typ, typ), ch if typ == 1 else '',
                os.path.relpath(wav, out_dir) if ok else '',
                CODEC_NAMES.get(h['codec'], h['codec']) if h else '',
                h['sample_rate'] if h else '', plan['vorbis_rate'] if plan else '', rate_final,
                h['num_samples'] if h else '', (plan['samples'] if plan else ''),
                h['stream_size'] if h else '', plan['new_size'] if plan else '',
                'aprox' if plan and plan['approx'] else '', dur, backed,
                'ok' if ok else 'fail: ' + (err[0] if isinstance(err, list) else err)]

    with ThreadPoolExecutor(max_workers=workers or os.cpu_count() or 4) as ex:
        rows = list(ex.map(work, jobs))
    idx = os.path.join(out_dir, 'index_%s.csv' % lang)
    with open(idx, 'w', newline='', encoding='utf-8') as f:
        w = csv.writer(f)
        w.writerow(['idioma', 'header', 'tipo', 'canales', 'wav', 'codec', 'rate_header', 'rate_ogg', 'rate_final',
                    'samples_header', 'samples_final', 'stream_size_header', 'stream_size_real', 'samples_aprox',
                    'duracion_s', 'origen_stream', 'estado'])
        w.writerows(rows)
    ok = sum(1 for r in rows if r[-1] == 'ok')
    log('%s: %d OK, %d fallidos -> %s' % (lang, ok, len(rows) - ok, idx))
    return rows




# =====================================================================
#  NUEVO v2: IMA ADPCM (Ubi, plano), WAV, remuestreo
# =====================================================================
import json, gzip, array, math, tempfile, time, collections, multiprocessing
from concurrent.futures import ProcessPoolExecutor, as_completed
try:
    import numpy as np
except Exception:
    np = None

STREAM_HDR = 0x28            # cabecera del BAO de stream; luego va el IMA crudo
SEEK_SELECTOR = 192          # byte 0x1c: variante con tabla de seek (NO soportada al encodear)
DEFAULT_RATE = 16000
# layout del header BAO audio (confirmado con BAO_0x20a8014b): ver learn_layout, que lo revalida
SIZE_OFF, STREAM_REF_OFF, CHAN_OFF, RATE_OFF, SAMPLES_OFF = 0x30, 0x44, 0x6C, 0x70, 0x78
DEFAULT_LANG_IDX = 3         # indice de idioma dentro de los BAO localizados (3 = español en el ejemplo del usuario)
MAX_LANG_IDX = 8
LANG_LABELS = {1: 'eng', 3: 'esp'}   # 1 = base/inglés (lo que sacaba la otra herramienta), 3 = español (muestras 55581)


def parse_labels(txt):
    out = dict(LANG_LABELS)
    for part in (txt or '').replace(';', ',').split(','):
        if '=' in part:
            a, b = part.split('=', 1)
            if a.strip().isdigit() and b.strip():
                out[int(a)] = b.strip()
    return out


def base_id(name):
    """BAO_0x20a8014b -> 0x00A8014B (sin el nibble de clase), como en esp_0x00A8014B.wav"""
    return '0x%08X' % (int(name[6:], 16) & 0x0FFFFFFF)


RATE_FIX = {16000: 11025}    # observado por el usuario: los NPC dicen 16000 en el header pero suenan a ~11025


def parse_ratefix(txt):
    out = {}
    for part in (txt or '').replace(';', ',').split(','):
        if ':' in part:
            a, b = part.split(':', 1)
            if a.strip().isdigit() and b.strip().isdigit():
                out[int(a)] = int(b)
    return out
LANG = 'Spanish'
STEP = [7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 23, 25, 28, 31, 34, 37, 41, 45, 50, 55, 60, 66,
        73, 80, 88, 97, 107, 118, 130, 143, 157, 173, 190, 209, 230, 253, 279, 307, 337, 371, 408,
        449, 494, 544, 598, 658, 724, 796, 876, 963, 1060, 1166, 1282, 1411, 1552, 1707, 1878, 2066,
        2272, 2499, 2749, 3024, 3327, 3660, 4026, 4428, 4871, 5358, 5894, 6484, 7132, 7845, 8630,
        9493, 10442, 11487, 12635, 13899, 15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767]
IDX_ADJ = (-1, -1, -1, -1, 2, 4, 6, 8)


def ima_decode(payload):
    """IMA ADPCM mono, hist=0, indice=0, nibble ALTO primero (como el stream BAO de AC1)."""
    pred = idx = 0
    out = array.array('h')
    ap = out.append
    for b in payload:
        for nib in (b >> 4, b & 15):
            step = STEP[idx]
            d = step >> 3
            if nib & 4: d += step
            if nib & 2: d += step >> 1
            if nib & 1: d += step >> 2
            pred = pred - d if nib & 8 else pred + d
            if pred > 32767: pred = 32767
            elif pred < -32768: pred = -32768
            idx += IDX_ADJ[nib & 7]
            if idx < 0: idx = 0
            elif idx > 88: idx = 88
            ap(pred)
    return out


def ima_encode(samples):
    """Inverso exacto de ima_decode. Devuelve bytes (n_muestras debe ser par)."""
    n = len(samples)
    if n & 1:
        samples = list(samples) + [0]
        n += 1
    out = bytearray(n // 2)
    pred = idx = 0
    hi = True
    pos = 0
    cur = 0
    for s in samples:
        step = STEP[idx]
        diff = s - pred
        nib = 0
        if diff < 0:
            nib = 8; diff = -diff
        d = step >> 3
        if diff >= step: nib |= 4; diff -= step; d += step
        if diff >= (step >> 1): nib |= 2; diff -= step >> 1; d += step >> 1
        if diff >= (step >> 2): nib |= 1; d += step >> 2
        pred = pred - d if nib & 8 else pred + d
        if pred > 32767: pred = 32767
        elif pred < -32768: pred = -32768
        idx += IDX_ADJ[nib & 7]
        if idx < 0: idx = 0
        elif idx > 88: idx = 88
        if hi:
            cur = nib << 4
        else:
            out[pos] = cur | nib; pos += 1
        hi = not hi
    return bytes(out)


def write_wav(path, samples, rate, channels=1):
    a = array.array('h', samples)
    if sys.byteorder == 'big':
        a.byteswap()
    os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
    with wave.open(path, 'wb') as w:
        w.setnchannels(channels); w.setsampwidth(2); w.setframerate(int(rate))
        w.writeframes(a.tobytes())


def read_wav_mono(path):
    """Lee WAV PCM 8/16/24/32 bits -> (lista de enteros 16 bit mono, rate)."""
    with wave.open(path, 'rb') as w:
        ch, sw, rate, n = w.getnchannels(), w.getsampwidth(), w.getframerate(), w.getnframes()
        raw = w.readframes(n)
    if sw == 2:
        a = array.array('h'); a.frombytes(raw)
        if sys.byteorder == 'big': a.byteswap()
        vals = list(a)
    elif sw == 1:
        vals = [(b - 128) << 8 for b in raw]
    elif sw == 3:
        vals = [int.from_bytes(raw[i + 1:i + 3], 'little', signed=True) for i in range(0, len(raw) - 2, 3)]
    elif sw == 4:
        a = array.array('i'); a.frombytes(raw)
        vals = [v >> 16 for v in a]
    else:
        raise ValueError('WAV de %d bytes/muestra no soportado' % sw)
    if ch > 1:
        vals = [sum(vals[i:i + ch]) // ch for i in range(0, len(vals) - ch + 1, ch)]
    return vals, rate


def resample(vals, src, dst):
    if src == dst or not vals:
        return list(vals)
    if np is not None:
        x = np.asarray(vals, dtype=np.float64)
        if dst < src:                                  # pasa-bajos FIR (ventana Kaiser)
            fc = 0.45 * dst / src
            taps = 127
            t = np.arange(taps) - (taps - 1) / 2
            h = np.sinc(2 * fc * t) * np.kaiser(taps, 8.0)
            h /= h.sum()
            x = np.convolve(x, h, mode='same')
        n = int(round(len(x) * dst / src))
        pos = np.arange(n) * (src / dst)
        y = np.interp(pos, np.arange(len(x)), x)
        return np.clip(np.rint(y), -32768, 32767).astype(np.int64).tolist()
    # sin numpy: media movil previa (si baja) + interpolacion lineal
    x = vals
    if dst < src:
        k = max(1, int(round(src / dst)))
        if k > 1:
            x = [sum(vals[max(0, i - k // 2):i + k // 2 + 1]) // (len(vals[max(0, i - k // 2):i + k // 2 + 1]) or 1)
                 for i in range(len(vals))]
    n = int(round(len(x) * dst / src))
    out = []
    r = src / dst
    for i in range(n):
        p = i * r; j = int(p); f = p - j
        a = x[j]; b = x[j + 1] if j + 1 < len(x) else a
        out.append(int(a + (b - a) * f))
    return out


def fit_length(vals, n):
    """Ajusta EXACTAMENTE a n muestras: rellena con silencio o recorta con fade de 10 ms."""
    cut = len(vals) > n
    if cut:
        vals = vals[:n]
    else:
        vals = list(vals) + [0] * (n - len(vals))
    return vals, cut


def snr_db(ref, test):
    m = min(len(ref), len(test))
    if m == 0:
        return 0.0
    num = sum(r * r for r in ref[:m]); den = sum((r - t) ** 2 for r, t in zip(ref[:m], test[:m]))
    if den == 0: return 99.0
    if num == 0: return 0.0
    return 10 * math.log10(num / den)


# =====================================================================
#  NUEVO v2: plan (la "data") para extraer solo lo necesario en español
# =====================================================================
def _bn(p):
    return os.path.basename(str(p).replace('\\', '/'))


def build_plan_from_csv(data_dir, lang=LANG, log=print):
    """Crea el plan desde index_<lang>.csv + bao_sources.csv (los CSV del scanner)."""
    csv.field_size_limit(10 ** 9)
    def rd(name):
        with open(os.path.join(data_dir, name), newline='', encoding='utf-8-sig') as f:
            return list(csv.DictReader(f))
    log('Leyendo CSV de %s ...' % data_dir)
    idx = rd('index_%s.csv' % lang)
    headers = {r['header'] for r in idx}
    prov = collections.defaultdict(set)
    streams = {}
    with open(os.path.join(data_dir, 'bao_sources.csv'), newline='', encoding='utf-8-sig') as f:
        for r in csv.DictReader(f):
            if r['kind'] == 'bao' and r['resource'] in headers:
                prov[r['resource']].add((_bn(r['source_forge']), r['source_entry']))
            elif r['kind'] == 'stream' and r['resource'].startswith(lang + '_BAO_0x'):
                streams[r['resource']] = [_bn(r['source_forge']), int(r['size_bytes'])]
    index = {}
    for r in idx:
        ch = int(r['canales']) if r['canales'].isdigit() and int(r['canales']) < 64 else 0
        index[r['header']] = [int(r['rate']) if r['rate'] else 0,
                              float(r['duracion_s']) if r['duracion_s'] else 0.0, ch,
                              1 if r['estado'] == 'ok' else 0]
    plan = {'version': 1, 'language': lang, 'headers': sorted(headers), 'streams': streams,
            'index': index, 'provenance': {h: sorted(map(list, v)) for h, v in prov.items()}}
    plan['cover'] = plan_cover(plan, headers)
    return plan


def plan_cover(plan, wanted):
    """Minimo de (forge, entrada) que contiene todos los headers pedidos (greedy)."""
    prov = plan['provenance']
    pc = collections.defaultdict(set)
    for h in wanted:
        for f, e in prov.get(h, []):
            pc[(f, e)].add(h)
    left = set(h for h in wanted if h in prov)
    out = []
    while left:
        p = max(pc, key=lambda x: len(pc[x] & left))
        g = pc[p] & left
        if not g:
            break
        out.append([p[0], p[1], len(g)]); left -= g
    return out


def load_plan(data_dir=None, out_dir=None, log=print):
    here = os.path.dirname(os.path.abspath(__file__))
    cands = []
    if out_dir: cands.append(os.path.join(out_dir, 'spanish', 'plan_refined.json'))
    for d in (data_dir, out_dir, here):
        if d:
            cands += [os.path.join(d, 'ac1_spanish_plan.json.gz'), os.path.join(d, 'ac1_spanish_plan.json')]
    for p in cands:
        if os.path.isfile(p):
            op = gzip.open if p.endswith('.gz') else open
            with op(p, 'rt', encoding='utf-8') as f:
                plan = json.load(f)
            log('Plan cargado: %s (%d entradas a descomprimir)' % (p, len(plan['cover'])))
            return plan
    if data_dir and os.path.isfile(os.path.join(data_dir, 'bao_sources.csv')):
        plan = build_plan_from_csv(data_dir, log=log)
        if out_dir:
            os.makedirs(out_dir, exist_ok=True)
            with gzip.open(os.path.join(out_dir, 'ac1_spanish_plan.json.gz'), 'wt', encoding='utf-8') as f:
                json.dump(plan, f, separators=(',', ':'))
        log('Plan construido desde CSV (%d entradas)' % len(plan['cover']))
        return plan
    raise FileNotFoundError('No hay plan: pon ac1_spanish_plan.json.gz junto al script o indica la carpeta con los CSV (data.zip descomprimido).')


# =====================================================================
#  NUEVO v2: extraccion rapida, variante de idioma, prefetch
# =====================================================================
def _write_csv(path, header, rows):
    os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
    with open(path, 'w', newline='', encoding='utf-8') as f:
        w = csv.writer(f); w.writerow(header); w.writerows(rows)


def _u32(h, off):
    return struct.unpack_from('<I', h, off)[0]


def hdr_fields(d):
    """Campos del header BAO de audio (type 1) desde bytes; None si no vale."""
    if len(d) < 0xA0 or d[:4] != BAO_VER or _u32(d, 0x20) != 0x20000000:
        return None
    g = lambda k: _u32(d, H[k])
    return dict(type=g('type'), stream_size=g('stream_size'), stream_id=g('stream_id'),
                is_stream=struct.unpack_from('<i', d, H['stream_flag'])[0] & 1,
                channels=struct.unpack_from('<i', d, H['channels'])[0], sample_rate=g('sample_rate'),
                num_samples=g('num_samples'), codec=g('codec'), prefetch=g('prefetch'))


def data_names(sid):
    """BAO de datos que acompanan a un header: el propio stream_id (audio en memoria) y el prefetch (0x3...)."""
    return ['BAO_0x%08x' % sid, 'BAO_0x%08x' % ((sid & 0x0FFFFFFF) | 0x30000000)]


def parse_variants(pack, v, end):
    """BAO localizado: tras un prefijo vienen entradas [idx u32][size u32][BAO...] consecutivas (idx 1..n,
    una por idioma). v = offset del primer BAO_VER. Devuelve [(idx, bytes)]; sin contenedor -> [(None, bao)]."""
    size = struct.unpack_from('<I', pack, v - 4)[0]
    out = []
    if v < 8 or size < 0x24 or v + size > len(pack):
        return out
    idx = struct.unpack_from('<I', pack, v - 8)[0]
    if not (1 <= idx <= MAX_LANG_IDX):
        return [(None, pack[v:v + size])]
    out.append((idx, pack[v:v + size]))
    pos = v + size
    while pos + 12 <= min(end, len(pack)):
        nidx, nsize = struct.unpack_from('<II', pack, pos)
        if nidx != out[-1][0] + 1 or nsize < 0x24 or pack[pos + 8:pos + 12] != BAO_VER or pos + 8 + nsize > len(pack):
            break
        out.append((nidx, pack[pos + 8:pos + 8 + nsize]))
        pos += 8 + nsize
    return out


def extract_baos_ex(pack):
    """Como extract_baos pero devuelve TODAS las variantes de idioma: (nombre, [(idx, bytes), ...])."""
    pos = 0
    while True:
        t = pack.find(b'BAO_0', pos)
        if t < 0:
            return
        pos = t + 1
        base = t - 0x0c
        if base < 0:
            continue
        _sid, sub_size, name_size = struct.unpack_from('<III', pack, base)
        if name_size > 64:
            continue
        name = pack[t:t + name_size].split(b'\0')[0].decode('latin1')
        end = t + name_size + 1 + sub_size
        pos = max(end, t + 1)
        if not name.startswith('BAO_0x'):
            continue
        v = pack.find(BAO_VER, t, t + sub_size + name_size)
        if v < 4:
            continue
        vs = parse_variants(pack, v, end + 8)
        if vs:
            yield name, vs




_W_WANT = None


def _init_worker(want):
    global _W_WANT
    _W_WANT = want


def _unpack_task(task):
    """(headers {nombre: variantes}, datos {nombre: variantes}, stats) de UNA entrada del forge.
    datos = BAO de audio en memoria y prefetch que apuntan los headers de esta misma entrada."""
    path, off, size, name = task
    heads, datas, stats = {}, {}, {}
    with open(path, 'rb') as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
        data = bytes(buf[off:off + size])
    if data[:4] == BAO_VER and BAO_RE.match(name):
        if name in _W_WANT:
            heads[name] = [(None, data)]
    elif data.find(COMP_SIG) >= 0:
        for pack in unpack_compressed(data, stats):
            allb = {}
            for n, vs in extract_baos_ex(pack):
                allb.setdefault(n, vs)
            for n, vs in allb.items():
                if n in _W_WANT:
                    heads[n] = vs
                    for _k, hb in vs[:1]:
                        if len(hb) > H['stream_id'] + 4:
                            for dn in data_names(_u32(hb, H['stream_id'])):
                                if dn in allb:
                                    datas[dn] = allb[dn]
    return heads, datas, stats


def _find_forge(forges, base):
    for f in forges:
        if _bn(f).lower() == base.lower():
            return f
    return None


def pick_variant(vs, lang_idx):
    """Variante del idioma elegido; si el BAO no esta localizado (1 sola) se usa tal cual."""
    if len(vs) == 1:
        return vs[0][1]
    for i, b in vs:
        if i == lang_idx:
            return b
    return None




def detect_lang_idx(heads, stream_len, log=print):
    """Que indice de variante es el idioma pedido: el que mas veces cumple, en el header,
    stream_size - prefetch == bytes reales del stream espanol (sin su cabecera de 0x28)."""
    score = collections.Counter(); tot = 0
    for vs in heads.values():
        if len(vs) < 2:
            continue
        f0 = hdr_fields(vs[0][1])
        if not f0 or not f0['is_stream'] or f0['stream_id'] not in stream_len:
            continue
        tot += 1
        real = stream_len[f0['stream_id']] - HEADER_SKIP
        for i, b in vs:
            f = hdr_fields(b)
            if f and i is not None and f['stream_size'] - f['prefetch'] == real:
                score[i] += 1
    if tot:
        log('  deteccion de idioma: %s de %d headers localizados con stream espanol' % (dict(sorted(score.items())), tot))
    if score:
        i, n = score.most_common(1)[0]
        if n >= 0.5 * tot:
            return i
    return None


def index_streams(forge_path, lang=LANG):
    """id(int) -> (offset_dato, size, nombre) de los Spanish_BAO_0x... del forge."""
    pref = lang + '_BAO_0x'
    out = {}
    with open(forge_path, 'rb') as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
        for e in parse_forge(buf):
            if e.name.startswith(pref):
                try:
                    out[int(e.name[len(pref):], 16)] = (e.offset, e.size, e.name)
                except ValueError:
                    pass
    return out


def locate_stream_forge(forge_dir, plan, lang=LANG):
    forges = list_forges(forge_dir)
    bases = {v[0] for v in plan.get('streams', {}).values()}
    for b in bases:
        fp = _find_forge(forges, b)
        if fp: return fp
    for fp in forges:                          # plan sin esa info: probar por nombre
        if 'streamedsounds' in _bn(fp).lower() and lang[:3].lower() in _bn(fp).lower():
            return fp
    return None


def _u32(h, off):
    return struct.unpack_from('<I', h, off)[0]




def read_map(out_dir):
    with open(os.path.join(out_dir, 'spanish', 'spanish_map.csv'), newline='', encoding='utf-8-sig') as f:
        return list(csv.DictReader(f))


LANG_IDX_DEFAULT = {'Spanish': DEFAULT_LANG_IDX, 'English': 1}


def extract_all(forge_dir, out_dir, log=print, progress=None):
    """Escaneo completo (como el batch original) pero guardando TODAS las variantes de idioma:
    la primera con el nombre normal y las demas como <nombre>~L<n>."""
    store = os.path.join(out_dir, '_store')
    os.makedirs(store, exist_ok=True)
    forges = list_forges(forge_dir)
    stats = {'forges': len(forges), 'streams': 0, 'baos': 0, 'dups': 0}
    langs = set()
    for fi, fp in enumerate(forges):
        log('[%d/%d] %s' % (fi + 1, len(forges), os.path.basename(fp)))
        try:
            with open(fp, 'rb') as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                for e in parse_forge(buf):
                    data = buf[e.offset:e.offset + e.size]
                    m = NAME_RE.match(e.name)
                    if m and data[:4] == BAO_VER:
                        if m.group('lang').lower() != 'common':
                            langs.add(m.group('lang'))
                        _save(store, e.name, data, stats, 'streams')
                    elif data[:4] == BAO_VER and BAO_RE.match(e.name):
                        _save(store, e.name, data, stats, 'baos')
                    elif data.find(COMP_SIG) >= 0:
                        for pack in unpack_compressed(data, stats):
                            for name, vs in extract_baos_ex(pack):
                                for j, (k, b) in enumerate(vs):
                                    _save(store, name if j == 0 else '%s~L%s' % (name, k), b, stats, 'baos')
        except Exception as ex:
            log('  ERROR en %s: %r' % (os.path.basename(fp), ex))
            stats['forge_errors'] = stats.get('forge_errors', 0) + 1
        if progress:
            progress(fi + 1, len(forges))
    return sorted(langs), stats


def build_language_dir(out_dir, lang, lang_idx=None):
    """bao/<lang>: compartido (con la variante de ese idioma si existe) + streams del idioma como Common_BAO_0x<id>."""
    store = os.path.join(out_dir, '_store')
    dst = os.path.join(out_dir, 'bao', lang)
    os.makedirs(dst, exist_ok=True)
    idx = lang_idx if lang_idx is not None else LANG_IDX_DEFAULT.get(lang)
    pref = lang + '_BAO_0x'
    names = set(os.listdir(store))
    lang_streams = []
    for f in names:
        if '~L' in f:
            continue
        if f.startswith(pref):
            lang_streams.append(f)
        elif f.startswith('BAO_0x') or f.startswith('Common_BAO_0x'):
            alt = '%s~L%d' % (f, idx) if idx is not None else None
            _link(os.path.join(store, alt if alt in names else f), os.path.join(dst, f))
    for f in lang_streams:
        bid = f[len(pref):]
        _link(os.path.join(store, f), os.path.join(dst, f))
        _link(os.path.join(store, f), os.path.join(dst, 'Common_BAO_0x' + bid))
    return dst, len(lang_streams)


def fast_extract_spanish(forge_dir, out_dir, plan, log=print, progress=None, workers=None, lang_idx=None,
                         save_variants=False, lang_labels=None, variants_wav=False):
    """Extraccion rapida: descomprime SOLO las entradas del plan, elige la variante de idioma de cada
    header y de sus datos (prefetch / audio en memoria), copia los streams del idioma y arma bao/Spanish.
    Todo queda en <out>/spanish (mismo esquema que el batch: _store, bao/Spanish, wav/Spanish)."""
    root = os.path.join(out_dir, 'spanish')
    store = os.path.join(root, '_store')
    os.makedirs(store, exist_ok=True)
    forges = list_forges(forge_dir)
    sf = locate_stream_forge(forge_dir, plan)
    if not sf:
        raise ValueError('No encuentro el forge de streams en %s' % LANG)
    sidx = index_streams(sf)
    stream_len = {k: v[1] for k, v in sidx.items()}
    with open(sf, 'rb') as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
        for sid, (off, size, nm) in sidx.items():
            with open(os.path.join(store, nm), 'wb') as f:
                f.write(buf[off:off + size])
    log('Streams %s copiados: %d (%s)' % (LANG, len(sidx), _bn(sf)))
    want = set(plan['headers'])
    by_forge = collections.defaultdict(set)
    for f, e, _n in plan['cover']:
        by_forge[f].add(e)
    tasks = []
    for fbase, names in by_forge.items():
        fp = _find_forge(forges, fbase)
        if not fp:
            log('AVISO: no encuentro %s en %s' % (fbase, forge_dir)); continue
        with open(fp, 'rb') as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
            for e in parse_forge(buf):
                if e.name in names and e.offset + e.size <= len(buf):
                    tasks.append((fp, e.offset, e.size, e.name))
    log('Entradas a descomprimir: %d (en vez de escanear todos los forges)' % len(tasks))
    heads, datas = {}, {}
    bad = {'errors': 0, 'unsupported': 0}
    t0 = time.time()

    def take(h, d, st):
        for n, v in h.items(): heads.setdefault(n, v)
        for n, v in d.items(): datas.setdefault(n, v)
        bad['errors'] += st.get('errors', 0); bad['unsupported'] += st.get('unsupported', 0)

    done = 0
    try:
        with ProcessPoolExecutor(max_workers=workers or min(os.cpu_count() or 2, 8),
                                 initializer=_init_worker, initargs=(want,)) as ex:
            for fu in as_completed([ex.submit(_unpack_task, t) for t in tasks]):
                take(*fu.result()); done += 1
                if progress: progress(done, len(tasks))
    except Exception as exn:
        log('Procesos en paralelo no disponibles (%r); sigo en un solo proceso' % (exn,))
        _init_worker(want); heads.clear(); datas.clear(); done = 0
        for t in tasks:
            take(*_unpack_task(t)); done += 1
            if progress: progress(done, len(tasks))
    nloc = sum(1 for v in heads.values() if len(v) > 1)
    log('Headers: %d de %d esperados (%d con varios idiomas), errores LZO: %d, no soportados: %d, %.1fs' %
        (len(heads), len(want), nloc, bad['errors'], bad['unsupported'], time.time() - t0))
    idx = lang_idx
    auto = detect_lang_idx(heads, stream_len, log)
    if auto is not None:
        if idx is not None and idx != auto:
            log('  AVISO: pediste indice %s pero los datos indican %s; uso %s' % (idx, auto, auto))
        idx = auto
    if idx is None:
        idx = DEFAULT_LANG_IDX
        log('  Idioma: indice por defecto %d (no se pudo detectar)' % idx)
    else:
        log('  Indice de idioma %s = %s' % (idx, LANG))
    nh = nd = 0
    for n, vs in heads.items():
        b = pick_variant(vs, idx)
        if b is not None:
            with open(os.path.join(store, n), 'wb') as f: f.write(b)
            nh += 1
    for n, vs in datas.items():
        b = pick_variant(vs, idx)
        if b is not None:
            with open(os.path.join(store, n), 'wb') as f: f.write(b)
            nd += 1
    log('Guardados: %d headers y %d BAO de datos (prefetch / audio en memoria)' % (nh, nd))
    if save_variants:
        _save_variants(root, heads, datas, lang_labels or LANG_LABELS, variants_wav, log)
    dst, n = build_language_dir(root, LANG, idx)
    log('bao/%s listo: %d streams propios -> %s' % (LANG, n, dst))
    return heads, idx, root


def _manifest_update(odir, rows):
    """ogg/_plantilla.csv: una fila por archivo (se fusiona con lo ya existente)."""
    path = os.path.join(odir, '_plantilla.csv')
    cols = ['archivo', 'bao', 'id_base', 'indice_idioma', 'etiqueta', 'codec', 'rate', 'muestras', 'bao_datos']
    cur = {}
    if os.path.exists(path):
        with open(path, newline='', encoding='utf-8-sig') as f:
            for r in csv.DictReader(f):
                cur[r['archivo']] = [r.get(k, '') for k in cols]
    for r in rows:
        cur[r[0]] = r
    _write_csv(path, cols, [cur[k] for k in sorted(cur)])


def _ogg_info(ab):
    """(rate, muestras) leyendo el Ogg Vorbis embebido: id header y granule de la ultima pagina."""
    d = ab[HEADER_SKIP:]
    rate = samples = ''
    i = d.find(b'\x01vorbis')
    if i >= 0 and i + 16 <= len(d):
        rate = struct.unpack_from('<I', d, i + 12)[0]
    j = d.rfind(b'OggS')
    if j >= 0 and j + 14 <= len(d):
        samples = struct.unpack_from('<q', d, j + 6)[0]
    return rate, samples


def _save_variants(root, heads, datas, labels, variants_wav, log):
    """variants/<BAO>/: headers y datos crudos (.bao). ogg/<BAO>/: el audio listo (.ogg y .wav) de cada
    idioma, que sirve de plantilla para editar. Sin etiqueta conocida se usa L<n>."""
    ff = shutil.which('ffmpeg') if variants_wav else None
    vdir, odir = os.path.join(root, 'variants'), os.path.join(root, 'ogg')
    nv = nw = no = 0
    man = []
    for n, vs in heads.items():
        if len(vs) < 2: continue
        fdir = os.path.join(vdir, n); os.makedirs(fdir, exist_ok=True)
        bid = base_id(n)
        f0 = hdr_fields(vs[0][1])
        sid = f0['stream_id'] if f0 else None
        for k, b in vs:
            lab = labels.get(k, 'L%s' % k)
            with open(os.path.join(fdir, '%s_%s_header.bao' % (lab, bid)), 'wb') as f: f.write(b)
            if sid is None: continue
            for dn in data_names(sid):
                ab = dict(datas.get(dn, [])).get(k)
                if ab is None: continue
                with open(os.path.join(fdir, '%s_0x%s_data.bao' % (lab, dn[6:].upper())), 'wb') as f: f.write(ab)
                if dn != data_names(sid)[0] or ab[HEADER_SKIP:HEADER_SKIP + 4] != b'OggS':
                    continue
                gdir = os.path.join(odir, n); os.makedirs(gdir, exist_ok=True)
                fn = '%s_%s' % (lab, bid)
                with open(os.path.join(gdir, fn + '.ogg'), 'wb') as f: f.write(ab[HEADER_SKIP:])
                no += 1
                if ff and subprocess.run([ff, '-v', 'error', '-y', '-i', os.path.join(gdir, fn + '.ogg'),
                                          os.path.join(gdir, fn + '.wav')]).returncode == 0:
                    nw += 1
                rate, smp = _ogg_info(ab)
                man.append([n + '/' + fn + '.ogg', n, bid, k, lab, 'OGG', rate, smp, dn])
        nv += 1
    if man:
        _manifest_update(odir, man)
    log('Variantes: %d BAO en %s (.bao crudos). Audio por idioma en %s: %d .ogg%s, plantilla: _plantilla.csv' %
        (nv, vdir, odir, no, ', %d .wav' % nw if ff else ''))
    log('  etiquetas: %s' % ', '.join('%s=%s' % (k, v) for k, v in sorted(labels.items())))


def build_map(out_dir, plan, stream_forge, log=print, rate_fix=None):
    """spanish_map.csv desde bao/Spanish (headers ya con la variante correcta). Base de export interno e importar."""
    rf = RATE_FIX if rate_fix is None else rate_fix
    root = os.path.join(out_dir, 'spanish')
    bao_dir = os.path.join(root, 'bao', LANG)
    sidx = index_streams(stream_forge)
    index = plan.get('index', {}) if plan else {}
    rows, cross = [], collections.Counter()
    for f in sorted(os.listdir(bao_dir)):
        if not HEADER_RE.match(f): continue
        hp = os.path.join(bao_dir, f)
        h = read_header(hp)
        if not h or h['type'] != 1: continue
        sid = h['stream_id']
        streamed = bool(h['is_stream']) and sid in sidx
        src = 'stream' if streamed else 'inline'
        codec = CODEC_NAMES.get(h['codec'], str(h['codec']))
        rate, rsrc = h['sample_rate'], 'header'
        if h['codec'] == 4:
            r = find_ogg_rate(bao_dir, hp)
            if r: rate, rsrc = r[0], 'ogg'
        elif rate in rf and streamed:
            rate, rsrc = rf[rate], 'fix'
        sname = sidx[sid][2] if streamed else 'BAO_0x%08x' % sid
        size = sidx[sid][1] if streamed else 0
        plain = 1 if (streamed and h['codec'] == 3 and h['prefetch'] == 0) else 0
        cross[(h['sample_rate'], codec, src, h['prefetch'] > 0)] += 1
        info = index.get(f, [0, 0.0, 0, 0])
        rows.append([sname, f, rate, rsrc, h['channels'], size, (size - HEADER_SKIP) * 2 if streamed else '',
                     h['num_samples'], src, plain, codec, info[3], h['prefetch'], h['sample_rate'],
                     h['stream_size']])
    used = {r[0] for r in rows}
    for sid, (off, size, sname) in sorted(sidx.items()):
        if sname not in used:
            rows.append([sname, '', DEFAULT_RATE, 'default', 0, size, (size - HEADER_SKIP) * 2, '', 'stream', 0, '', 0, '', '', ''])
    _write_csv(os.path.join(root, 'spanish_map.csv'),
               ['stream', 'header', 'rate', 'rate_source', 'channels', 'stream_size', 'payload_samples',
                'header_samples', 'source', 'plain_ima', 'codec', 'vgm_ok', 'prefetch', 'header_rate', 'header_stream_size'], rows)
    log('Mapa: %d filas; importables en el mismo hueco (IMA sin prefetch): %d' % (len(rows), sum(r[9] for r in rows)))
    log('Tabla rate x codec x origen x con-prefetch:')
    for (hr, cd, sr, pf), n in sorted(cross.items(), key=lambda kv: -kv[1])[:12]:
        log('   %5d Hz | %-8s | %-6s | prefetch=%-5s -> %d' % (hr, cd, sr, pf, n))
    sp = {r[1] for r in rows if r[1]}
    if sp and plan and plan.get('provenance'):
        ref = dict(plan); ref['headers'] = sorted(sp); ref['cover'] = plan_cover(plan, sp)
        with open(os.path.join(root, 'plan_refined.json'), 'w', encoding='utf-8') as f:
            json.dump(ref, f, separators=(',', ':'))
        log('Plan refinado: %d entradas (antes %d) para la proxima vez' % (len(ref['cover']), len(plan['cover'])))
    return rows


def export_wavs_vgm(out_dir, vgm, types=(1, 5, 6), rate_fix=None, log=print, progress=None, only_backed=False):
    """WAV limpios con vgmstream-cli sobre bao/Spanish (header + prefetch + stream), como el batch original."""
    return export_wavs(os.path.join(out_dir, 'spanish'), LANG, vgm, tuple(types), log=log, progress=progress,
                       rate_fix=RATE_FIX if rate_fix is None else rate_fix, only_backed=only_backed)


# =====================================================================
#  NUEVO v2: exportar WAV (decodificador interno, en paralelo)
# =====================================================================
def _decode_chunk(chunk):
    done, errs = 0, []
    by_path = collections.defaultdict(list)
    for t in chunk:
        by_path[t[0]].append(t)
    for path, items in by_path.items():
        with open(path, 'rb') as fh:
            for _p, off, size, rate, outp in items:
                try:
                    fh.seek(off); d = fh.read(size)
                    if d[:4] != BAO_VER or len(d) <= STREAM_HDR:
                        raise ValueError('no es un BAO de stream')
                    write_wav(outp, ima_decode(d[STREAM_HDR:]), rate)
                    done += 1
                except Exception as ex:
                    errs.append((outp, repr(ex)))
    return done, errs


def export_spanish_wavs(out_dir, stream_forge, log=print, progress=None, workers=None, only_ids=None):
    rows = read_map(out_dir)
    sidx = index_streams(stream_forge)
    wdir = os.path.join(out_dir, 'spanish', 'wav')
    seen, tasks = set(), []
    skipped = 0
    for r in rows:
        if r['stream'] in seen: continue
        seen.add(r['stream'])
        if r.get('source') == 'inline' or r.get('plain_ima') != '1':
            skipped += 1; continue
        sid = int(r['stream'].split('_0x')[1], 16)
        if only_ids and sid not in only_ids: continue
        off, size, _n = sidx[sid]
        tasks.append((stream_forge, off, size, int(r['rate']), os.path.join(wdir, r['stream'] + '.wav')))
    if skipped:
        log('Omitidos %d audios (inline, con prefetch u otro codec): usa el export con vgmstream' % skipped)
    chunks = [tasks[i:i + 40] for i in range(0, len(tasks), 40)]
    log('Exportando %d WAV (decodificador interno) -> %s' % (len(tasks), wdir))
    done, errs, t0, k = 0, [], time.time(), 0
    try:
        with ProcessPoolExecutor(max_workers=workers or min(os.cpu_count() or 2, 8)) as ex:
            for fu in as_completed([ex.submit(_decode_chunk, c) for c in chunks]):
                d, e = fu.result(); done += d; errs += e; k += 1
                if progress: progress(k, len(chunks))
    except Exception as exn:
        log('Paralelo no disponible (%r); un solo proceso' % (exn,))
        done, errs, k = 0, [], 0
        for c in chunks:
            d, e = _decode_chunk(c); done += d; errs += e; k += 1
            if progress: progress(k, len(chunks))
    log('WAV listos: %d, errores: %d (%.1fs)' % (done, len(errs), time.time() - t0))
    for p, m in errs[:5]:
        log('  %s: %s' % (os.path.basename(p), m))
    return done, errs


def export_ogg_audio(out_dir, stream_forge=None, log=print, ffmpeg=None):
    """Audio Ogg completo en memoria (idioma elegido) -> ogg/<BAO>/esp_<id>.ogg (+ .wav con ffmpeg),
    mismo esquema que las variantes: esa carpeta es la plantilla de edicion."""
    root = os.path.join(out_dir, 'spanish')
    rows = [r for r in read_map(out_dir) if r.get('codec') == 'OGG' and r['source'] == 'inline' and r['prefetch'] in ('', '0') and r['header']]
    odir = os.path.join(root, 'ogg'); os.makedirs(odir, exist_ok=True)
    ff = ffmpeg or shutil.which('ffmpeg')
    lab = LANG_LABELS.get(DEFAULT_LANG_IDX, 'esp')
    n = w = 0
    man = []
    for r in rows:
        p0 = os.path.join(root, 'bao', LANG, r['stream'])
        if not os.path.exists(p0): continue
        data = open(p0, 'rb').read()
        if data[HEADER_SKIP:HEADER_SKIP + 4] != b'OggS': continue
        gdir = os.path.join(odir, r['header']); os.makedirs(gdir, exist_ok=True)
        fn = '%s_%s' % (lab, base_id(r['header']))
        with open(os.path.join(gdir, fn + '.ogg'), 'wb') as f: f.write(data[HEADER_SKIP:])
        n += 1
        if ff and subprocess.run([ff, '-v', 'error', '-y', '-i', os.path.join(gdir, fn + '.ogg'), os.path.join(gdir, fn + '.wav')]).returncode == 0:
            w += 1
        rate, smp = _ogg_info(data)
        man.append([r['header'] + '/' + fn + '.ogg', r['header'], base_id(r['header']), DEFAULT_LANG_IDX, lab, 'OGG', rate, smp, r['stream']])
    if man: _manifest_update(odir, man)
    log('Ogg: %d en %s%s' % (n, odir, (' (+%d WAV con ffmpeg)' % w) if ff else ' (sin ffmpeg: solo .ogg)'))
    return n


# =====================================================================
#  NUEVO v2: importar / encodear (reemplazo en el mismo hueco del forge)
# =====================================================================
ID_RE = re.compile(r'(?:0x)?([0-9a-fA-F]{8})')


def stream_id_from_name(fname):
    stem = os.path.splitext(os.path.basename(fname))[0]
    m = re.search(r'0x([0-9a-fA-F]{8})', stem) or ID_RE.search(stem)
    return int(m.group(1), 16) if m else None


def encode_for_slot(wav_path, old_bao, rate, name='stream'):
    """WAV -> BAO de stream del MISMO tamano que old_bao. Devuelve (nuevo_bao, info)."""
    if old_bao[:4] != BAO_VER:
        raise ValueError('el stream original no empieza con la firma BAO')
    hdr, old_payload = old_bao[:STREAM_HDR], old_bao[STREAM_HDR:]
    if hdr[0x1c] == SEEK_SELECTOR:
        raise ValueError('variante IMA con seek-table (selector 192): aun no se puede encodear')
    n_target = len(old_payload) * 2
    vals, src_rate = read_wav_mono(wav_path)
    dur_in = len(vals) / float(src_rate or 1)
    vals = resample(vals, src_rate, rate)
    vals, cut = fit_length(vals, n_target)
    if cut:                                     # fade-out de 10 ms para no dejar un click
        f = min(len(vals), int(rate * 0.010))
        for i in range(f):
            vals[len(vals) - f + i] = int(vals[len(vals) - f + i] * (1 - (i + 1) / f))
    payload = ima_encode(vals)
    assert len(payload) == len(old_payload)
    rec = ima_decode(payload)
    info = {'dur_in': round(dur_in, 3), 'dur_slot': round(n_target / float(rate), 3), 'cut': cut,
            'snr_db': round(snr_db(vals, rec), 1), 'rate': rate}
    return hdr + payload, info


def import_wavs(wav_files, out_dir, stream_forge, backup=True, dry_run=False, log=print, progress=None):
    rows = read_map(out_dir)
    bymap = {r['stream']: r for r in rows}
    sidx = index_streams(stream_forge)
    report, ok = [], 0
    if backup and not dry_run and not os.path.exists(stream_forge + '.bak'):
        log('Creando copia de seguridad: %s.bak (puede tardar)' % _bn(stream_forge))
        shutil.copyfile(stream_forge, stream_forge + '.bak')
    fh = None if dry_run else open(stream_forge, 'r+b')
    try:
        for i, wp in enumerate(wav_files):
            fname = os.path.basename(wp)
            try:
                sid = stream_id_from_name(wp)
                if sid is None or sid not in sidx:
                    raise ValueError('el nombre no contiene un id de stream %s conocido' % LANG)
                off, size, sname = sidx[sid]
                r = bymap.get(sname)
                if not r or r.get('plain_ima') != '1':
                    raise ValueError('solo se importan IMA del forge de voces SIN prefetch (el prefetch vive en un paquete comprimido)')
                rate = int(r['rate']) if r else DEFAULT_RATE
                with open(stream_forge, 'rb') as rf:
                    rf.seek(off); old = rf.read(size)
                if r and r['channels'] not in ('', '0', '1'):
                    raise ValueError('header con %s canales: solo se reemplaza mono' % r['channels'])
                new, info = encode_for_slot(wp, old, rate, sname)
                if len(new) != size:
                    raise ValueError('tamano distinto (bug)')
                if not dry_run:
                    fh.seek(off); fh.write(new)
                msg = 'OK'
                if info['cut']: msg += ' (RECORTADO: el WAV dura %.2fs y el hueco %.2fs)' % (info['dur_in'], info['dur_slot'])
                if info['snr_db'] < 12: msg += ' (SNR bajo)'
                report.append([fname, sname, rate, info['dur_in'], info['dur_slot'], info['snr_db'], msg])
                ok += 1
            except Exception as ex:
                report.append([fname, '', '', '', '', '', 'ERROR: %s' % ex])
                log('  %s: %s' % (fname, ex))
            if progress: progress(i + 1, len(wav_files))
    finally:
        if fh:
            fh.flush(); fh.close()
    rp = os.path.join(out_dir, 'spanish', 'import_report.csv')
    _write_csv(rp, ['wav', 'stream', 'rate', 'dur_wav_s', 'dur_hueco_s', 'snr_db', 'estado'], report)
    cuts = sum(1 for r in report if 'RECORTADO' in r[-1])
    log('%s: %d OK, %d error(es), %d recortado(s). Informe: %s' %
        ('Simulacion' if dry_run else 'Importado', ok, len(report) - ok, cuts, rp))
    return report


def restore_backup(stream_forge, log=print):
    bak = stream_forge + '.bak'
    if not os.path.exists(bak):
        log('No existe %s' % bak); return False
    shutil.copyfile(bak, stream_forge)
    log('Forge restaurado desde .bak'); return True


# =====================================================================
#  NUEVO v2: comprobar mi decodificador contra vgmstream (verdad de referencia)
# =====================================================================
def vgm_crosscheck(vgm, out_dir, stream_forge, n=5, log=print):
    rows = [r for r in read_map(out_dir) if r['header'] and r['plain_ima'] == '1' and r['channels'] in ('1', '')]
    sidx = index_streams(stream_forge)
    hdir = os.path.join(out_dir, 'spanish', 'bao', LANG)
    good = 0
    for r in rows[:n * 4]:
        if good >= n: break
        sid = int(r['stream'].split('_0x')[1], 16)
        off, size, _ = sidx[sid]
        with open(stream_forge, 'rb') as f:
            f.seek(off); st = f.read(size)
        with tempfile.TemporaryDirectory() as td:
            shutil.copy(os.path.join(hdir, r['header']), os.path.join(td, r['header']))
            with open(os.path.join(td, 'Common_BAO_0x%08x' % sid), 'wb') as f: f.write(st)
            wav = os.path.join(td, 'o.wav')
            p = subprocess.run([vgm, '-i', '-o', wav, os.path.join(td, r['header'])], capture_output=True, text=True)
            if p.returncode != 0 or not os.path.exists(wav):
                continue
            ref, _rate = read_wav_mono(wav)
        mine = list(ima_decode(st[STREAM_HDR:]))
        m = min(len(ref), len(mine))
        exact = sum(1 for a, b in zip(ref[:m], mine[:m]) if a == b) / float(m or 1)
        log('%s / %s: vgmstream %d muestras, mio %d, identicas %.1f%%, SNR %.1f dB' %
            (r['header'], r['stream'], len(ref), len(mine), exact * 100, snr_db(ref, mine)))
        good += 1
    if not good:
        log('No pude comparar ningun stream (revisa la ruta de vgmstream-cli y que haya headers con vgm_ok=1)')
    else:
        log('Si "identicas" ~100%% el decodificador (y por tanto el encoder) coincide con el del juego.')
    return good


# =====================================================================
#  CLI
# =====================================================================
# =====================================================================
#  NUEVO v2.1: importar WAV -> Ogg Vorbis DENTRO de los .forge (parche en el sitio, mismo tamano)
#  - Nombres de los WAV: los mismos de la carpeta wav (BAO_0x<header>.wav, o esp_0x00A8017D.wav, etc.)
#  - Idioma destino por casillas (Espanol = variante 3, Ingles = variante 1)
#  - Busca el BAO de datos en TODOS los .forge de la carpeta; .bak por forge antes de tocarlo
# =====================================================================
# ---- LZO1X: compresor propio (formato minilzo) con ajuste exacto de tamano -------------------------
LZO_WINDOW = 16384            # solo M2/M3 (distancia <= 16384); suficiente para chunks de 32 KB


def _lzo_ops(data, depth=1):
    """Parseo voraz con busqueda por rfind -> [('L', bytes) | ('M', dist, len)]."""
    n, i, lit0, ops = len(data), 0, 0, []
    find = data.rfind
    while i + 3 <= n:
        key = data[i:i + 3]
        lo = max(0, i - LZO_WINDOW)
        j = find(key, lo, i + 2)                      # inicio j < i con data[j:j+3] == key
        best_len, best_j = 0, -1
        tries = 0
        while j >= 0 and tries < 6:
            L = 3
            mx = n - i
            while L < mx and data[j + L] == data[i + L]:
                L += 1
            if L > best_len: best_len, best_j = L, j
            tries += 1
            j = find(key, lo, j + 2) if j > lo else -1
        if best_len >= 3 and not (best_len == 3 and i - best_j > 2048 and False):
            if i > lit0: ops.append(['L', data[lit0:i]])
            ops.append(['M', i - best_j, best_len])
            i += best_len; lit0 = i
        else:
            i += 1
    if lit0 < n: ops.append(['L', data[lit0:n]])
    return ops


def _lit_hdr(r):                                      # cabecera de una tirada literal >= 4 (estado 0)
    if r <= 18: return bytes([r - 3])
    v = r - 18; z, b = divmod(v - 1, 255)
    return b'\x00' + b'\x00' * z + bytes([b + 1])


def _match_bytes(dist, ln, s):
    if ln <= 8 and dist <= 2048:                      # M2
        return bytes([((ln - 1) << 5) | (((dist - 1) & 7) << 2) | s, (dist - 1) >> 3])
    d = ((dist - 1) << 2) | s                         # M3
    if ln <= 33: return bytes([32 | (ln - 2), d & 255, d >> 8])
    v = ln - 33; z, b = divmod(v - 1, 255)
    return bytes([32]) + b'\x00' * z + bytes([b + 1, d & 255, d >> 8])


def lzo_encode(ops):
    """ops -> flujo LZO1X con EOF. Une tiradas literales contiguas."""
    seg = []
    for o in ops:
        if o[0] == 'L' and seg and seg[-1][0] == 'L':
            seg[-1] = ['L', seg[-1][1] + o[1]]
        elif o[0] == 'L' and not o[1]:
            continue
        else:
            seg.append(list(o))
    out = bytearray(); k = 0; first = True
    while k < len(seg):
        o = seg[k]
        if o[0] == 'L':                                # literales sin match previo (inicio)
            r = len(o[1])
            if r < 4 and first:                        # 1..3 al inicio: byte 17+r
                out.append(17 + r)
            elif r < 4:
                raise ValueError('literales 1..3 sin match previo')
            else:
                out += _lit_hdr(r)
            out += o[1]; k += 1; first = False; continue
        nxt = seg[k + 1] if k + 1 < len(seg) and seg[k + 1][0] == 'L' else None
        s = len(nxt[1]) if nxt is not None and len(nxt[1]) <= 3 else 0
        out += _match_bytes(o[1], o[2], s); first = False
        if nxt is not None:
            if s:
                out += nxt[1]
            else:
                out += _lit_hdr(len(nxt[1])) + nxt[1]
            k += 2
        else:
            k += 1
    out += b'\x11\x00\x00'
    return bytes(out)


def lzo_fit(data, target, ops=None):
    """Comprime `data` a EXACTAMENTE `target` bytes (convierte partes de matches en literales).
    -> bytes o None si no cabe / no hay margen para igualar."""
    ops = ops if ops is not None else _lzo_ops(data)
    ops = [list(o) for o in ops]
    # el inicio no puede ser un literal de 1..3 si luego no hay match; _lzo_ops no lo produce salvo todo-literal
    def size(o):
        try: return len(lzo_encode(o))
        except ValueError: return 1 << 30
    cur = size(ops)
    if cur == target: return lzo_encode(ops)
    if cur > target: return None
    # posiciones de bytes de cada op para poder reconstruir literales
    def expand(o):
        pos, res = 0, []
        for x in o:
            if x[0] == 'L': res.append((x, pos)); pos += len(x[1])
            else: res.append((x, pos)); pos += x[2]
        return res
    for _round in range(6):
        cand = sorted([k for k, x in enumerate(ops) if x[0] == 'M'], key=lambda k: -ops[k][2])[:24]
        if not cand: return None
        starts = {}
        pos = 0
        for k, x in enumerate(ops):
            starts[k] = pos; pos += len(x[1]) if x[0] == 'L' else x[2]
        for k in cand:
            _t, dist, L = ops[k]; p0 = starts[k]
            def make(j):                                   # los j primeros bytes del match pasan a literales
                lit = ['L', data[p0:p0 + j]]
                rest = [['M', dist, L - j]] if L - j >= 3 else ([] if L - j == 0 else None)
                if rest is None: return None
                return ops[:k] + [lit] + rest + ops[k + 1:]
            js = [j for j in range(0, L + 1) if (L - j >= 3 or L - j == 0)]
            lo, hi = 0, len(js) - 1                         # mayor j con size <= target
            best = None
            while lo <= hi:
                mid = (lo + hi) // 2
                o2 = make(js[mid]) if js[mid] else ops
                s2 = size(o2) if o2 is not None else 1 << 30
                if s2 == target: return lzo_encode(o2)
                if s2 < target: best = (mid, o2); lo = mid + 1
                else: hi = mid - 1
            if best and best[0] > 0:
                ops = [list(x) for x in best[1]]            # aplica lo posible y sigue con otros matches
                if size(ops) == target: return lzo_encode(ops)
                break
        else:
            return None
    return None


# ---- LZO1X v2: parser fiel + codificador por tipos + empalme (splice) con el stream original -----------
class _BadState(Exception):
    pass


def lzo_parse(src):
    """Stream LZO1X -> [['L', n], ['M', tipo, dist, n]]; tipo in M1a, M1b, M2, M3, M4. Mismo esquema que lzo1x_decompress."""
    ops, ip, state = [], 0, 'top'
    t = src[ip]
    if t > 17:
        ip += 1; t -= 17; ops.append(['L', t]); ip += t
        state = 'match_next' if t < 4 else 'first_literal'
    while True:
        if state == 'top':
            t = src[ip]; ip += 1
            if t >= 16: state = 'match'
            else:
                if t == 0:
                    while src[ip] == 0: t += 255; ip += 1
                    t += 15 + src[ip]; ip += 1
                t += 3; ops.append(['L', t]); ip += t; state = 'first_literal'
        if state == 'first_literal':
            t = src[ip]; ip += 1
            if t >= 16: state = 'match'
            else:
                ops.append(['M', 'M1b', 1 + 0x800 + (t >> 2) + (src[ip] << 2), 3]); ip += 1; state = 'match_done'
        if state == 'match':
            if t >= 64:
                dist = 1 + ((t >> 2) & 7) + (src[ip] << 3); ip += 1; n = (t >> 5) - 1 + 2; kind = 'M2'
            elif t >= 32:
                n = t & 31
                if n == 0:
                    while src[ip] == 0: n += 255; ip += 1
                    n += 31 + src[ip]; ip += 1
                dist = 1 + (src[ip] >> 2) + (src[ip + 1] << 6); ip += 2; n += 2; kind = 'M3'
            elif t >= 16:
                n = t & 7
                if n == 0:
                    while src[ip] == 0: n += 255; ip += 1
                    n += 7 + src[ip]; ip += 1
                d14 = (src[ip] >> 2) + (src[ip + 1] << 6); ip += 2
                if (t & 8) == 0 and d14 == 0: break          # EOF
                dist = ((t & 8) << 11) + d14 + 0x4000; n += 2; kind = 'M4'
            else:
                dist = 1 + (t >> 2) + (src[ip] << 2); ip += 1; n = 2; kind = 'M1a'
            ops.append(['M', kind, dist, n]); state = 'match_done'
        if state == 'match_done':
            t = src[ip - 2] & 3
            if t == 0: state = 'top'; continue
            ops.append(['L', t]); ip += t
            t = src[ip]; ip += 1; state = 'match'; continue
        if state == 'match_next':
            t = src[ip]; ip += 1; state = 'match'
    return ops


def _mbytes2(kind, dist, n, s):
    if kind == 'M1a': return bytes([(((dist - 1) & 3) << 2) | s, (dist - 1) >> 2])
    if kind == 'M1b':
        d = dist - 2049; return bytes([((d & 3) << 2) | s, d >> 2])
    if kind == 'M2': return bytes([((n - 1) << 5) | (((dist - 1) & 7) << 2) | s, (dist - 1) >> 3])
    if kind == 'M3':
        d = ((dist - 1) << 2) | s
        if n <= 33: return bytes([32 | (n - 2), d & 255, d >> 8])
        z, b = divmod(n - 33 - 1, 255)
        return bytes([32]) + b'\x00' * z + bytes([b + 1, d & 255, d >> 8])
    x = dist - 0x4000; h, d14 = x >> 14, x & 0x3FFF          # M4
    c = n - 2
    if 1 <= c <= 7: head = bytes([16 | (h << 3) | c])
    else:
        z, b = divmod(c - 7 - 1, 255); head = bytes([16 | (h << 3)]) + b'\x00' * z + bytes([b + 1])
    return head + bytes([((d14 & 63) << 2) | s, d14 >> 6])


def lzo_encode2(ops, data):
    """ops (+ bytes de salida `data`) -> stream LZO1X con EOF. Lanza _BadState(k) si un M1 no cabe en su estado."""
    seg = []
    for o in ops:
        if o[0] == 'L':
            if o[1] == 0: continue
            if seg and seg[-1][0] == 'L': seg[-1] = ['L', seg[-1][1] + o[1]]; continue
        seg.append(list(o))
    out = bytearray(); pos = 0; k = 0; state = 'top'; first = True
    while k < len(seg):
        o = seg[k]
        if o[0] == 'L':
            n = o[1]
            if first:
                if n <= 238: out.append(17 + n); state = 'match_next' if n < 4 else 'first_literal'
                else: out += _lit_hdr(n); state = 'first_literal'
            else:
                if state != 'top' or n < 4: raise ValueError('literales en estado invalido')
                out += _lit_hdr(n); state = 'first_literal'
            out += data[pos:pos + n]; pos += n; k += 1; first = False; continue
        _t, kind, dist, n = o
        nxt = seg[k + 1] if k + 1 < len(seg) and seg[k + 1][0] == 'L' else None
        s = nxt[1] if nxt is not None and nxt[1] <= 3 else 0
        if kind == 'M1a' and state not in ('tr', 'match_next'): raise _BadState(k)
        if kind == 'M1b' and state != 'first_literal': raise _BadState(k)
        out += _mbytes2(kind, dist, n, s); pos += n; first = False
        if s:
            out += data[pos:pos + s]; pos += s; state = 'tr'; k += 2
        else:
            state = 'top'; k += 1
    out += b'\x11\x00\x00'
    return bytes(out)


def _encode_safe(ops, data):
    """lzo_encode2 convirtiendo en literales los M1 cuyo estado dejo de ser valido."""
    ops = [list(o) for o in ops]
    for _ in range(len(ops) + 2):
        try:
            return lzo_encode2(ops, data), ops
        except _BadState as e:
            # el indice k es de la lista normalizada; localizamos el M1 invalido recorriendo en el mismo orden
            seg_idx, kk = -1, -1
            merged = []
            for i, o in enumerate(ops):
                if o[0] == 'L' and o[1] == 0: continue
                if o[0] == 'L' and merged and merged[-1][0] == 'L': merged[-1][2].append(i); continue
                merged.append([o[0], i, [i]])
            idx = merged[e.args[0]][1] if e.args[0] < len(merged) else None
            if idx is None: raise
            ops[idx] = ['L', ops[idx][3]]
    raise ValueError('no converge')


def _valid_match(new, pos, dist, n):
    if dist > pos: return False
    src = new[pos - dist:pos]
    if dist >= n: return new[pos:pos + n] == src[:n]
    rep = (src * (n // dist + 1))[:n]
    return new[pos:pos + n] == rep


def _find_ops_range(data, a, b):
    """Matches M2/M3 para data[a:b] con fuentes en cualquier parte previa -> ops [L|M] que cubren exactamente [a,b)."""
    ops, i, lit0, find = [], a, a, data.rfind
    while i + 3 <= b:
        key = data[i:i + 3]; lo = max(0, i - LZO_WINDOW)
        j = find(key, lo, i + 2); best_len, best_j, tries = 0, -1, 0
        while j >= 0 and tries < 8:
            L = 3
            while i + L < b and data[j + L] == data[i + L]: L += 1
            if L > best_len: best_len, best_j = L, j
            tries += 1
            j = find(key, lo, j + 2) if j > lo else -1
        if best_len >= 3:
            if i > lit0: ops.append(['L', i - lit0])
            ops.append(['M', 'M2' if (best_len <= 8 and i - best_j <= 2048) else 'M3', i - best_j, best_len])
            i += best_len; lit0 = i
        else:
            i += 1
    if lit0 < b: ops.append(['L', b - lit0])
    return ops


def lzo_splice(orig_stored, old_dec, new_dec, target):
    """Recomprime new_dec reutilizando el stream ORIGINAL en todo lo que no cambio (bytes identicos) y
    ajusta a EXACTAMENTE `target` bytes. -> bytes o None."""
    if len(old_dec) != len(new_dec): return None
    ops = lzo_parse(orig_stored)
    # 1) matches que ya no reproducen el contenido nuevo -> literales
    pos, mod = 0, []                                       # mod: rangos [a,b) de literales que hay que re-buscar
    res = []
    for o in ops:
        if o[0] == 'L':
            res.append(['L', o[1]]); 
            if old_dec[pos:pos + o[1]] != new_dec[pos:pos + o[1]]: mod.append((pos, pos + o[1]))
            pos += o[1]
        else:
            if _valid_match(new_dec, pos, o[2], o[3]): res.append(list(o))
            else: res.append(['L', o[3]]); mod.append((pos, pos + o[3]))
            pos += o[3]
    # 2) unir literales contiguos y buscar matches nuevos dentro de las tiradas modificadas
    merged, pos = [], 0
    for o in res:
        n = o[1] if o[0] == 'L' else o[3]
        if o[0] == 'L' and merged and merged[-1][0] == 'L': merged[-1][1] += n
        else: merged.append(list(o))
    final, pos = [], 0
    for o in merged:
        if o[0] == 'L':
            a, b = pos, pos + o[1]
            if any(m[0] < b and m[1] > a for m in mod): final += _find_ops_range(new_dec, a, b)
            else: final.append(o)
            pos = b
        else:
            final.append(o); pos += o[3]
    # 3) tamano exacto
    try: enc, final = _encode_safe(final, new_dec)
    except Exception: return None
    if len(enc) == target: return enc
    if len(enc) > target: return None
    return _grow_ops(final, new_dec, target)


def _grow_ops(ops, data, target):
    """Convierte (parte de) matches en literales hasta alcanzar target exacto. -> bytes o None."""
    def size(o):
        try: return len(_encode_safe(o, data)[0])
        except Exception: return 1 << 30
    ops = [list(o) for o in ops]
    for _round in range(8):
        cur = size(ops)
        if cur == target: return _encode_safe(ops, data)[0]
        if cur > target: return None
        starts, pos = {}, 0
        for k, x in enumerate(ops):
            starts[k] = pos; pos += x[1] if x[0] == 'L' else x[3]
        cand = sorted([k for k, x in enumerate(ops) if x[0] == 'M'], key=lambda k: -ops[k][3])[:24]
        if not cand: return None
        progressed = False
        for k in cand:
            _t, kind, dist, L = ops[k]
            def make(j):                                   # los j primeros bytes del match pasan a literales
                if j == 0: return ops
                rest = [['M', kind if (kind in ('M3', 'M4') or L - j >= 3) else 'M2', dist, L - j]] if L - j >= 3 else ([] if L - j == 0 else None)
                if rest is None: return None
                if rest and rest[0][1] in ('M1a', 'M1b'): rest[0][1] = 'M2' if dist <= 2048 else 'M3'
                return ops[:k] + [['L', j]] + rest + ops[k + 1:]
            js = [j for j in range(0, L + 1) if (L - j >= 3 or L - j == 0)]
            lo, hi, best = 0, len(js) - 1, None
            while lo <= hi:
                mid = (lo + hi) // 2; o2 = make(js[mid]); s2 = size(o2) if o2 is not None else 1 << 30
                if s2 == target: return _encode_safe(o2, data)[0]
                if s2 < target: best = (mid, o2); lo = mid + 1
                else: hi = mid - 1
            if best and best[0] > 0:
                ops = [list(x) for x in best[1]]; progressed = True; break
        if not progressed: return None
    return None


OGG_LANGS = {'esp': 3, 'eng': 1}
COMP_SIG_OGG = b'\x33\xaa\xfb\x57\x99\xfa\x04\x10'


def _mk_crc_table():
    t = []
    for i in range(256):
        r = i << 24
        for _ in range(8):
            r = ((r << 1) ^ 0x04C11DB7) & 0xFFFFFFFF if r & 0x80000000 else (r << 1) & 0xFFFFFFFF
        t.append(r)
    return t
_OGG_CT = _mk_crc_table()


def _ogg_crc(b):
    c = 0
    for x in b:
        c = ((c << 8) & 0xFFFFFFFF) ^ _OGG_CT[((c >> 24) & 0xFF) ^ x]
    return c


def ogg_set_serial(ogg, serial):
    """Pone el serial original en todas las paginas y recalcula sus CRC."""
    out, p = bytearray(ogg), 0
    while True:
        p = out.find(b'OggS', p)
        if p < 0: break
        ns = out[p + 26]
        ln = 27 + ns + sum(out[p + 27:p + 27 + ns])
        struct.pack_into('<I', out, p + 14, serial)
        struct.pack_into('<I', out, p + 22, 0)
        struct.pack_into('<I', out, p + 22, _ogg_crc(out[p:p + ln]))
        p += ln
    return bytes(out)


def ogg_stream_info(ogg):
    """(canales, rate, granule final, serial) de un Ogg Vorbis."""
    i = ogg.find(b'\x01vorbis'); j = ogg.rfind(b'OggS')
    return ogg[i + 11], struct.unpack_from('<I', ogg, i + 12)[0], struct.unpack_from('<q', ogg, j + 6)[0], \
        struct.unpack_from('<I', ogg, 14)[0]


def _fit_pcm(raw, ch, n_frames, rate):
    """PCM16 -> exactamente n_frames (silencio al final o recorte con fade de 10 ms). -> (bytes, recortado)"""
    a = array.array('h'); a.frombytes(raw)
    if sys.byteorder == 'big': a.byteswap()
    need_s, cut = n_frames * ch, False
    if len(a) < need_s:
        a.extend([0] * (need_s - len(a)))
    elif len(a) > need_s:
        del a[need_s:]; cut = True
        f = min(n_frames, int(rate * 0.010))
        for i in range(f):
            for c in range(ch):
                k = (n_frames - f + i) * ch + c
                a[k] = int(a[k] * (1 - (i + 1) / f))
    if sys.byteorder == 'big': a.byteswap()
    return a.tobytes(), cut


def _vorbis_run(ff, wav, q, pad, tmp):
    o = os.path.join(tmp, 'e.ogg')
    cmd = [ff, '-v', 'error', '-y', '-i', wav, '-map_metadata', '-1', '-fflags', '+bitexact', '-flags:a', '+bitexact',
           '-c:a', 'libvorbis', '-q:a', '%.2f' % q]
    if pad > 0: cmd += ['-metadata', 'PAD=' + 'x' * pad]
    subprocess.run(cmd + [o], check=True)
    with open(o, 'rb') as f: return f.read()


def _ogg_pages(d):
    out, p = [], 0
    while True:
        p = d.find(b'OggS', p)
        if p < 0: break
        ns = d[p + 26]; lac = list(d[p + 27:p + 27 + ns]); ln = sum(lac)
        out.append(dict(flag=d[p + 5], gran=struct.unpack_from('<q', d, p + 6)[0], seq=struct.unpack_from('<I', d, p + 18)[0],
                        lac=lac, body=d[p + 27 + ns:p + 27 + ns + ln], full=d[p:p + 27 + ns + ln]))
        p += 27 + ns + ln
    return out


def _ogg_packets(pg):
    pk, cur = [], b''
    for g in pg:
        i = 0
        for l in g['lac']:
            cur += g['body'][i:i + l]; i += l
            if l < 255: pk.append(cur); cur = b''
    return pk


def _ogg_page(flag, gran, serial, seq, packets):
    lac = bytearray()
    for p in packets:
        lac += b'\xff' * (len(p) // 255) + bytes([len(p) % 255])
    if len(lac) > 255: raise ValueError('pagina de cabeceras demasiado grande')
    hdr = b'OggS' + bytes([0, flag]) + struct.pack('<qIII', gran, serial, seq, 0) + bytes([len(lac)]) + bytes(lac)
    pg = hdr + b''.join(packets)
    return pg[:22] + struct.pack('<I', _ogg_crc(pg)) + pg[26:]


def ogg_with_pads(ogg, head_pad, tail_pad, serial):
    """Ogg de ffmpeg -> mismo audio, con etiqueta PAD=xxxx en el comentario Vorbis (head_pad = bytes totales que
    anade; 0 = sin etiqueta) y `tail_pad` ceros tras la pagina final. Serial y CRC recalculados."""
    pg = _ogg_pages(ogg)
    pk = _ogg_packets(pg[:2])
    if len(pk) != 3 or not pk[1].startswith(b'\x03vorbis'): raise ValueError('cabeceras Ogg inesperadas')
    com = pk[1]
    vl = struct.unpack_from('<I', com, 7)[0]; cnt_off = 11 + vl
    cnt = struct.unpack_from('<I', com, cnt_off)[0]
    body, frame = com[:-1], com[-1:]
    if head_pad:
        if head_pad < 9: raise ValueError('relleno de comentario < 9')
        item = b'PAD=' + b'x' * (head_pad - 8)
        body = body[:cnt_off] + struct.pack('<I', cnt + 1) + body[cnt_off + 4:] + struct.pack('<I', len(item)) + item
    page1 = _ogg_page(0, 0, 0, 1, [body + frame, pk[2]])
    res = pg[0]['full'] + page1 + b''.join(g['full'] for g in pg[2:]) + bytes(tail_pad)
    return ogg_set_serial(res, serial)


def _pad_layout(audio_ogg, serial, n_total, tail):
    """Reparte n_total bytes de relleno: `tail` ceros al final y el resto en el comentario. -> bytes exactos o None."""
    want = n_total - tail
    if want < 0: return None
    base = len(ogg_with_pads(audio_ogg, 0, 0, serial))
    if want == 0: return ogg_with_pads(audio_ogg, 0, tail, serial)
    if want < 9: return ogg_with_pads(audio_ogg, 0, tail + want, serial)      # sobras pequenas al final
    for hp in (want, want - 1, want - 2, want - 3, want + 1, want + 2):
        try: c = ogg_with_pads(audio_ogg, hp, tail, serial)
        except ValueError: continue
        if len(c) - base - tail == want: return c
        if len(c) == base + n_total: return c
    for hp in range(max(9, want - 12), want + 12):
        try: c = ogg_with_pads(audio_ogg, hp, tail, serial)
        except ValueError: continue
        if len(c) == base + n_total: return c
    return None


def encode_ogg_slot(wav_path, old_bao, ffmpeg=None, fit=None):
    """WAV -> BAO de datos Ogg con el MISMO tamano, rate, canales, muestras y serial que old_bao.
    fit(candidato_bao) -> None si cabe en el paquete, o un texto de error (chunks LZO que no admiten el tamano).
    Relleno compresible: comentario Vorbis (inicio) y, solo si hace falta, ceros tras la pagina final."""
    ff = ffmpeg or shutil.which('ffmpeg')
    if not ff: raise RuntimeError('no encuentro ffmpeg (con libvorbis) en el PATH')
    if old_bao[HEADER_SKIP:HEADER_SKIP + 4] != b'OggS': raise ValueError('la variante original no contiene Ogg')
    old = old_bao[HEADER_SKIP:]
    ch, rate, gran, serial = ogg_stream_info(old)
    target = len(old)
    with tempfile.TemporaryDirectory() as tmp:
        w1 = os.path.join(tmp, 'in.wav'); w2 = os.path.join(tmp, 'fit.wav')
        subprocess.run([ff, '-v', 'error', '-y', '-i', wav_path, '-ac', str(ch), '-ar', str(rate), '-c:a', 'pcm_s16le', w1], check=True)
        with wave.open(w1) as w: raw = w.readframes(w.getnframes())
        dur_in = len(raw) / 2.0 / ch / rate
        cut = False
        if gran > 0: raw, cut = _fit_pcm(raw, ch, gran, rate)
        with wave.open(w2, 'wb') as w:
            w.setnchannels(ch); w.setsampwidth(2); w.setframerate(rate); w.writeframes(raw)
        base_len = len(ogg_with_pads(_vorbis_run(ff, w2, 5.0, 0, tmp), 0, 0, serial))
        lo, hi, q0 = -0.1, 10.0, None
        for _ in range(12):                      # mayor calidad que quepa en el hueco
            q = (lo + hi) / 2
            if len(ogg_with_pads(_vorbis_run(ff, w2, q, 0, tmp), 0, 0, serial)) <= target: q0, lo = q, q
            else: hi = q
        if q0 is None: raise ValueError('no cabe en el hueco ni a la calidad minima (el audio es demasiado largo/complejo)')
        res, err, qq, tailpad = None, None, q0, 0
        for dq in (0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.75, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0):
            qq = q0 - dq
            if qq < -0.1: break
            audio = _vorbis_run(ff, w2, qq, 0, tmp)
            n = target - len(ogg_with_pads(audio, 0, 0, serial))
            if n < 0: continue
            for tail in (0, 24, 64, 160, 400, 1000):
                if tail > n: break
                c = _pad_layout(audio, serial, n, tail)
                if c is None or len(c) != target: continue
                err = fit(old_bao[:HEADER_SKIP] + c) if fit else None
                if err is None: res, tailpad = c, tail; break
            if res is not None: break
        if res is None: raise ValueError(err or 'no se pudo igualar el tamano exacto del hueco')
    g2 = ogg_stream_info(res)[2]
    return old_bao[:HEADER_SKIP] + res, dict(q=round(qq, 2), cut=cut, dur_in=round(dur_in, 3), tailpad=tailpad,
                                               dur_slot=round(gran / float(rate), 3) if gran > 0 else 0, granule=g2, old_granule=gran)


def _adler0(d):                                  # CRC de chunk del .compressed (Adler-32 con semilla 0)
    return zlib.adler32(bytes(d), 0) & 0xFFFFFFFF


class OggPack:
    """Paquete .compressed dentro de un forge. Lee chunks sin comprimir y LZO; escribe en el sitio
    (LZO: recomprime a EXACTAMENTE el mismo tamano comprimido para no mover nada en el forge)."""
    def __init__(self, buf, sig):
        self.buf, self.sig = buf, sig
        p = sig + 8
        _v, self.ztype, _ms, _mz, n = struct.unpack_from('<HBHHH', buf, p); p += 9
        tbl = [struct.unpack_from('<HH', buf, p + 4 * i) for i in range(n)]; p += 4 * n
        self.chunks, v = [], 0                    # (pos_crc, pos_datos, size, zsize, inicio_virtual)
        for sz, zs in tbl:
            self.chunks.append((p, p + 4, sz, zs, v)); p += 4 + zs; v += sz
        self.end, self.vsize = p, v
        self._cache, self._mode = {}, 0

    def chunk_index(self, fpos):
        for ci, (cp, dp, sz, zs, vs) in enumerate(self.chunks):
            if dp <= fpos < dp + zs: return ci
        return None

    def chunk_data(self, ci, cache=True):
        d = self._cache.get(ci)
        if d is None:
            cp, dp, sz, zs, vs = self.chunks[ci]
            raw = bytes(self.buf[dp:dp + zs])
            if sz != zs and self.ztype != 1: raise ValueError('ZTYPE %d no soportado' % self.ztype)
            d = raw if sz == zs else lzo1x_decompress(raw, sz)
            if len(d) != sz: raise ValueError('chunk %d: tamano descomprimido inesperado' % ci)
            if cache: self._cache[ci] = d
        return d

    def _span(self, voff, n):
        out, end = [], voff + n
        for ci, (cp, dp, sz, zs, vs) in enumerate(self.chunks):
            if vs + sz <= voff or vs >= end: continue
            a, b = max(voff, vs), min(end, vs + sz)
            out.append((ci, a - vs, a - voff, b - a))
        if sum(x[3] for x in out) != n: raise ValueError('el BAO se sale del paquete')
        return out

    def read(self, voff, n):
        return b''.join(self.chunk_data(ci)[o:o + ln] for ci, o, _x, ln in self._span(voff, n))

    def crc_mode(self):
        """'stored' = Adler0 del dato guardado; 'dec' = del descomprimido; None = no se pudo confirmar (con LZO)."""
        if self._mode != 0: return self._mode
        seen = ok_s = ok_d = 0
        for ci, (cp, dp, sz, zs, vs) in enumerate(self.chunks):
            if sz == zs: continue
            raw = bytes(self.buf[dp:dp + zs]); crc = struct.unpack_from('<I', self.buf, cp)[0]
            seen += 1
            ok_s += crc == _adler0(raw)
            ok_d += crc == _adler0(self.chunk_data(ci, cache=False))
            if seen >= 6: break
        self._mode = 'stored' if seen and ok_s == seen else 'dec' if seen and ok_d == seen else (None if seen else 'stored')
        return self._mode

    def _plan(self, voff, data):
        """{chunk: (descomprimido_nuevo, guardado_nuevo)} o texto de error."""
        new = {}
        for ci, o, ofs, ln in self._span(voff, len(data)):
            d = bytearray(new[ci][0] if ci in new else self.chunk_data(ci))
            d[o:o + ln] = data[ofs:ofs + ln]
            cp, dp, sz, zs, vs = self.chunks[ci]
            if sz == zs:
                new[ci] = (bytes(d), bytes(d))
            else:
                if self.crc_mode() is None:
                    return 'chunk %d LZO: no se pudo confirmar como calcula el juego el CRC de los chunks LZO' % ci
                stored = bytes(self.buf[dp:dp + zs])
                z = lzo_splice(stored, self.chunk_data(ci), bytes(d), zs) or lzo_fit(bytes(d), zs)
                if z is None:
                    return 'chunk %d LZO: no se pudo recomprimir al tamano original (%d bytes)' % (ci, zs)
                if lzo1x_decompress(z, sz) != bytes(d):
                    return 'chunk %d LZO: la recompresion no verifica (bug)' % ci
                new[ci] = (bytes(d), z)
        return new

    def check(self, voff, data):
        r = self._plan(voff, data)
        return r if isinstance(r, str) else None

    def write(self, fh, voff, data):
        plan = self._plan(voff, data)
        if isinstance(plan, str): raise ValueError(plan)
        for ci, (dec, stored) in sorted(plan.items()):
            cp, dp, sz, zs, vs = self.chunks[ci]
            assert len(stored) == zs
            crc = _adler0(dec) if (sz != zs and self.crc_mode() == 'dec') else _adler0(stored)
            fh.seek(dp); fh.write(stored)
            fh.seek(cp); fh.write(struct.pack('<I', crc))
            self._cache[ci] = dec
        fh.flush()


def ogg_variants_in(pk, vt):
    """Con vt = offset virtual del nombre del BAO de datos -> {idx: (voff, size)} o None."""
    try:
        _sid, sub, nsz = struct.unpack('<III', pk.read(vt - 0x0c, 12))
        blob = pk.read(vt, min(nsz + 1 + sub + 16, pk.vsize - vt))
    except Exception: return None
    v = blob.find(BAO_VER, 0, nsz + sub)
    if v < 8: return None
    first = vt + v
    size, = struct.unpack_from('<I', blob, v - 4); idx, = struct.unpack_from('<I', blob, v - 8)
    if not (1 <= idx <= MAX_LANG_IDX): return None
    vs = {idx: (first, size)}; cur = first + size; end = vt + nsz + 1 + sub + 8
    while cur + 12 <= min(end, pk.vsize):
        try:
            nidx, nsize = struct.unpack('<II', pk.read(cur, 8)); head = pk.read(cur + 8, 4)
        except Exception: break
        if nidx != max(vs) + 1 or nsize < 0x24 or head != BAO_VER: break
        vs[nidx] = (cur + 8, nsize); cur += 8 + nsize
    return vs


def ogg_locate(buf, t, key, packs):
    """Offset de fichero t donde el forge contiene `key` como literal -> [(OggPack, offset virtual del nombre)].
    En chunks LZO se descomprime ese chunk y se busca el nombre dentro."""
    s = buf.rfind(COMP_SIG_OGG, 0, t)
    if s < 0: return []
    pk = packs.get(s)
    if pk is None:
        try: pk = packs[s] = OggPack(buf, s)
        except Exception: return []
    if t >= pk.end: return []
    ci = pk.chunk_index(t)
    if ci is None: return []
    cp, dp, sz, zs, vs = pk.chunks[ci]
    if sz == zs: return [(pk, vs + t - dp)]
    try: d = pk.chunk_data(ci)
    except Exception: return []
    out, p = [], 0
    while True:
        i = d.find(key, p)
        if i < 0: break
        out.append((pk, vs + i)); p = i + 1
    return out


def ogg_deep_scan(pk, keys, log=print):
    """Busqueda lenta: descomprime TODOS los chunks LZO de un paquete y busca los nombres (para BAO cuyo
    nombre no aparece como literal). -> {key: [vt, ...]}"""
    found = {k: [] for k in keys}; prev = b''; vprev = 0
    for ci, (cp, dp, sz, zs, vs) in enumerate(pk.chunks):
        if sz == zs:
            d = pk.chunk_data(ci, cache=False)
        else:
            try: d = pk.chunk_data(ci, cache=False)
            except Exception: prev = b''; continue
        buf = prev + d; base = vs - len(prev)
        for k in keys:
            p = 0
            while True:
                i = buf.find(k, p)
                if i < 0: break
                if base + i + len(k) > vs: found[k].append(base + i)   # evita duplicados del solape
                p = i + 1
        prev = d[-64:]
        if ci % 200 == 0: log('    paquete: chunk %d/%d' % (ci, len(pk.chunks)))
    return found


def ogg_index_forges(forge_dir, names, log=print):
    """Una pasada por forge: nombre de BAO de datos -> [(ruta_forge, offset_del_nombre)]."""
    want = {n.lower(): [] for n in names}
    rx = re.compile(rb'BAO_0x[0-9a-fA-F]{8}\x00')
    forges = list_forges(forge_dir)
    for k, fp in enumerate(forges):
        log('  buscando en %s (%d/%d)' % (_bn(fp), k + 1, len(forges)))
        try:
            with open(fp, 'rb') as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                for m in rx.finditer(buf):
                    nm = m.group()[:-1].decode().lower()
                    if nm in want: want[nm].append((fp, m.start()))
        except (ValueError, OSError) as ex:
            log('  (omitido %s: %s)' % (_bn(fp), ex))
        if all(want.values()): break
    return want


def _dkey(dn):                                   # nombre en minusculas -> bytes tal como estan en el forge
    return ('BAO_0x' + dn[6:]).encode() + b'\0'


def _hex8(stem):
    m = re.search(r'0x([0-9a-fA-F]{8})', stem) or re.search(r'(?<![0-9a-fA-F])([0-9a-fA-F]{8})(?![0-9a-fA-F])', stem)
    return int(m.group(1), 16) if m else None


def _load_ogg_names(out_dir, plantilla, log):
    """header -> nombre del BAO de datos Ogg (spanish_map.csv y/o _plantilla.csv)."""
    hdr2data = {}
    try:
        for r in read_map(out_dir):
            if r.get('codec') == 'OGG' and r.get('source') == 'inline' and r.get('header'):
                hdr2data[r['header'].lower()] = r['stream'].lower()
    except Exception:
        pass
    cands = [plantilla] if plantilla else []
    cands += [os.path.join(out_dir, 'spanish', 'ogg', '_plantilla.csv'), os.path.join(out_dir, 'ogg', '_plantilla.csv')]
    for c in cands:
        if c and os.path.isfile(c):
            with open(c, newline='', encoding='utf-8-sig') as f:
                for r in csv.DictReader(f):
                    if r.get('bao') and r.get('bao_datos'):
                        hdr2data.setdefault(r['bao'].lower(), r['bao_datos'].lower())
            log('Plantilla: %s' % c)
    return hdr2data


def import_wavs_auto(files, forge_dir, out_dir, langs=(3,), stream_forge_fn=None, backup=True, dry_run=False,
                     log=print, progress=None, plantilla=None):
    """Importa WAV de una carpeta (nombres = los de la carpeta wav). Ogg -> forges (por idioma); IMA -> forge de voces."""
    hdr2data = _load_ogg_names(out_dir, plantilla, log)
    ogg_jobs, ima_files, report = [], [], []
    for wp in files:
        stem = os.path.splitext(os.path.basename(wp))[0]
        if stem.lower().startswith('spanish_'):
            ima_files.append(wp); continue
        sid = _hex8(stem)
        hdr = 'bao_0x%08x' % (((sid & 0x00FFFFFF) | 0x20000000) if sid is not None else 0)
        if sid is not None and hdr in hdr2data:
            ogg_jobs.append((wp, hdr, hdr2data[hdr]))
        elif sid is not None and ('bao_0x%08x' % sid) in hdr2data:
            ogg_jobs.append((wp, 'bao_0x%08x' % sid, hdr2data['bao_0x%08x' % sid]))
        else:
            ima_files.append(wp)                 # puede ser un IMA con nombre propio; import_wavs lo valida
    log('WAV: %d (Ogg: %d, IMA/otros: %d). Idiomas destino: %s' % (
        len(files), len(ogg_jobs), len(ima_files), ', '.join(k for k, v in OGG_LANGS.items() if v in langs)))
    ok = 0
    lname_of = {v: k for k, v in OGG_LANGS.items()}
    if ogg_jobs:
        jobs_by_dn = collections.defaultdict(list)
        for wp, hdr, dn in ogg_jobs: jobs_by_dn[dn].append((wp, hdr))
        idx = ogg_index_forges(forge_dir, set(jobs_by_dn), log)
        state = dict(done=0, total=len(ogg_jobs) * len(langs))
        resolved, errors = set(), collections.defaultdict(list)

        def patch_here(fp, fh, pk, vt, dn):
            """Parchea todas las variantes pedidas del BAO de datos dn ubicado en (pk, vt)."""
            nonlocal ok
            vs = ogg_variants_in(pk, vt)
            if not vs:
                errors[dn].append('no se pudo leer la tabla de variantes en el paquete'); return False
            for wp, hdr in jobs_by_dn[dn]:
                fname = os.path.basename(wp)
                for lg in langs:
                    ln = lname_of.get(lg, str(lg))
                    try:
                        if lg not in vs: raise ValueError('el BAO no tiene la variante %d (%s)' % (lg, ln))
                        voff, size = vs[lg]
                        old = pk.read(voff, size)
                        lzo = any(pk.chunks[c][2] != pk.chunks[c][3] for c, *_r in pk._span(voff, size))
                        new, info = encode_ogg_slot(wp, old, fit=lambda c, voff=voff: pk.check(voff, c))
                        if len(new) != size: raise ValueError('tamano distinto (bug)')
                        if not dry_run:
                            if backup and not os.path.exists(fp + '.bak'):
                                log('Copia de seguridad: %s.bak (puede tardar)' % _bn(fp)); shutil.copyfile(fp, fp + '.bak')
                            pk.write(fh, voff, new)
                        msg = 'OK' + (' (simulado)' if dry_run else '') + (' [LZO]' if lzo else '')
                        if info.get('tailpad'): msg += ' (relleno final %d B)' % info['tailpad']
                        if info['cut']: msg += ' (RECORTADO: WAV %.2fs, hueco %.2fs)' % (info['dur_in'], info['dur_slot'])
                        report.append([fname, hdr, dn, ln, _bn(fp), info['q'], msg]); ok += 1
                    except Exception as ex:
                        report.append([fname, hdr, dn, ln, _bn(fp), '', 'ERROR: %s' % ex])
                        log('  %s [%s]: %s' % (fname, ln, ex))
                    state['done'] += 1
                    if progress: progress(state['done'], state['total'])
            resolved.add(dn); return True

        sigs_by_forge = {}
        by_forge = collections.defaultdict(lambda: collections.defaultdict(list))
        for dn, hits in idx.items():
            for fp, t in hits: by_forge[fp][dn].append(t)
        for fp in sorted(by_forge):
            fh = open(fp, 'rb' if dry_run else 'r+b')
            try:
                with mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                    packs = {}
                    for dn, ts in by_forge[fp].items():
                        if dn in resolved: continue
                        key = _dkey(dn)
                        for t in ts:
                            for pk, vt in ogg_locate(buf, t, key, packs):
                                if patch_here(fp, fh, pk, vt, dn): break
                            if dn in resolved: break
                    sigs_by_forge[fp] = list(packs)
                    packs.clear()
            finally:
                fh.flush(); fh.close()
        pend = [dn for dn in jobs_by_dn if dn not in resolved]
        if pend:
            log('Busqueda profunda de %d BAO que no aparecen como literal: %s%s' % (
                len(pend), ', '.join(pend[:6]), ' ...' if len(pend) > 6 else ''))
            for fp in list_forges(forge_dir):
                if not pend: break
                fh = open(fp, 'rb' if dry_run else 'r+b')
                try:
                    with mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                        sigs, p = [], 0
                        while True:
                            i = buf.find(COMP_SIG_OGG, p)
                            if i < 0: break
                            sigs.append(i); p = i + 1
                        known = set(sigs_by_forge.get(fp, []))
                        sigs.sort(key=lambda x: (x not in known, x))
                        log('  %s: %d paquetes' % (_bn(fp), len(sigs)))
                        for s0 in sigs:
                            if not pend: break
                            try: pk = OggPack(buf, s0)
                            except Exception: continue
                            if len(pk.chunks) < 2: continue
                            found = ogg_deep_scan(pk, [_dkey(d) for d in pend], lambda m: None)
                            for key, vts in found.items():
                                dn = key[:-1].decode().lower()
                                for vt in vts:
                                    if dn not in resolved and patch_here(fp, fh, pk, vt, dn): break
                            pend = [d for d in pend if d not in resolved]
                finally:
                    fh.flush(); fh.close()
        for dn in jobs_by_dn:
            if dn in resolved: continue
            for wp, hdr in jobs_by_dn[dn]:
                why = errors[dn][-1] if errors[dn] else 'BAO de datos no encontrado en ningun forge'
                report.append([os.path.basename(wp), hdr, dn, '', '', '', 'ERROR: ' + why])
    if ima_files:
        sel = [v for v in langs if v == DEFAULT_LANG_IDX]
        if not sel:
            for wp in ima_files: report.append([os.path.basename(wp), '', '', '', '', '', 'OMITIDO: IMA solo existe en el forge de voces en espanol (marca Espanol)'])
        else:
            sf = stream_forge_fn() if stream_forge_fn else None
            if not sf:
                for wp in ima_files: report.append([os.path.basename(wp), '', '', '', '', '', 'ERROR: no se identifico el audio (ni Ogg ni IMA); ejecuta "Extraer espanol rapido" o indica la plantilla'])
            else:
                for r in import_wavs(ima_files, out_dir, sf, backup, dry_run, log, progress):
                    report.append([r[0], '', r[1], 'esp', _bn(sf), '', r[-1]])
                    ok += 1 if r[-1].startswith('OK') else 0
    rp = os.path.join(out_dir, 'spanish', 'import_report_v21.csv')
    _write_csv(rp, ['wav', 'header', 'bao_datos/stream', 'idioma', 'forge', 'calidad_q', 'estado'], report)
    errs = sum(1 for r in report if str(r[-1]).startswith(('ERROR', 'OMITIDO')))
    log('%s: %d OK, %d error(es)/omitido(s). Informe: %s' % ('Simulacion' if dry_run else 'Importado', ok, errs, rp))
    return report


def restore_all_backups(forge_dir, log=print):
    n = 0
    for fp in list_forges(forge_dir):
        if os.path.exists(fp + '.bak'):
            shutil.copyfile(fp + '.bak', fp); log('Restaurado: %s' % _bn(fp)); n += 1
    if not n: log('No hay .bak en %s' % forge_dir)
    return n


def run_cli(argv):
    ap = argparse.ArgumentParser(description='AC1 BAO Tool v2')
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('fast', help='extraccion rapida espanol: headers + mapa (+ WAV con --wav)')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('--data', default=None)
    p.add_argument('--wav', action='store_true'); p.add_argument('--vgm', default='')
    p.add_argument('--variants', action='store_true', help='guardar todas las variantes de idioma en carpetas por BAO')
    p.add_argument('--labels', default='', help='etiquetas de idioma, ej. 1=eng,3=esp,2=fra')
    p.add_argument('--variants-wav', action='store_true', help='decodificar las variantes Ogg a WAV (ffmpeg)')
    p.add_argument('--ratefix', default='16000:11025', help='correccion de rate, ej. 16000:11025 ; vacio = ninguna')
    p = sub.add_parser('wav', help='exportar WAV espanol (necesita haber hecho fast)')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('--data', default=None)
    p.add_argument('--vgm', default=''); p.add_argument('--ratefix', default='16000:11025')
    p = sub.add_parser('import', help='importar WAV editados (carpeta o archivos)')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('wavs', nargs='+')
    p.add_argument('--data', default=None); p.add_argument('--no-backup', action='store_true')
    p.add_argument('--dry-run', action='store_true')
    p.add_argument('--lang', default='esp', help='idioma destino: esp, eng o esp,eng (variantes Ogg)')
    p.add_argument('--plantilla', default=None, help='_plantilla.csv (opcional; por defecto spanish_map.csv / out/spanish/ogg/_plantilla.csv)')
    p = sub.add_parser('check', help='comparar decodificador interno con vgmstream-cli')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('--vgm', default='vgmstream-cli')
    p.add_argument('--data', default=None)
    p = sub.add_parser('full', help='escaneo completo antiguo (todos los forges)')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('--vgm', default='vgmstream-cli')
    p.add_argument('--lang', default=''); p.add_argument('--types', default='1,5,6'); p.add_argument('--no-wav', action='store_true')
    a = ap.parse_args(argv)
    if a.cmd == 'full':
        os.makedirs(a.out, exist_ok=True)
        langs, stats = extract_all(a.forges, a.out)
        print('Extraccion:', stats)
        for l in [l for l in langs if not a.lang or l.lower() in [x.lower() for x in a.lang.split(',')]]:
            build_language_dir(a.out, l)
            if not a.no_wav:
                export_wavs(a.out, l, a.vgm, tuple(int(x) for x in a.types.split(',')))
        return
    plan = load_plan(a.data, a.out) if a.cmd in ('fast', 'wav', 'check') else None
    if a.cmd == 'fast':
        sf = locate_stream_forge(a.forges, plan)
        fast_extract_spanish(a.forges, a.out, plan, save_variants=a.variants, lang_labels=parse_labels(a.labels), variants_wav=a.variants_wav)
        build_map(a.out, plan, sf, rate_fix=parse_ratefix(a.ratefix))
        if a.wav:
            if a.vgm: export_wavs_vgm(a.out, a.vgm, rate_fix=parse_ratefix(a.ratefix))
            else:
                export_spanish_wavs(a.out, sf); export_ogg_audio(a.out, sf)
    elif a.cmd == 'wav':
        sf = locate_stream_forge(a.forges, plan)
        if a.vgm: export_wavs_vgm(a.out, a.vgm, rate_fix=parse_ratefix(a.ratefix))
        else:
            export_spanish_wavs(a.out, sf); export_ogg_audio(a.out, sf)
    elif a.cmd == 'check':
        vgm_crosscheck(a.vgm, a.out, locate_stream_forge(a.forges, plan))
    elif a.cmd == 'import':
        files = []
        for w in a.wavs:
            if os.path.isdir(w):
                files += [os.path.join(w, f) for f in sorted(os.listdir(w)) if f.lower().endswith('.wav')]
            else:
                files.append(w)
        langs = [OGG_LANGS.get(x.strip().lower(), int(x) if x.strip().isdigit() else None) for x in a.lang.split(',') if x.strip()]
        if not langs or None in langs: raise SystemExit('--lang invalido (esp, eng)')
        import_wavs_auto(files, a.forges, a.out, langs, lambda: locate_stream_forge(a.forges, load_plan(a.data, a.out)),
                         not a.no_backup, a.dry_run, plantilla=a.plantilla)


# =====================================================================
#  GUI (CustomTkinter, adaptable, con scroll vertical)
# =====================================================================
def run_gui():
    import customtkinter as ctk
    from tkinter import filedialog
    ctk.set_appearance_mode('dark'); ctk.set_default_color_theme('blue')
    app = ctk.CTk()
    app.title('AC1 BAO Tool v2 - Español rápido / Importar')
    app.geometry('900x700'); app.minsize(560, 420)
    cfg_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ac1_bao_tool_cfg.json')
    try:
        cfg = json.load(open(cfg_path, encoding='utf-8'))
    except Exception:
        cfg = {}
    V = {k: ctk.StringVar(value=cfg.get(k, d)) for k, d in
         (('forges', ''), ('out', ''), ('data', ''), ('vgm', 'vgmstream-cli'), ('wavdir', ''), ('ratefix', '16000:11025'), ('labels', '1=eng,3=esp'), ('plantilla', ''))}
    V['backup'] = ctk.BooleanVar(value=cfg.get('backup', True))
    V['dry'] = ctk.BooleanVar(value=False)
    V['lang_esp'] = ctk.BooleanVar(value=cfg.get('lang_esp', True))
    V['lang_eng'] = ctk.BooleanVar(value=cfg.get('lang_eng', False))
    V['variants'] = ctk.BooleanVar(value=False)
    V['vwav'] = ctk.BooleanVar(value=False)

    def save_cfg():
        try:
            json.dump({k: v.get() for k, v in V.items()}, open(cfg_path, 'w', encoding='utf-8'))
        except Exception:
            pass

    scroll = ctk.CTkScrollableFrame(app)                      # scroll vertical si no cabe
    scroll.pack(fill='both', expand=True, padx=4, pady=4)
    scroll.grid_columnconfigure(0, weight=1)
    tabs = ctk.CTkTabview(scroll)
    tabs.grid(row=0, column=0, sticky='ew', padx=6, pady=6)
    t1, t2, t3, t4 = (tabs.add(n) for n in ('1 · Extraer', '2 · WAV', '3 · Importar', 'Avanzado'))
    for t in (t1, t2, t3, t4):
        t.grid_columnconfigure(0, weight=1)
    log_box = ctk.CTkTextbox(scroll, height=230, wrap='word')
    log_box.grid(row=1, column=0, sticky='ew', padx=6, pady=4)
    pb = ctk.CTkProgressBar(scroll); pb.set(0)
    pb.grid(row=2, column=0, sticky='ew', padx=8, pady=(2, 8))
    busy = [False]
    buttons = []

    def log(m):
        app.after(0, lambda: (log_box.insert('end', m + '\n'), log_box.see('end')))

    def prog(a, b):
        app.after(0, lambda: pb.set(a / max(b, 1)))

    def field(parent, row, label, var, mode):
        ctk.CTkLabel(parent, text=label, anchor='w', justify='left').grid(row=row, column=0, sticky='w', padx=6, pady=(8, 0))
        f = ctk.CTkFrame(parent, fg_color='transparent'); f.grid(row=row + 1, column=0, sticky='ew', padx=2)
        f.grid_columnconfigure(0, weight=1)
        ctk.CTkEntry(f, textvariable=var).grid(row=0, column=0, sticky='ew', padx=4, pady=2)
        def pick():
            r = filedialog.askdirectory() if mode == 'dir' else filedialog.askopenfilename()
            if r: var.set(r)
        if mode != 'text':
            ctk.CTkButton(f, text='...', width=40, command=pick).grid(row=0, column=1, padx=4)

    def action(parent, row, text, fn, note=''):
        b = ctk.CTkButton(parent, text=text, command=lambda: launch(fn))
        b.grid(row=row, column=0, sticky='ew', padx=8, pady=(10, 2)); buttons.append(b)
        if note:
            lab = ctk.CTkLabel(parent, text=note, anchor='w', justify='left', text_color='gray70', wraplength=520)
            lab.grid(row=row + 1, column=0, sticky='ew', padx=10)
            parent.bind('<Configure>', lambda e, l=lab: l.configure(wraplength=max(200, e.width - 40)), add='+')

    def launch(fn):
        if busy[0]:
            return
        save_cfg(); busy[0] = True
        for b in buttons: b.configure(state='disabled')
        def run():
            try:
                fn()
            except Exception as ex:
                log('ERROR: %r' % (ex,))
            finally:
                busy[0] = False
                app.after(0, lambda: [b.configure(state='normal') for b in buttons])
        threading.Thread(target=run, daemon=True).start()

    def need(*keys):
        miss = [k for k in keys if not V[k].get().strip()]
        if miss:
            raise ValueError('Falta completar: ' + ', '.join(miss))

    def get_plan():
        return load_plan(V['data'].get().strip() or None, V['out'].get(), log)

    def do_fast():
        need('forges', 'out')
        plan = get_plan()
        sf = locate_stream_forge(V['forges'].get(), plan)
        if not sf: raise ValueError('No encuentro el forge de streams en español')
        fast_extract_spanish(V['forges'].get(), V['out'].get(), plan, log, prog, save_variants=V['variants'].get(),
                             lang_labels=parse_labels(V['labels'].get()), variants_wav=V['vwav'].get())
        build_map(V['out'].get(), plan, sf, log, rate_fix=parse_ratefix(V['ratefix'].get()))
        log('Listo. Siguiente: pestaña 2 (WAV).')

    def do_wav_vgm():
        need('out', 'vgm')
        export_wavs_vgm(V['out'].get(), V['vgm'].get(), rate_fix=parse_ratefix(V['ratefix'].get()), log=log, progress=prog)

    def do_wav():
        need('forges', 'out')
        sf = locate_stream_forge(V['forges'].get(), get_plan())
        export_spanish_wavs(V['out'].get(), sf, log, prog)
        export_ogg_audio(V['out'].get(), sf, log)

    def do_import():
        need('forges', 'out', 'wavdir')
        langs = [i for i, k in ((3, 'lang_esp'), (1, 'lang_eng')) if V[k].get()]
        if not langs: raise ValueError('Marca al menos un idioma destino (Español / Inglés)')
        d = V['wavdir'].get()
        files = [os.path.join(d, f) for f in sorted(os.listdir(d)) if f.lower().endswith('.wav')] if os.path.isdir(d) else [d]
        import_wavs_auto(files, V['forges'].get(), V['out'].get(), langs,
                         lambda: locate_stream_forge(V['forges'].get(), get_plan()), V['backup'].get(), V['dry'].get(),
                         log, prog, V['plantilla'].get().strip() or None)

    def do_restore():
        need('forges')
        restore_all_backups(V['forges'].get(), log)

    def do_check():
        need('forges', 'out')
        sf = locate_stream_forge(V['forges'].get(), get_plan())
        vgm_crosscheck(V['vgm'].get(), V['out'].get(), sf, 5, log)

    def do_full():
        need('forges', 'out')
        langs, stats = extract_all(V['forges'].get(), V['out'].get(), log, prog)
        log('Extraccion completa: %s' % stats)

    field(t1, 0, 'Carpeta de los .forge del juego', V['forges'], 'dir')
    field(t1, 2, 'Carpeta de salida (aquí se guarda todo)', V['out'], 'dir')
    field(t1, 4, 'Carpeta con los CSV (data.zip descomprimido) - opcional si ac1_spanish_plan.json.gz está junto al script', V['data'], 'dir')
    field(t1, 6, 'Corrección de rate para IMA de voces (ej. 16000:11025; vacío = ninguna)', V['ratefix'], 'text')
    ctk.CTkCheckBox(t1, text='Guardar todas las variantes de idioma en una carpeta por BAO', variable=V['variants']).grid(row=8, column=0, sticky='w', padx=10, pady=(10, 0))
    field(t1, 9, 'Etiquetas de idioma por índice (ej. 1=eng,3=esp,2=fra)', V['labels'], 'text')
    ctk.CTkCheckBox(t1, text='Decodificar las variantes Ogg a WAV (necesita ffmpeg)', variable=V['vwav']).grid(row=11, column=0, sticky='w', padx=10, pady=(6, 0))
    action(t1, 12, 'Extraer español rápido (solo las entradas necesarias)', do_fast,
           'Descomprime solo las entradas del plan en vez de los 18 forges y arma spanish_map.csv (stream ↔ header ↔ rate).')
    field(t2, 0, 'vgmstream-cli', V['vgm'], 'file')
    action(t2, 2, 'Exportar WAV con vgmstream (completo: header + prefetch + stream)', do_wav_vgm,
           'Recomendado: igual que tu batch original, pero con la variante de idioma correcta. Salida: <salida>/spanish/wav/Spanish.')
    action(t2, 4, 'Exportar rápido sin vgmstream (IMA sin prefetch + Ogg en memoria)', do_wav,
           'IMA -> Spanish_BAO_0x<id>.wav en <salida>/spanish/wav. Los audios en memoria son Ogg Vorbis: se guardan como .ogg (y WAV si hay ffmpeg) en <salida>/spanish/ogg.')
    field(t3, 0, 'Carpeta con los WAV editados (mismos nombres que la carpeta wav: BAO_0x<header>.wav, esp_0x........wav, Spanish_BAO_0x........)', V['wavdir'], 'dir')
    field(t3, 2, '_plantilla.csv (opcional: se usa spanish_map.csv / spanish/ogg/_plantilla.csv si existen)', V['plantilla'], 'file')
    ctk.CTkLabel(t3, text='Idioma donde inyectar (puedes marcar los dos):', anchor='w').grid(row=4, column=0, sticky='w', padx=10, pady=(10, 0))
    ctk.CTkCheckBox(t3, text='Español (variante 3)', variable=V['lang_esp']).grid(row=5, column=0, sticky='w', padx=10, pady=2)
    ctk.CTkCheckBox(t3, text='Inglés (variante 1)', variable=V['lang_eng']).grid(row=6, column=0, sticky='w', padx=10, pady=2)
    ctk.CTkCheckBox(t3, text='Crear copia de seguridad .bak de cada forge que se modifique (primera vez)', variable=V['backup']).grid(row=7, column=0, sticky='w', padx=10, pady=(10, 0))
    ctk.CTkCheckBox(t3, text='Solo simular (no escribe nada)', variable=V['dry']).grid(row=8, column=0, sticky='w', padx=10, pady=4)
    action(t3, 9, 'Encodear e importar al forge', do_import,
           'Ogg: encodea a Vorbis con el mismo tamaño, rate, canales y muestras del hueco (silencio o recorte con fade) y lo escribe en el forge que lo contiene; el forge no cambia de tamaño. IMA: igual que antes (solo español).')
    action(t3, 11, 'Restaurar forges desde .bak', do_restore)
    field(t4, 0, 'vgmstream-cli (solo para comprobar el decodificador)', V['vgm'], 'file')
    action(t4, 2, 'Comprobar decodificador vs vgmstream', do_check,
           'Compara 5 streams: si coinciden ~100% el encoder genera lo que el juego espera.')
    action(t4, 4, 'Escaneo completo antiguo (todos los forges)', do_full)
    app.protocol('WM_DELETE_WINDOW', lambda: (save_cfg(), app.destroy()))
    app.mainloop()


if __name__ == '__main__':
    multiprocessing.freeze_support()
    if len(sys.argv) > 1:
        run_cli(sys.argv[1:])
    else:
        run_gui()
