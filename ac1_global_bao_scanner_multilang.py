#!/usr/bin/env python3
"""
AC1 Global BAO Scanner & Linker (PC) - escaneo global de todos los .forge

Replica en Python el pipeline de los BMS:
  .forge (scimitar, VER 0x19)  ->  entradas FILEDATA
      - entradas "<Idioma>_BAO_0x..." / "Common_BAO_0x..."  = streams (BAO directo)
      - entradas con firma .compressed                       = paquetes LZO con BAO_0x...
  paquetes -> BAO_0x20 (headers), BAO_0x30 (prefetch/memoria), etc.
  por idioma: carpeta con todo lo compartido + streams de ese idioma como Common_BAO_0x<id>
  indices globales: inventario Forge, procedencia BAO, hashes, duplicados y conflictos
  vgmstream-cli decodifica cada header -> WAV (resuelve header+prefetch+stream)

Uso GUI : python ac1_bao_batch.py
Uso CLI : python ac1_bao_batch.py <carpeta_forges> <salida> [--vgm RUTA] [--lang Spanish,English]
                                  [--types 1,5,6] [--no-wav] [--no-16000-fix] [--rate-16000-to 11050]
Dependencias: solo libreria estandar. Opcional: python-lzo (mucho mas rapido).
Compresion soportada: LZO1X (ZTYPE 1). LZO2A/LZO1C/XMem se reportan como no soportadas.
"""
import os, re, sys, csv, mmap, struct, shutil, subprocess, threading, wave, argparse, hashlib
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



def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def _safe_resource_name(name):
    """Evita que nombres internos puedan escribir fuera de _store."""
    name = str(name).replace("\\", "/").split("/")[-1].strip()
    if not name or name in (".", ".."):
        raise ValueError("nombre de recurso no valido")
    return name


def _write_csv(path, headers, rows):
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.writer(f)
        writer.writerow(headers)
        writer.writerows(rows)


def extract_all(forge_dir, out_dir, log=print, progress=None):
    """
    Escanea TODOS los .forge recursivamente y construye un indice global.
    Conserva procedencia, hashes y conflictos de nombres entre depots.
    """
    store = os.path.join(out_dir, "_store")
    conflicts_dir = os.path.join(out_dir, "_conflicts")
    os.makedirs(store, exist_ok=True)
    os.makedirs(conflicts_dir, exist_ok=True)

    forges = list_forges(forge_dir)
    stats = {
        "forges": len(forges), "streams": 0, "baos": 0,
        "duplicates_identical": 0, "name_conflicts": 0,
        "unsupported": 0, "errors": 0, "forge_errors": 0
    }
    langs = set()
    source_rows = []
    inventory_rows = []
    master = {}

    def save_resource(name, data, forge_path, forge_entry, kind):
        name = _safe_resource_name(name)
        digest = _sha256(data)
        rel_forge = os.path.relpath(forge_path, forge_dir)
        existing = master.get(name)

        if existing is None:
            target = os.path.join(store, name)
            with open(target, "wb") as f:
                f.write(data)
            master[name] = {
                "kind": kind, "size": len(data), "sha256": digest,
                "sources": [rel_forge], "hashes": {digest},
                "conflicts": 0
            }
            stats["streams" if kind == "stream" else "baos"] += 1
            disposition = "saved"
        elif digest in existing["hashes"]:
            existing["sources"].append(rel_forge)
            stats["duplicates_identical"] += 1
            disposition = "identical_duplicate"
        else:
            # No se descarta el contenido: se conserva aparte para inspeccion.
            alt_name = "%s__conflict_%s" % (name, digest[:10])
            alt_path = os.path.join(conflicts_dir, alt_name)
            if not os.path.exists(alt_path):
                with open(alt_path, "wb") as f:
                    f.write(data)
            existing["sources"].append(rel_forge)
            existing["hashes"].add(digest)
            existing["conflicts"] += 1
            stats["name_conflicts"] += 1
            disposition = "different_content_same_name"
        source_rows.append([
            name, kind, rel_forge, forge_entry, len(data), digest, disposition
        ])

    for fi, fp in enumerate(forges):
        rel_path = os.path.relpath(fp, forge_dir)
        file_size = os.path.getsize(fp)
        forge_ver = ""
        entry_count = 0
        resource_count_before = len(source_rows)
        status = "ok"
        log("[%d/%d] %s" % (fi + 1, len(forges), rel_path))
        try:
            if file_size == 0:
                raise ValueError("archivo vacio")
            with open(fp, "rb") as fh, mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                if len(buf) >= 17 and buf[:9] == FORGE_MAGIC:
                    forge_ver = struct.unpack_from("<I", buf, 9)[0]
                entries = parse_forge(buf)
                entry_count = len(entries)

                for e in entries:
                    if e.offset < 0 or e.size < 0 or e.offset + e.size > len(buf):
                        stats["errors"] += 1
                        continue
                    data = buf[e.offset:e.offset + e.size]
                    m = NAME_RE.match(e.name)

                    if m and data[:4] == BAO_VER:
                        language = m.group("lang")
                        if language.lower() != "common":
                            langs.add(language)
                        save_resource(e.name, data, fp, e.name, "stream")
                    elif data[:4] == BAO_VER and BAO_RE.match(e.name):
                        save_resource(e.name, data, fp, e.name, "bao")
                    elif COMP_SIG in data[:256] or data.find(COMP_SIG) >= 0:
                        local_stats = {}
                        for pack in unpack_compressed(data, local_stats):
                            for name, bao in extract_baos(pack):
                                save_resource(name, bao, fp, e.name, "bao")
                        stats["unsupported"] += local_stats.get("unsupported", 0)
                        stats["errors"] += local_stats.get("errors", 0)

        except Exception as ex:
            status = "error: %r" % ex
            log("  ERROR en %s: %r" % (os.path.basename(fp), ex))
            stats["forge_errors"] += 1

        extracted = len(source_rows) - resource_count_before
        inventory_rows.append([
            rel_path, file_size, forge_ver, entry_count, extracted, status
        ])
        if progress:
            progress(fi + 1, len(forges))

    # Inventario completo: incluso los .forge que no contienen BAO reconocibles.
    _write_csv(
        os.path.join(out_dir, "forge_inventory.csv"),
        ["forge", "size_bytes", "version", "entries", "audio_resources_found", "status"],
        inventory_rows
    )
    _write_csv(
        os.path.join(out_dir, "bao_sources.csv"),
        ["resource", "kind", "source_forge", "source_entry", "size_bytes", "sha256", "disposition"],
        source_rows
    )

    master_rows = []
    duplicate_rows = []
    for name, item in sorted(master.items()):
        hashes = sorted(item["hashes"])
        master_rows.append([
            name, item["kind"], item["size"], item["sha256"],
            len(item["sources"]), " | ".join(item["sources"]),
            item["conflicts"], " | ".join(hashes)
        ])
        if len(item["sources"]) > 1 or item["conflicts"]:
            duplicate_rows.append([
                name, len(item["sources"]), item["conflicts"],
                " | ".join(item["sources"]), " | ".join(hashes)
            ])

    _write_csv(
        os.path.join(out_dir, "bao_master_index.csv"),
        ["resource", "kind", "size_bytes", "canonical_sha256", "source_count",
         "source_forges", "conflict_count", "all_sha256"],
        master_rows
    )
    _write_csv(
        os.path.join(out_dir, "duplicates.csv"),
        ["resource", "source_count", "different_content_count", "source_forges", "hashes"],
        duplicate_rows
    )

    stats["unique_resources"] = len(master)
    stats["source_records"] = len(source_rows)
    stats["identical_duplicates"] = stats["duplicates_identical"]
    log("Indices globales creados: forge_inventory.csv, bao_sources.csv, "
        "bao_master_index.csv y duplicates.csv")
    if stats["name_conflicts"]:
        log("ATENCION: hay nombres repetidos con contenido diferente. "
            "Las variantes se conservaron en _conflicts.")
    return sorted(langs), stats


def _save(store, name, data, stats, key):
    """Compatibilidad con llamadas antiguas."""
    path = os.path.join(store, _safe_resource_name(name))
    if os.path.exists(path):
        stats["dups"] = stats.get("dups", 0) + 1
        return
    with open(path, "wb") as f:
        f.write(data)
    stats[key] += 1


def _link(src, dst):
    if os.path.exists(dst):
        os.remove(dst)
    try:
        os.link(src, dst)
    except OSError:
        shutil.copy2(src, dst)



def parse_header_stream_id(data):
    """Lee el ID de stream del BAO Audio (offset 0x44, little-endian).

    En los BAO_0x20 observados de AC1, el campo de referencia está en 0x44.
    Devuelve None si no parece un header válido o el campo está vacío.
    """
    if len(data) < 0x48 or data[:4] != BAO_VER:
        return None
    try:
        value = struct.unpack_from('<I', data, 0x44)[0]
    except struct.error:
        return None
    return value if value not in (0, 0xFFFFFFFF) else None


def patch_wav_rate_header(path, old_rate=16000, new_rate=11050):
    """Cambia SOLO la frecuencia declarada en RIFF/WAVE; no remuestrea PCM.

    Es la misma clase de ajuste de Sample Rate que el usuario probó:
    los bytes de audio quedan intactos, por lo que cambian velocidad/tono.
    Se limita estrictamente a WAV cuyo fmt.sample_rate == old_rate.
    """
    with open(path, 'r+b') as f:
        if f.read(4) != b'RIFF':
            return False
        f.seek(8)
        if f.read(4) != b'WAVE':
            return False
        pos = 12
        while True:
            f.seek(pos)
            head = f.read(8)
            if len(head) != 8:
                return False
            chunk_id, chunk_size = head[:4], struct.unpack('<I', head[4:])[0]
            data_pos = pos + 8
            if chunk_id == b'fmt ':
                if chunk_size < 16:
                    return False
                f.seek(data_pos)
                fmt = f.read(min(chunk_size, 64))
                if len(fmt) < 16:
                    return False
                rate = struct.unpack_from('<I', fmt, 4)[0]
                byte_rate = struct.unpack_from('<I', fmt, 8)[0]
                if rate != old_rate:
                    return False
                new_byte_rate = int(round(byte_rate * (new_rate / float(old_rate))))
                f.seek(data_pos + 4)
                f.write(struct.pack('<I', new_rate))
                f.write(struct.pack('<I', new_byte_rate))
                return True
            pos = data_pos + chunk_size + (chunk_size & 1)


def build_language_dir(out_dir, lang):
    """Prepara los BAO para un idioma resolviendo streams por ID global.

    Prioridad: stream del idioma exacto > Common_BAO > BAO genérico.
    Los streams de otros idiomas nunca se usan como fallback.
    """
    store = os.path.join(out_dir, "_store")
    dst = os.path.join(out_dir, "bao", lang)
    os.makedirs(dst, exist_ok=True)
    if not os.path.isdir(store):
        raise FileNotFoundError("No existe _store. Ejecuta primero la extraccion.")

    files = [f for f in os.listdir(store) if os.path.isfile(os.path.join(store, f))]
    localized = {}
    common = {}
    generic = {}
    headers = []
    pref = lang + "_BAO_0x"

    for name in files:
        m = NAME_RE.match(name)
        if m:
            if m.group("lang").lower() == lang.lower():
                localized[m.group("id").lower()] = name
            continue
        if HEADER_RE.match(name):
            headers.append(name)
            continue
        m = BAO_RE.match(name)
        if m:
            generic[m.group("id").lower()] = name
            continue
        if name.startswith("Common_BAO_0x"):
            common[name[len("Common_BAO_0x"):].lower()] = name

    # Copiar headers (BAO_0x20...), prefetch y otros BAO necesarios.
    for name in files:
        if name.startswith("BAO_0x") or name.startswith("Common_BAO_0x"):
            _link(os.path.join(store, name), os.path.join(dst, name))

    # Crear un alias Common por cada ID, con fallback neutral y sin mezclar idiomas.
    stream_ids = set(generic) | set(common) | set(localized)
    relationship_rows = []
    for sid in sorted(stream_ids):
        source = localized.get(sid)
        relation = "localized"
        if source is None:
            source = common.get(sid)
            relation = "common" if source else "generic"
        if source is None:
            source = generic.get(sid)
        if source:
            alias = "Common_BAO_0x" + sid
            _link(os.path.join(store, source), os.path.join(dst, alias))
            if source in localized.values():
                _link(os.path.join(store, source), os.path.join(dst, source))
            relationship_rows.append([lang, source, alias, sid, relation])

    # Informe explícito de qué stream resolverá cada header Audio.
    ref_rows = []
    for name in sorted(headers):
        path = os.path.join(store, name)
        try:
            data = open(path, "rb").read()
            sid = parse_header_stream_id(data)
        except OSError:
            sid = None
        if sid is None:
            ref_rows.append([lang, name, "", "", "unparsed_or_no_stream_ref"])
            continue
        key = "%08x" % sid
        source = localized.get(key) or common.get(key) or generic.get(key)
        if key in localized:
            resolution = "localized"
        elif key in common:
            resolution = "common"
        elif key in generic:
            resolution = "generic"
        else:
            resolution = "MISSING"
        ref_rows.append([lang, name, "0x" + key, source or "", resolution])

    _write_csv(
        os.path.join(out_dir, "bao_relationships_%s.csv" % lang),
        ["language", "source_resource", "resolved_resource_name", "resource_id", "relationship"],
        relationship_rows
    )
    _write_csv(
        os.path.join(out_dir, "bao_header_stream_refs_%s.csv" % lang),
        ["language", "header", "stream_id", "selected_stream_resource", "resolution"],
        ref_rows
    )
    return dst, sum(1 for f in files if f.startswith(pref))


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


def export_wavs(out_dir, lang, vgm, types=(1, 5, 6), log=print, workers=None, progress=None,
                fix_16000=True, rate_16000_to=11050):
    bao_dir = os.path.join(out_dir, 'bao', lang)
    wav_dir = os.path.join(out_dir, 'wav', lang)
    os.makedirs(wav_dir, exist_ok=True)
    jobs = []
    for f in sorted(os.listdir(bao_dir)):
        if not HEADER_RE.match(f):
            continue
        info = header_info(os.path.join(bao_dir, f))
        if not info or info[0] != 0x20000000 or info[1] not in types:
            continue
        jobs.append((f, info))
    log('%s: %d headers a exportar' % (lang, len(jobs)))
    rows, done = [], [0]

    def work(job):
        f, (cls, typ, ch) = job
        wav = os.path.join(wav_dir, f + '.wav')
        try:
            r = subprocess.run([vgm, '-i', '-o', wav, os.path.join(bao_dir, f)],
                               capture_output=True, text=True, timeout=120)
            ok = r.returncode == 0 and os.path.exists(wav)
            err = '' if ok else (r.stderr or r.stdout).strip().splitlines()[-1:] or ['?']
        except Exception as ex:
            ok, err = False, [repr(ex)]
        rate = dur = original_rate = correction = ''
        if ok:
            try:
                with wave.open(wav, 'rb') as w:
                    original_rate = w.getframerate()
                    frames = w.getnframes()
                if fix_16000 and original_rate == 16000:
                    if patch_wav_rate_header(wav, 16000, int(rate_16000_to)):
                        correction = 'header_only_%d_to_%d' % (16000, int(rate_16000_to))
                with wave.open(wav, 'rb') as w:
                    rate = w.getframerate()
                    dur = round(w.getnframes() / float(rate), 3)
            except Exception as ex:
                correction = 'rate_check_error: %r' % ex
        done[0] += 1
        if progress:
            progress(done[0], len(jobs))
        return [lang, f, TYPE_NAMES.get(typ, typ), ch, os.path.relpath(wav, out_dir) if ok else '',
                original_rate, rate, dur, correction, 'ok' if ok else 'fail: ' + (err[0] if isinstance(err, list) else err)]

    with ThreadPoolExecutor(max_workers=workers or os.cpu_count() or 4) as ex:
        rows = list(ex.map(work, jobs))
    idx = os.path.join(out_dir, 'index_%s.csv' % lang)
    with open(idx, 'w', newline='', encoding='utf-8') as f:
        w = csv.writer(f)
        w.writerow(['idioma', 'header', 'tipo', 'canales', 'wav', 'rate_original', 'rate_final', 'duracion_s', 'correccion_rate', 'estado'])
        w.writerows(rows)
    ok = sum(1 for r in rows if r[-1] == 'ok')
    log('%s: %d OK, %d fallidos -> %s' % (lang, ok, len(rows) - ok, idx))
    return rows


# ------------------------------------------------------------------- CLI
def run_cli(a):
    os.makedirs(a.out, exist_ok=True)
    langs, stats = extract_all(a.forges, a.out)
    print('Extraccion:', stats)
    print('Idiomas detectados:', langs)
    sel = [l for l in langs if not a.lang or l.lower() in [x.lower() for x in a.lang.split(',')]]
    for l in sel:
        d, n = build_language_dir(a.out, l)
        print('%s: %d streams propios -> %s' % (l, n, d))
        if not a.no_wav:
            export_wavs(a.out, l, a.vgm, tuple(int(x) for x in a.types.split(',')),
                        fix_16000=not a.no_16000_fix, rate_16000_to=a.rate_16000_to)


# ------------------------------------------------------------------- GUI
def run_gui():
    import tkinter as tk
    from tkinter import ttk, filedialog, scrolledtext
    root = tk.Tk()
    root.title('AC1 BAO Batch - extraccion por idioma')
    root.geometry('860x640')
    v_forge, v_out, v_vgm = tk.StringVar(), tk.StringVar(), tk.StringVar(value='vgmstream-cli')
    lang_vars, type_vars = {}, {t: tk.BooleanVar(value=t in (1, 5, 6)) for t in (1, 5, 6, 8)}
    fix_16k_var = tk.BooleanVar(value=True)
    rate_16k_var = tk.StringVar(value='11050')

    def row(r, label, var, pick):
        tk.Label(root, text=label, anchor='w').grid(row=r, column=0, sticky='w', padx=8, pady=3)
        tk.Entry(root, textvariable=var, width=70).grid(row=r, column=1, sticky='ew', padx=4)
        if pick:
            tk.Button(root, text='...', command=pick).grid(row=r, column=2, padx=6)
    row(0, 'Carpeta de .forge', v_forge, lambda: v_forge.set(filedialog.askdirectory() or v_forge.get()))
    row(1, 'Carpeta de salida', v_out, lambda: v_out.set(filedialog.askdirectory() or v_out.get()))
    row(2, 'vgmstream-cli', v_vgm, lambda: v_vgm.set(filedialog.askopenfilename() or v_vgm.get()))
    root.columnconfigure(1, weight=1)
    lf = tk.LabelFrame(root, text=' Idiomas (aparecen tras extraer) ')
    lf.grid(row=3, column=0, columnspan=3, sticky='ew', padx=8, pady=4)
    tf = tk.LabelFrame(root, text=' Tipos de header a exportar ')
    tf.grid(row=4, column=0, columnspan=3, sticky='ew', padx=8, pady=4)
    ratef = tk.LabelFrame(root, text=' Ajuste de Sample Rate ')
    ratef.grid(row=5, column=0, columnspan=3, sticky='ew', padx=8, pady=4)
    tk.Checkbutton(ratef, text='Cambiar SOLO WAV de 16000 Hz a:', variable=fix_16k_var).pack(side='left', padx=6)
    tk.Entry(ratef, textvariable=rate_16k_var, width=8).pack(side='left')
    tk.Label(ratef, text='Hz (solo cabecera; no remuestrea)').pack(side='left', padx=6)
    for t, v in type_vars.items():
        tk.Checkbutton(tf, text='%d %s' % (t, TYPE_NAMES.get(t, '')), variable=v).pack(side='left', padx=6)
    pb = ttk.Progressbar(root); pb.grid(row=7, column=0, columnspan=3, sticky='ew', padx=8, pady=4)
    txt = scrolledtext.ScrolledText(root, height=20); txt.grid(row=8, column=0, columnspan=3, sticky='nsew', padx=8, pady=4)
    root.rowconfigure(8, weight=1)

    def log(m):
        root.after(0, lambda: (txt.insert('end', m + '\n'), txt.see('end')))
    def prog(a, b):
        root.after(0, lambda: pb.configure(maximum=max(b, 1), value=a))

    def t_extract():
        def run():
            langs, stats = extract_all(v_forge.get(), v_out.get(), log, prog)
            log('Extraccion: %s' % stats)
            def fill():
                for w in lf.winfo_children():
                    w.destroy()
                lang_vars.clear()
                for l in langs:
                    lang_vars[l] = tk.BooleanVar(value=True)
                    tk.Checkbutton(lf, text=l, variable=lang_vars[l]).pack(side='left', padx=6)
            root.after(0, fill)
        threading.Thread(target=run, daemon=True).start()

    def t_wav():
        langs = [l for l, v in lang_vars.items() if v.get()]
        types = tuple(t for t, v in type_vars.items() if v.get())
        def run():
            for l in langs:
                d, n = build_language_dir(v_out.get(), l)
                log('%s: %d streams propios' % (l, n))
                export_wavs(v_out.get(), l, v_vgm.get(), types, log, progress=prog,
                            fix_16000=fix_16k_var.get(), rate_16000_to=int(rate_16k_var.get()))
            log('Listo.')
        threading.Thread(target=run, daemon=True).start()

    bf = tk.Frame(root); bf.grid(row=6, column=0, columnspan=3, pady=4)
    tk.Button(bf, text='1) Extraer BAOs de todos los forges', command=t_extract).pack(side='left', padx=6)
    tk.Button(bf, text='2) Exportar WAV por idioma', command=t_wav).pack(side='left', padx=6)
    root.mainloop()


if __name__ == '__main__':
    if len(sys.argv) > 1:
        ap = argparse.ArgumentParser()
        ap.add_argument('forges'); ap.add_argument('out')
        ap.add_argument('--vgm', default='vgmstream-cli')
        ap.add_argument('--lang', default='')
        ap.add_argument('--types', default='1,5,6', help='Tipos BAO a exportar, por ejemplo 1,5,6 o 1,2,3,5,6,8')
        ap.add_argument('--no-wav', action='store_true')
        ap.add_argument('--no-16000-fix', action='store_true', help='No cambiar la cabecera de WAV a 16000 Hz')
        ap.add_argument('--rate-16000-to', type=int, default=11050, help='Frecuencia declarada para WAV de 16000 Hz (default 11050)')
        run_cli(ap.parse_args())
    else:
        run_gui()
