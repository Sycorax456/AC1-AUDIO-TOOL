#!/usr/bin/env python3
"""
AC1 BAO Tool v2.2 (PC) [parcheo LZO] - extraccion rapida en espanol + importar/encodear

Flujo:
  1) Extraer espanol rapido : usa el plan (ac1_spanish_plan.json.gz o los CSV de data.zip) y descomprime solo
                              las entradas de los .forge que contienen headers espanoles. Crea spanish_map.csv.
  2) WAV                    : decodifica los streams Spanish_BAO_0x... (IMA Ubi) con decodificador interno.
  3) Importar               : WAV editado -> IMA -> mismo hueco del forge (tamano y header intactos).
                              Ogg: modo 'append' (agregar al final del forge y repuntar, calidad completa, rate automatico)
                              o modo 'hueco' (mismo tamano).
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


# ------------------------------------------------------------------ LZO1X compresor (v2.2)
class LZOOverflow(Exception):
    """El chunk recomprimido no cabe en su hueco original: 'over' = bytes que sobran."""
    def __init__(self, over):
        Exception.__init__(self, 'el chunk LZO recomprimido excede el hueco por %d bytes' % over)
        self.over = over


def _lzo_tokens(src, depth=24):
    """Parseo voraz con cadenas hash. Tokens (tipo, x, y, s, e): literal (0,s,e,s,e) / match (1,len,dist,s,e)."""
    n = len(src); toks = []; head = {}; i = 0; lit = 0; lim = n - 4; MAXD = 0xBFFF
    while i < lim:
        key = src[i:i + 4]; cand = head.get(key); bl = bd = 0
        if cand:
            c = 0; mx = n - i
            for p in reversed(cand):
                d = i - p
                if d > MAXD: break
                l = 4
                while l < mx and src[p + l] == src[i + l]: l += 1
                if l > bl or (l == bl and d < bd): bl, bd = l, d
                c += 1
                if c >= depth or bl >= 273: break
        if bl >= 4 and not (bd > 0x4000 and bl < 5):
            if i > lit: toks.append((0, lit, i, lit, i))
            toks.append((1, bl, bd, i, i + bl))
            for k in range(i, min(i + bl, lim)):
                kk = src[k:k + 4]; lst = head.get(kk)
                if lst is None: head[kk] = [k]
                else:
                    lst.append(k)
                    if len(lst) > depth * 2: del lst[0]
            i += bl; lit = i
        else:
            lst = head.get(key)
            if lst is None: head[key] = [i]
            else:
                lst.append(i)
                if len(lst) > depth * 2: del lst[0]
            i += 1
    if n > lit: toks.append((0, lit, n, lit, n))
    return toks


def _lzo_emit(src, toks, force=frozenset()):
    """Tokens -> flujo LZO1X estandar (solo M2/M3/M4) con marca de fin. force = indices de match que usan forma M3 (+1 byte)."""
    out = bytearray(); last = -1
    for ti, (k, x, y, s, e) in enumerate(toks):
        if k == 0:
            L = e - s
            if last >= 0 and L <= 3:
                out[last] |= L
            elif last < 0 and not out and L <= 238:
                out.append(17 + L)
            elif 4 <= L <= 18:
                out.append(L - 3)
            else:
                out.append(0); t = L - 18
                while t > 255: out.append(0); t -= 255
                out.append(t)
            out.extend(src[s:e])
        elif k == 2:
            d = y - 1
            out.append(((d & 3) << 2)); last = len(out) - 1
            out.append(d >> 2)
        elif k == 3:
            d = y - 0x801
            out.append(((d & 3) << 2)); last = len(out) - 1
            out.append(d >> 2)
        else:
            length, dist = x, y
            if length <= 8 and dist <= 2048 and ti not in force:
                d = dist - 1
                out.append(((length - 1) << 5) | ((d & 7) << 2)); last = len(out) - 1
                out.append(d >> 3)
            elif dist <= 0x4000:
                d = dist - 1
                if length - 2 <= 31: out.append(32 | (length - 2))
                else:
                    out.append(32); t = length - 2 - 31
                    while t > 255: out.append(0); t -= 255
                    out.append(t)
                last = len(out); out.append((d & 63) << 2); out.append(d >> 6)
            else:
                xx = dist - 0x4000; flag = (xx >> 14) & 1; lo = xx & 0x3FFF
                if length - 2 <= 7: out.append(16 | (flag << 3) | (length - 2))
                else:
                    out.append(16 | (flag << 3)); t = length - 2 - 7
                    while t > 255: out.append(0); t -= 255
                    out.append(t)
                last = len(out); out.append((lo & 63) << 2); out.append(lo >> 6)
    out.extend(b'\x11\x00\x00')
    return bytes(out)


import bisect

def _mcost(length, dist):
    if length <= 8 and dist <= 2048: return 2
    if dist <= 0x4000:
        return 3 if length - 2 <= 31 else 3 + 1 + (length - 2 - 31 - 1) // 255
    return 3 if length - 2 <= 7 else 3 + 1 + (length - 2 - 7 - 1) // 255


def _lzo_tokens_opt(src, depth=64, depth3=32, depth2=12):
    """Parseo optimo (programacion dinamica, costes reales LZO1X incl. M1). Tokens (tipo,x,y,s,e):
    0 literal, 1 match M2/M3/M4, 2 M1 de 2 bytes (tras match+literales 1..3), 3 M1 de 3 bytes (dist 2049..3072, tras literal>=4)."""
    n = len(src)
    if n < 8:
        return [(0, 0, n, 0, n)] if n else []
    INF = 1 << 60
    best = [INF] * (n + 1); best[0] = 0
    back = [None] * (n + 1)          # (p, len, dist, j, kind)
    h4 = {}; h3 = {}; h2 = {}
    fin = [0]; m19ptr = 0; m19 = INF; m19j = -1
    lim = n - 3
    skip_to = 0
    for p in range(lim + 1):
        if p < skip_to:                      # dentro de un match largo: solo indexar
            kk = src[p:p + 4]
            if len(kk) == 4:
                l_ = h4.get(kk)
                if l_ is None: h4[kk] = [p]
                else:
                    l_.append(p)
                    if len(l_) > depth * 2: del l_[0]
            kk = src[p:p + 3]; l_ = h3.get(kk)
            if l_ is None: h3[kk] = [p]
            else:
                l_.append(p)
                if len(l_) > depth3 * 2: del l_[0]
            kk = src[p:p + 2]; l_ = h2.get(kk)
            if l_ is None: h2[kk] = [p]
            else:
                l_.append(p)
                if len(l_) > depth2 * 2: del l_[0]
            continue
        k4 = src[p:p + 4] if p <= n - 4 else None
        c4 = h4.get(k4) if k4 is not None else None
        k3 = src[p:p + 3]; c3 = h3.get(k3)
        k2 = src[p:p + 2]; c2 = h2.get(k2)
        found = []; m1c = []; m13c = []
        if c4:
            cnt = 0
            for q in reversed(c4):
                d = p - q
                if d > 0xBFFF: break
                l = 4; mx = n - p
                while l < mx and src[q + l] == src[p + l]: l += 1
                found.append((l, d)); cnt += 1
                if cnt >= depth or l >= 273: break
        if c3:
            cnt = 0
            for q in reversed(c3):
                d = p - q
                if d > 3072: break
                l = 3; mx = n - p
                while l < mx and src[q + l] == src[p + l]: l += 1
                if d <= 2048: found.append((l, d))
                else: m13c.append(d)
                cnt += 1
                if cnt >= depth3: break
        # M1 de 2 bytes: solo si hay un match terminado en p-1..p-3
        has_prev = best[p - 1] < INF or best[p - 2] < INF or best[p - 3] < INF if p >= 3 else False
        if c2 and has_prev:
            cnt = 0
            for q in reversed(c2):
                d = p - q
                if d > 1024: break
                m1c.append(d); cnt += 1
                if cnt >= depth2: break
        # indexar p
        if k4 is not None:
            if c4 is None: h4[k4] = [p]
            else:
                c4.append(p)
                if len(c4) > depth * 2: del c4[0]
        if c3 is None: h3[k3] = [p]
        else:
            c3.append(p)
            if len(c3) > depth3 * 2: del c3[0]
        if c2 is None: h2[k2] = [p]
        else:
            c2.append(p)
            if len(c2) > depth2 * 2: del c2[0]
        if not (found or m1c or m13c): continue
        while m19ptr < len(fin) and fin[m19ptr] <= p - 19:
            j = fin[m19ptr]
            if j != 0 and best[j] - j < m19: m19 = best[j] - j; m19j = j
            m19ptr += 1
        # gA: cualquier forma ; gB: literal >= 4 (estado 'first_literal')
        gA = INF; gAj = -1; gB = INF; gBj = -1
        if best[p] < gA: gA, gAj = best[p], p
        for L in range(1, min(18, p) + 1):
            j = p - L; b = best[j]
            if b >= INF: continue
            if j == 0: c = b + 1 + L
            elif L <= 3: c = b + L
            else: c = b + L + 1
            if c < gA: gA, gAj = c, j
            if L >= 4 or (j == 0 and L >= 4):
                if c < gB: gB, gBj = c, j
        if m19 < INF:
            c = m19 + p + 2
            if c < gA: gA, gAj = c, m19j
            if c < gB: gB, gBj = c, m19j
        if p >= 19:
            c = (1 + p) if p <= 238 else (p + 2 + (p - 19) // 255)
            if c < gA: gA, gAj = c, 0
            if c < gB: gB, gBj = c, 0
        # --- matches normales
        if gA < INF:
            seen = set()
            for (ml, d) in found:
                minl = 3 if d <= 2048 else 4
                if ml < minl: continue
                ls = set(range(minl, min(ml, 12) + 1)); ls.add(ml)
                for t in (1, 2, 3):
                    if ml - t >= minl: ls.add(ml - t)
                for l in ls:
                    if (l, d) in seen: continue
                    seen.add((l, d))
                    e = p + l; c = gA + _mcost(l, d)
                    if c < best[e]:
                        if best[e] >= INF:
                            if e > fin[-1]: fin.append(e)
                            else: bisect.insort(fin, e)
                        best[e] = c; back[e] = (p, l, d, gAj, 1)
        if found:
            mlx = max(f[0] for f in found)
            if mlx >= 96: skip_to = p + mlx
        # --- M1 de 3 bytes (tras literal >= 4)
        if m13c and gB < INF and p + 3 <= n:
            e = p + 3; c = gB + 2
            if c < best[e]:
                d = m13c[0]
                # longitud exacta 3 (el match puede ser mas largo, pero M1 copia 3)
                if best[e] >= INF:
                    if e > fin[-1]: fin.append(e)
                    else: bisect.insort(fin, e)
                best[e] = c; back[e] = (p, 3, d, gBj, 3)
        # --- M1 de 2 bytes (tras match + 1..3 literales)
        if m1c:
            bc = INF; bj = -1
            for L in (1, 2, 3):
                j = p - L
                if j > 0 and best[j] < INF and best[j] + L + 2 < bc: bc, bj = best[j] + L + 2, j
            if bc < INF and p + 2 <= n:
                e = p + 2
                if bc < best[e]:
                    if best[e] >= INF:
                        if e > fin[-1]: fin.append(e)
                        else: bisect.insort(fin, e)
                    best[e] = bc; back[e] = (p, 2, m1c[0], bj, 2)
    # --- cierre: literales finales
    endc = INF; endj = -1
    for L in range(0, min(n, 400) + 1):
        j = n - L
        if best[j] >= INF: continue
        if L == 0: c = best[j]
        elif j == 0: c = best[j] + 1 + L
        elif L <= 3: c = best[j] + L
        elif L <= 18: c = best[j] + L + 1
        else: c = best[j] + L + 2 + (L - 19) // 255
        if c < endc: endc, endj = c, j
    for j in fin:
        if j < n - 400 and j != 0:
            L = n - j; c = best[j] + L + 2 + (L - 19) // 255
            if c < endc: endc, endj = c, j
    if endj < 0: return [(0, 0, n, 0, n)]
    toks = []
    if endj < n: toks.append((0, endj, n, endj, n))
    e = endj
    while e > 0:
        p, l, d, gj, kind = back[e]
        toks.append((kind, l, d, p, e))
        if gj < p: toks.append((0, gj, p, gj, p))
        e = gj
    toks.reverse()
    return toks


def _lzo_legal(toks):
    """Comprueba que las secuencias con M1 (tipos 2 y 3) siguen siendo decodificables."""
    for i, (k, x, y, s, e) in enumerate(toks):
        if k == 2:
            if not (i >= 2 and toks[i - 1][0] == 0 and 1 <= toks[i - 1][4] - toks[i - 1][3] <= 3 and toks[i - 2][0] in (1, 2, 3)): return False
        elif k == 3:
            if not (i >= 1 and toks[i - 1][0] == 0 and toks[i - 1][4] - toks[i - 1][3] >= 4): return False
    return True


def _lzo_parse(src, depth=64):
    try:
        t = _lzo_tokens_opt(src)
        if _lzo_legal(t): return t
    except Exception:
        pass
    return _lzo_tokens(src, depth)


def lzo1x_compress(src, depth=24):
    src = bytes(src)
    return _lzo_emit(src, _lzo_parse(src))


def _lzo_grow(src, toks, target):
    """Agranda el flujo SIN cambiar lo que descomprime hasta medir exactamente `target` (None si no se logra)."""
    toks = list(toks); force = set()
    for _ in range(300):
        cur = _lzo_emit(src, toks, force); rem = target - len(cur)
        if rem == 0: return cur
        if rem < 0: return None
        m2 = [i for i, t in enumerate(toks) if t[0] == 1 and t[1] <= 8 and t[2] <= 2048 and i not in force]
        if len(m2) >= rem:
            force.update(m2[:rem]); continue
        # convertir un match en literales (delta mayor que quepa) y reintentar
        best = None
        cands = sorted((i for i, t in enumerate(toks) if t[0] == 1 and t[1] <= rem + 4), key=lambda i: -toks[i][1])[:40]
        for i in cands:
            t2 = list(toks); k, x, y, s, e = t2[i]; t2[i] = (0, s, e, s, e)
            j = i
            if j + 1 < len(t2) and t2[j + 1][0] == 0:
                a = t2[j]; b = t2[j + 1]; t2[j:j + 2] = [(0, a[3], b[4], a[3], b[4])]
            if j > 0 and t2[j - 1][0] == 0:
                a = t2[j - 1]; b = t2[j]; t2[j - 1:j + 1] = [(0, a[3], b[4], a[3], b[4])]
            nf = {f - (1 if f > i and False else 0) for f in ()}   # force se reconstruye vacio tras reindexar
            if not _lzo_legal(t2): continue
            d = len(_lzo_emit(src, t2)) - len(_lzo_emit(src, toks))
            if 0 < d <= rem and (best is None or d > best[0]): best = (d, t2)
        if best is None: return None
        toks = best[1]; force = set()
    return None


def lzo1x_fit(src, target, depth=24):
    """Comprime a EXACTAMENTE `target` bytes (el hueco del chunk). -> (bytes, modo). Lanza LZOOverflow si no cabe.
    modo: 'exacto' o 'ceros:N' (relleno con N ceros tras la marca de fin, solo si no se pudo igualar exacto)."""
    src = bytes(src); toks = _lzo_parse(src, depth)
    comp = _lzo_emit(src, toks)
    if len(comp) > target: raise LZOOverflow(len(comp) - target)
    k = target - len(comp)
    if k == 0: return comp, 'exacto'
    g = _lzo_grow(src, toks, target)
    if g is not None and len(g) == target: return g, 'exacto'
    return comp + b'\x00' * k, 'ceros:%d' % k


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


def forge_folder_name(forge_file):
    """DataPC_Present_Room.forge -> Present_Room ; DataPC.forge -> DataPC."""
    b = os.path.splitext(os.path.basename(forge_file))[0]
    if b.lower().startswith('datapc_') and len(b) > 7: b = b[7:]
    return re.sub(r'[<>:"/\\|?*]', '_', b) or '_sin_forge'


def make_forge_resolver(top_out):
    """Devuelve f(header, stream) -> carpeta del forge al que pertenece el audio (segun el plan: provenance de
    cada header; si no, el forge del stream). Sin dato: '_sin_forge'."""
    try: plan = load_plan(None, top_out, log=lambda *a: None)
    except Exception: plan = {}
    prov = {k.lower(): v for k, v in (plan.get('provenance') or {}).items()}
    strm = {k.lower(): v for k, v in (plan.get('streams') or {}).items()}

    def res(header='', stream=''):
        v = prov.get((header or '').lower())
        if v and v[0] and v[0][0]: return forge_folder_name(v[0][0])
        v = strm.get((stream or '').lower())
        if v and v[0]: return forge_folder_name(v[0])
        return '_sin_forge'
    return res


# =====================================================================
#  v2.5: salida ordenada  spanish/Audio/<OST|Historia|NPC|Extras>/<BAO>/<archivo>.wav
#        OST = 48000 Hz | Historia = 24000 Hz | NPC = 11025 Hz (los 16000 ya vienen corregidos) | Extras = el resto
# =====================================================================
AUDIO_FOLDERS = ('OST', 'Historia', 'NPC', 'Extras')
AUDIO_BY_RATE = {48000: 'OST', 24000: 'Historia', 11025: 'NPC'}


def audio_category(rate):
    try: return AUDIO_BY_RATE.get(int(rate or 0), 'Extras')
    except Exception: return 'Extras'


def _wav_rate(path):
    """Sample rate leyendo solo la cabecera 'fmt ' del WAV (0 si no se puede)."""
    try:
        with open(path, 'rb') as f:
            hd = f.read(12)
            if len(hd) < 12 or hd[8:12] != b'WAVE': return 0
            while True:
                ch = f.read(8)
                if len(ch) < 8: return 0
                cid, csz = struct.unpack('<4sI', ch)
                if cid == b'fmt ':
                    return struct.unpack('<I', f.read(8)[4:8])[0]
                f.seek(csz + (csz & 1), 1)
    except Exception:
        return 0


def _merge_dir(src, dst):
    for fn in os.listdir(src):
        os.replace(os.path.join(src, fn), os.path.join(dst, fn))
    try: os.rmdir(src)
    except OSError: pass


def _place_audio(root, src, bao):
    """Mueve un WAV a <root>/Audio/<categoria>/<bao>/ segun su frecuencia real. Devuelve la ruta nueva."""
    cat = audio_category(_wav_rate(src))
    dst_dir = os.path.join(root, 'Audio', cat, bao); os.makedirs(dst_dir, exist_ok=True)
    dst = os.path.join(dst_dir, os.path.basename(src)); os.replace(src, dst)
    for c in AUDIO_FOLDERS:                       # si ese BAO estaba en otra categoria (p. ej. antes de la regla de rates), se junta
        o = os.path.join(root, 'Audio', c, bao)
        if c != cat and os.path.isdir(o): _merge_dir(o, dst_dir)
    return dst


def _primary_wav(paths, bao):
    names = {os.path.basename(p).lower(): p for p in paths}
    if (bao + '.wav').lower() in names: return names[(bao + '.wav').lower()]
    for pre in ('esp_', 'spanish_'):
        for k in sorted(names):
            if k.startswith(pre): return names[k]
    return sorted(paths)[0]


def organize_audio(root, log=print):
    """Reordena los WAV de <root>/<Forge>/WAV/<BAO>/ en <root>/Audio/<OST|Historia|NPC|Extras>/<BAO>/.
    Todos los archivos de un BAO (BAO_0x...wav, esp_, eng_, L2_...) quedan juntos; la categoria sale de la frecuencia
    del WAV principal (o de la carpeta que ese BAO ya tenga en Audio/). Se puede repetir sin problema."""
    skip = {'audio', 'bao', '_store', 'variants', 'ogg'}
    groups = collections.defaultdict(list)
    forge_dirs = []
    for fk in sorted(os.listdir(root)):
        wdir = os.path.join(root, fk, 'WAV')
        if fk.lower() in skip or not os.path.isdir(wdir): continue
        forge_dirs.append(os.path.join(root, fk))
        for bao in os.listdir(wdir):
            d = os.path.join(wdir, bao)
            if os.path.isdir(d):
                groups[bao] += [os.path.join(d, fn) for fn in os.listdir(d) if fn.lower().endswith('.wav')]
    nfiles = 0
    for bao, paths in groups.items():
        if not paths: continue
        main = [q for q in paths if os.path.basename(q).lower() == (bao + '.wav').lower() or os.path.basename(q).lower().startswith('spanish_')]
        if main:                                   # WAV principal nuevo: manda su frecuencia (asi un BAO migra si cambia la regla de rates)
            cat = audio_category(_wav_rate(main[0]))
        else:                                      # solo variantes (esp_/eng_/L2_...): siguen a la carpeta que el BAO ya tenga
            cat = next((c for c in AUDIO_FOLDERS if os.path.isdir(os.path.join(root, 'Audio', c, bao))), None)
            if cat is None: cat = audio_category(_wav_rate(_primary_wav(paths, bao)))
        dst_dir = os.path.join(root, 'Audio', cat, bao); os.makedirs(dst_dir, exist_ok=True)
        for p in paths:
            os.replace(p, os.path.join(dst_dir, os.path.basename(p))); nfiles += 1
        for c in AUDIO_FOLDERS:
            o = os.path.join(root, 'Audio', c, bao)
            if c != cat and os.path.isdir(o): _merge_dir(o, dst_dir)
    for fd in forge_dirs:                          # limpia carpetas vacias <Forge>/WAV/<BAO>
        wdir = os.path.join(fd, 'WAV')
        for bao in os.listdir(wdir):
            try: os.rmdir(os.path.join(wdir, bao))
            except OSError: pass
        for d in (wdir, fd):
            try: os.rmdir(d)
            except OSError: pass
    cnt = {c: (len(os.listdir(os.path.join(root, 'Audio', c))) if os.path.isdir(os.path.join(root, 'Audio', c)) else 0) for c in AUDIO_FOLDERS}
    log('Audio ordenado en %s: %d archivos movidos | carpetas BAO: %s' % (
        os.path.join(root, 'Audio'), nfiles, ', '.join('%s %d' % (c, n) for c, n in cnt.items())))
    return cnt


def export_wavs(out_dir, lang, vgm, types=(1, 5, 6), log=print, workers=None, progress=None,
                rate_fix=None, only_backed=False, patch=True):
    bao_dir = os.path.join(out_dir, 'bao', lang)
    fres = make_forge_resolver(os.path.dirname(os.path.normpath(out_dir)))   # <forge>/WAV/<BAO>/<BAO>.wav
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
        wdir_ = os.path.join(out_dir, fres(f), 'WAV', f); os.makedirs(wdir_, exist_ok=True)
        wav = os.path.join(wdir_, f + '.wav')
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
                inline_ima = bool(h) and RATE_FIX_INLINE and h['codec'] != 4 and not h['is_stream']
                if plan is None and h and h['sample_rate'] in rate_fix and (backed == 'idioma' or inline_ima) and rate_vgm in rate_fix:
                    relabel_wav_rate(wav, rate_fix[rate_vgm]); rate_final = rate_fix[rate_vgm]
                with wave.open(wav, 'rb') as w:
                    dur = round(w.getnframes() / float(w.getframerate()), 3)
            except Exception:
                pass
            try:
                wav = _place_audio(out_dir, wav, f)      # v2.5: Audio/<OST|Historia|NPC|Extras>/<BAO>/
            except Exception:
                pass
            try: os.rmdir(wdir_)
            except OSError: pass
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
    try: organize_audio(out_dir, log)       # limpia carpetas <Forge>/WAV vacias y junta lo que haya quedado
    except Exception as ex: log('  (no se pudo ordenar: %r)' % (ex,))
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
DEFAULT_RATE = 11025       # v2.5: regla fija, todo 16000 es 11025 (streams sin header incluidos)
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


RATE_FIX = {16000: 11025}    # REGLA FIJA: todo 16000 es 11025 (NPC). Referencia: 32000 ambiental | 48000 OST/SFX | 11025 NPC | 24000 dialogos de historia
RATE_FIX_INLINE = True       # v2.4: aplicar tambien la correccion a los IMA 'inline' (dentro del forge del nivel); antes solo a los 'stream'


def parse_ratefix(txt):
    # v2.5: la regla es fija (16000 -> 11025); ya no hay campo en la interfaz. Se acepta --ratefix por CLI solo para pruebas.
    if not (txt or '').strip():
        return dict(RATE_FIX)
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
    import base64
    plan = json.loads(gzip.decompress(base64.b64decode(''.join(_EMB_PLAN))).decode('utf-8'))
    log('Plan incrustado en el script (%d entradas a descomprimir)' % len(plan['cover']))
    return plan


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
    if variants_wav and not ff:
        log('  AVISO: no encuentro ffmpeg en el PATH; las variantes se guardan solo como .ogg/.bao (sin .wav)')
    vdir, odir = os.path.join(root, 'variants'), os.path.join(root, 'ogg')
    fres = make_forge_resolver(os.path.dirname(os.path.normpath(root)))
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
                fk = fres(n)
                gdir = os.path.join(root, fk, 'OGG', n); os.makedirs(gdir, exist_ok=True)
                fn = '%s_%s' % (lab, bid)
                with open(os.path.join(gdir, fn + '.ogg'), 'wb') as f: f.write(ab[HEADER_SKIP:])
                no += 1
                if ff:
                    wdir_ = os.path.join(root, fk, 'WAV', n); os.makedirs(wdir_, exist_ok=True)
                    if subprocess.run([ff, '-v', 'error', '-y', '-i', os.path.join(gdir, fn + '.ogg'),
                                       os.path.join(wdir_, fn + '.wav')]).returncode == 0:
                        nw += 1
                rate, smp = _ogg_info(ab)
                man.append(['/'.join((fk, 'OGG', n, fn + '.ogg')), n, bid, k, lab, 'OGG', rate, smp, dn])
        nv += 1
    if man:
        os.makedirs(odir, exist_ok=True); _manifest_update(odir, man)
    if nw: organize_audio(root, log)
    log('Variantes: %d BAO en %s (.bao crudos). Audio por idioma en %s/<Forge>/OGG|WAV: %d .ogg%s, plantilla: ogg/_plantilla.csv' %
        (nv, vdir, root, no, ', %d .wav' % nw if ff else ''))
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
        elif rate in rf and (streamed or RATE_FIX_INLINE):
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
    wdir = os.path.join(out_dir, 'spanish')
    fres = make_forge_resolver(out_dir)
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
        odir_ = os.path.join(wdir, fres(r['header'], r['stream']), 'WAV', r['header'] or r['stream']); os.makedirs(odir_, exist_ok=True)
        tasks.append((stream_forge, off, size, int(r['rate']), os.path.join(odir_, r['stream'] + '.wav')))
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
    organize_audio(wdir, log)
    return done, errs


def export_ogg_audio(out_dir, stream_forge=None, log=print, ffmpeg=None):
    """Audio Ogg completo en memoria (idioma elegido) -> <Forge>/OGG/<BAO>/esp_<id>.ogg y <Forge>/WAV/<BAO>/esp_<id>.wav
    (con ffmpeg), p. ej. DataPC_Present_Room.forge -> Present_Room/OGG/BAO_0x20a20000/. _plantilla.csv queda en ogg/."""
    root = os.path.join(out_dir, 'spanish')
    rows = [r for r in read_map(out_dir) if r.get('codec') == 'OGG' and r['source'] == 'inline' and r['prefetch'] in ('', '0') and r['header']]
    odir = os.path.join(root, 'ogg'); os.makedirs(odir, exist_ok=True)
    ff = ffmpeg or shutil.which('ffmpeg')
    lab = LANG_LABELS.get(DEFAULT_LANG_IDX, 'esp')
    fres = make_forge_resolver(out_dir)
    n = w = 0
    man = []
    for r in rows:
        p0 = os.path.join(root, 'bao', LANG, r['stream'])
        if not os.path.exists(p0): continue
        data = open(p0, 'rb').read()
        if data[HEADER_SKIP:HEADER_SKIP + 4] != b'OggS': continue
        fk = fres(r['header'], r['stream'])
        gdir = os.path.join(root, fk, 'OGG', r['header']); os.makedirs(gdir, exist_ok=True)
        fn = '%s_%s' % (lab, base_id(r['header']))
        with open(os.path.join(gdir, fn + '.ogg'), 'wb') as f: f.write(data[HEADER_SKIP:])
        n += 1
        if ff:
            wdir_ = os.path.join(root, fk, 'WAV', r['header']); os.makedirs(wdir_, exist_ok=True)
            if subprocess.run([ff, '-v', 'error', '-y', '-i', os.path.join(gdir, fn + '.ogg'), os.path.join(wdir_, fn + '.wav')]).returncode == 0:
                w += 1
        rate, smp = _ogg_info(data)
        man.append(['/'.join((fk, 'OGG', r['header'], fn + '.ogg')), r['header'], base_id(r['header']), DEFAULT_LANG_IDX, lab, 'OGG', rate, smp, r['stream']])
    if man: _manifest_update(odir, man)
    if w: organize_audio(root, log)
    log('Ogg: %d en %s/<Forge>/OGG%s' % (n, root, (' (+%d WAV en Audio/<categoria>/<BAO> con ffmpeg)' % w) if ff else ' (sin ffmpeg: solo .ogg)'))
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


def _ogg_headers(d):
    """(paquetes [id, comentario, setup], offset donde empieza el audio) o None si la cabecera no son 2 paginas."""
    pk, cur, p, end = [], b'', 0, 0
    while p < len(d) and len(pk) < 3:
        if d[p:p + 4] != b'OggS': return None
        ns = d[p + 26]; seg = d[p + 27:p + 27 + ns]; q = p + 27 + ns
        for s in seg:
            cur += d[q:q + s]; q += s
            if s < 255: pk.append(cur); cur = b''
        p = q
        if len(pk) >= 3: end = p
    if len(pk) < 3 or d[:end].count(b'OggS') != 2: return None
    return pk, end


def _ogg_page(pkts, seq, htype, serial):
    segs, body = bytearray(), b''
    for k in pkts:
        n = len(k); segs += b'\xff' * (n // 255) + bytes([n % 255]); body += k
    if len(segs) > 255: raise ValueError('pagina Ogg de cabecera demasiado grande')
    return b'OggS' + bytes([0, htype]) + struct.pack('<qIII', 0, serial, seq, 0) + bytes([len(segs)]) + bytes(segs) + body


def _comment_pad(cpk, extra, layout=0):
    """Comentario Vorbis original + una entrada de relleno que suma exactamente `extra` bytes (0 o >= 4)."""
    if extra == 0: return cpk
    L = extra - 4
    vl, = struct.unpack_from('<I', cpk, 7); pos = 11 + vl
    cnt, = struct.unpack_from('<I', cpk, pos)
    if cpk[-1:] != b'\x01': raise ValueError('comentario Vorbis sin bit de cierre')
    ent = (b'PAD=' + b'x' * (L - 4)) if (layout == 0 and L >= 4) else b'x' * L
    if layout == 2:       # relleno antes de los comentarios originales
        return cpk[:pos] + struct.pack('<I', cnt + 1) + struct.pack('<I', L) + ent + cpk[pos + 4:]
    return cpk[:pos] + struct.pack('<I', cnt + 1) + cpk[pos + 4:-1] + struct.pack('<I', L) + ent + b'\x01'


def _assemble_ogg(old_pk, d, extra, serial, layout=0):
    """Cabecera ID + comentario del Ogg ORIGINAL (asi LZO sigue deduplicandolos entre idiomas) + setup y audio nuevos."""
    new_pk, end = _ogg_headers(d)
    idp = old_pk[0] if (len(old_pk[0]) == len(new_pk[0]) and old_pk[0][11:16] == new_pk[0][11:16]
                        and old_pk[0][28:29] == new_pk[0][28:29]) else new_pk[0]
    p1 = _ogg_page([idp], 0, 2, serial)
    p2 = _ogg_page([_comment_pad(old_pk[1], extra, layout), new_pk[2]], 1, 0, serial)
    return ogg_set_serial(p1 + p2 + d[end:], serial)


def _fit_ogg(old_pk, d, target, serial, layout=0):
    """Ogg de EXACTAMENTE `target` bytes (rellenando el comentario) o None."""
    n = target - len(_assemble_ogg(old_pk, d, 0, serial, layout))
    if n < 0 or 0 < n < 4: return None
    if n == 0: return _assemble_ogg(old_pk, d, 0, serial, layout)
    for e in range(max(4, n - n // 255 - 3), n + 2):
        r = _assemble_ogg(old_pk, d, e, serial, layout)
        if len(r) == target: return r
    return None


def encode_ogg_slot(wav_path, old_bao, ffmpeg=None, audio_budget=None, layout=0):
    """WAV -> BAO de datos Ogg con el MISMO tamano, rate, canales, muestras y serial que old_bao.
    La cabecera ID y el comentario se toman del Ogg original; el hueco sobrante se rellena con una entrada de
    comentario (muy compresible). audio_budget (opcional) limita los bytes de audio+setup para que, en paquetes
    con chunks LZO, el chunk recomprimido siga cabiendo en su hueco original."""
    ff = ffmpeg or shutil.which('ffmpeg')
    if not ff: raise RuntimeError('no encuentro ffmpeg (con libvorbis) en el PATH')
    if old_bao[HEADER_SKIP:HEADER_SKIP + 4] != b'OggS': raise ValueError('la variante original no contiene Ogg')
    old = old_bao[HEADER_SKIP:]
    ch, rate, gran, serial = ogg_stream_info(old)
    oh = _ogg_headers(old)
    if not oh: raise ValueError('el Ogg original no tiene la estructura de cabecera esperada (ID, comentario+setup)')
    old_pk = oh[0]
    target = len(old)
    budget = target if audio_budget is None else max(1, min(target, audio_budget))
    with tempfile.TemporaryDirectory() as tmp:
        w1 = os.path.join(tmp, 'in.wav'); w2 = os.path.join(tmp, 'fit.wav')
        subprocess.run([ff, '-v', 'error', '-y', '-i', wav_path, '-ac', str(ch), '-ar', str(rate), '-c:a', 'pcm_s16le', w1], check=True)
        with wave.open(w1) as w: raw = w.readframes(w.getnframes())
        dur_in = len(raw) / 2.0 / ch / rate
        cut = False
        if gran > 0: raw, cut = _fit_pcm(raw, ch, gran, rate)
        with wave.open(w2, 'wb') as w:
            w.setnchannels(ch); w.setsampwidth(2); w.setframerate(rate); w.writeframes(raw)
        cache = {}
        def enc(q):
            k = round(q, 3)
            if k not in cache:
                d = _vorbis_run(ff, w2, q, 0, tmp)
                if not _ogg_headers(d): raise ValueError('salida de ffmpeg con cabecera Ogg inesperada')
                cache[k] = (d, len(_assemble_ogg(old_pk, d, 0, serial, 0)))
            return cache[k]
        lo, hi, best = -0.1, 10.0, None
        for _ in range(12):                      # mayor calidad que quepa en el presupuesto
            q = (lo + hi) / 2
            d, sz = enc(q)
            if sz <= budget: best, lo = q, q
            else: hi = q
        if best is None: raise ValueError('no cabe en el hueco ni a la calidad minima (el audio es demasiado largo/complejo)')
        res = None; qf = best
        for q in (best, best - 0.05, best - 0.1, best - 0.2, best - 0.4, best - 0.8):
            d, sz = enc(q)
            if sz > budget: continue
            res = _fit_ogg(old_pk, d, target, serial, layout); qf = q
            if res: break
        if not res: raise ValueError('no se pudo igualar el tamano exacto del hueco')
    g2 = ogg_stream_info(res)[2]
    return old_bao[:HEADER_SKIP] + res, dict(q=round(qf, 2), rate=rate, ch=ch, cut=cut, dur_in=round(dur_in, 3),
                                               dur_slot=round(gran / float(rate), 3) if gran > 0 else 0, granule=g2, old_granule=gran,
                                               audio=budget)


def _adler0(d):                                  # CRC de chunk del .compressed (verificado: Adler-32 con semilla 0)
    return zlib.adler32(bytes(d), 0) & 0xFFFFFFFF


class OggPack:
    """Paquete .compressed dentro de un forge. Lee y escribe tanto chunks sin comprimir como chunks LZO
    (estos se recomprimen y se rellenan hasta el tamano comprimido original, asi el forge no cambia de tamano)."""
    def __init__(self, buf, sig):
        self.buf, self.sig = buf, sig
        p = sig + 8
        _v, self.ztype, _ms, _mz, n = struct.unpack_from('<HBHHH', buf, p); p += 9
        tbl = [struct.unpack_from('<HH', buf, p + 4 * i) for i in range(n)]; p += 4 * n
        self.chunks, v = [], 0                    # (pos_crc, pos_datos, size, zsize, inicio_virtual)
        for sz, zs in tbl:
            self.chunks.append((p, p + 4, sz, zs, v)); p += 4 + zs; v += sz
        self.end, self.vsize = p, v
        self._plain = {}                          # cache de chunks LZO descomprimidos

    def has_lzo(self):
        return any(sz != zs for _cp, _dp, sz, zs, _vs in self.chunks)

    def locate(self, fpos):
        """posicion de archivo -> offset virtual (solo si cae en un chunk sin comprimir)."""
        for cp, dp, sz, zs, vs in self.chunks:
            if dp <= fpos < dp + zs:
                return vs + (fpos - dp) if sz == zs else None
        return None

    def _chunk_plain(self, ci):
        cp, dp, sz, zs, vs = self.chunks[ci]
        if sz == zs: return bytes(self.buf[dp:dp + zs])
        p = self._plain.get(ci)
        if p is None:
            if self.ztype != 1: raise ValueError('ZTYPE %d no soportado (1=LZO1X)' % self.ztype)
            p = lzo1x_decompress(bytes(self.buf[dp:dp + zs]), sz)
            if len(p) != sz: raise ValueError('chunk %d: la descompresion dio %d bytes en vez de %d' % (ci, len(p), sz))
            self._plain[ci] = p
        return p

    def find_name(self, name):
        """offset virtual del nombre `name` (BAO_0x........) dentro del paquete descomprimido, o None."""
        allp = b''.join(self._chunk_plain(ci) for ci in range(len(self.chunks)))
        want = name.lower()
        for m in _NAME_RX.finditer(allp):
            if m.group()[:-1].decode().lower() != want: continue
            o = m.start()
            if o >= 12 and struct.unpack_from('<I', allp, o - 4)[0] in (len(name), len(name) + 1): return o
        return None

    def read(self, voff, n):
        out, end = bytearray(), voff + n
        for ci, (cp, dp, sz, zs, vs) in enumerate(self.chunks):
            if vs + sz <= voff or vs >= end: continue
            a, b = max(voff, vs), min(end, vs + sz)
            out += self._chunk_plain(ci)[a - vs:b - vs]
        if len(out) != n: raise ValueError('el BAO se sale del paquete')
        return bytes(out)

    def prepare(self, voff, data):
        """Calcula (sin escribir) lo que hay que grabar. Lanza LZOOverflow si un chunk LZO no cabe en su hueco."""
        ops, end = [], voff + len(data)
        for ci, (cp, dp, sz, zs, vs) in enumerate(self.chunks):
            if vs + sz <= voff or vs >= end: continue
            a, b = max(voff, vs), min(end, vs + sz)
            part = data[a - voff:b - voff]
            if sz == zs:
                ops.append((ci, dp + (a - vs), part, None, 'directo'))
            else:
                plain = bytearray(self._chunk_plain(ci)); plain[a - vs:b - vs] = part; plain = bytes(plain)
                comp, mode = lzo1x_fit(plain, zs)
                real = comp[:len(comp) - int(mode.split(':')[1])] if mode.startswith('ceros') else comp
                if lzo1x_decompress(real, sz) != plain: raise ValueError('chunk %d: verificacion LZO fallo (no se escribe nada)' % ci)
                ops.append((ci, dp, comp, plain, mode))
        if sum(len(o[2]) for o in ops if o[3] is None) + sum(min(len(o[2]), 0) for o in ops) < 0: raise ValueError('interno')
        return ops

    def commit(self, fh, ops):
        for ci, fpos, payload, plain, mode in ops:
            fh.seek(fpos); fh.write(payload)
            if plain is not None: self._plain[ci] = plain
        fh.flush()
        for ci in sorted({o[0] for o in ops}):
            cp, dp, sz, zs, vs = self.chunks[ci]
            fh.seek(dp); d = fh.read(zs)
            fh.seek(cp); fh.write(struct.pack('<I', _adler0(d)))
        fh.flush()
        return [o[4] for o in ops]

    def write(self, fh, voff, data):
        return self.commit(fh, self.prepare(voff, data))


def ogg_variants_at(buf, t, name):
    """BAO de datos `name` cuyo nombre esta en el offset t del forge -> (OggPack, {idx: (voff, size)}) o None.
    Si t cae dentro de un chunk LZO (o es el inicio del paquete) el nombre se busca en el paquete descomprimido."""
    s = buf.rfind(COMP_SIG_OGG, 0, t)
    if s < 0: return None
    try: pk = OggPack(buf, s)
    except Exception: return None
    if t >= pk.end: return None
    try:
        vt = pk.locate(t)
        if vt is None: vt = pk.find_name(name)
        if vt is None: return None
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
    return pk, vs


_NAME_RX = re.compile(rb'BAO_0x[0-9a-fA-F]{8}\x00')


def _deep_scan(fp, left, found, log, prefer_lzo=True):
    """Recorre los paquetes del forge y busca nombres dentro de los chunks LZO descomprimidos."""
    nbs = {n.lower(): 1 for n in left}
    try:
        with open(fp, 'rb') as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as buf:
            pos, npk, nlzo = 0, 0, 0
            while nbs:
                s = buf.find(COMP_SIG_OGG, pos)
                if s < 0: break
                try: pk = OggPack(buf, s)
                except Exception: pos = s + 8; continue
                pos = max(pk.end, s + 8); npk += 1
                if not pk.has_lzo(): continue
                nlzo += 1
                if nlzo % 200 == 0: log('    ... %d paquetes LZO revisados en %s' % (nlzo, _bn(fp)))
                try:
                    allp = b''.join(pk._chunk_plain(ci) for ci in range(len(pk.chunks)))
                except Exception:
                    continue
                for m in _NAME_RX.finditer(allp):
                    n = m.group()[:-1].decode().lower()
                    if n not in nbs: continue
                    o = m.start()
                    if o >= 12 and struct.unpack_from('<I', allp, o - 4)[0] in (len(n), len(n) + 1):
                        found[n].append((fp, s + 8)); del nbs[n]
                        if not nbs: break
            log('  busqueda profunda en %s: %d paquetes, %d con LZO' % (_bn(fp), npk, nlzo))
    except (ValueError, OSError) as ex:
        log('  (omitido %s: %s)' % (_bn(fp), ex))


def ogg_index_forges(forge_dir, names, log=print):
    """Una pasada por forge: nombre de BAO de datos -> [(ruta_forge, offset)]. Los nombres que no aparecen en claro
    (porque estan en chunks LZO) se buscan despues descomprimiendo los paquetes."""
    want = {n.lower(): [] for n in names}
    rx = re.compile(rb'BAO_0x[0-9a-fA-F]{8}\x00')
    forges = list_forges(forge_dir)
    hits = {}
    for k, fp in enumerate(forges):
        log('  buscando en %s (%d/%d)' % (_bn(fp), k + 1, len(forges)))
        try:
            with open(fp, 'rb') as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                for m in rx.finditer(buf):
                    nm = m.group()[:-1].decode().lower()
                    if nm in want: want[nm].append((fp, m.start())); hits[fp] = hits.get(fp, 0) + 1
        except (ValueError, OSError) as ex:
            log('  (omitido %s: %s)' % (_bn(fp), ex))
        if all(want.values()): break
    left = [n for n, v in want.items() if not v]
    if left:
        log('  %d BAO de datos no aparecen en claro: busqueda profunda en paquetes LZO (puede tardar)' % len(left))
        order = sorted(forges, key=lambda p: -hits.get(p, 0))
        for fp in order:
            if not left: break
            _deep_scan(fp, left, want, log)
            left = [n for n in left if not want[n]]
    return want


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
    import base64
    n0 = len(hdr2data)
    for ln in gzip.decompress(base64.b64decode(''.join(_EMB_OGG))).decode().splitlines():
        h, _c, d = ln.partition(',')
        if h and d: hdr2data.setdefault(h, d)
    if len(hdr2data) > n0: log('Tabla Ogg incrustada: %d audios adicionales (spanish_map.csv/plantilla tienen prioridad)' % (len(hdr2data) - n0))
    return hdr2data


# =====================================================================
#  Modo "agregar al final y repuntar" (integrado de forge_append_test.py)
#  Los chunks modificados del paquete .compressed se guardan SIN comprimir (size == zsize), el paquete crece,
#  y la entrada completa del forge (FILEDATA + payload) se copia al final del archivo repuntando el indice.
#  Calidad completa (sin hueco LZO que respetar). El rate / canales / muestras se toman SIEMPRE del Ogg original
#  del hueco (48000, 44100, 16000... el que tenga cada audio) y el WAV se adapta a ellos automaticamente.
# =====================================================================
AP_FD = 440          # cabecera FILEDATA
AP_ALIGN = 2048      # los datos de cada entrada empiezan en multiplos de 2048


def ap_load_entries(buf):
    """Entradas del forge con la posicion de sus 3 campos de tamano."""
    if buf[:9] != b'scimitar\x00': raise ValueError('no es un forge scimitar')
    ver, info_off = struct.unpack_from('<II', buf, 9)
    p = info_off + 12 + 4 + 8
    _fm, _cc = struct.unpack_from('<II', buf, p); p += 8
    cn = struct.unpack_from('<q', buf, p)[0]; ents = []; guard = 0
    while cn > 0 and guard < 64:
        guard += 1
        files, _u, start, nxt, _mn, _mx, name_off, _do = struct.unpack_from('<IIqqIIqq', buf, cn)
        for i in range(files):
            rec, nrec = start + 16 * i, name_off + 188 * i
            lo, hi, fid, size = struct.unpack_from('<IIII', buf, rec)
            name = bytes(buf[nrec + 44:nrec + 44 + 128]).split(b'\0')[0].decode('latin1')
            ents.append(dict(name=name, off=lo | (hi << 32), hi=hi, id=fid, size=size, rec=rec, nrec=nrec,
                             ds=(lo | (hi << 32)) + AP_FD))
        cn = nxt
    return ents


def ap_rebuild_pack(buf, pk, edits):
    """Paquete .compressed nuevo: los chunks tocados se guardan SIN comprimir; los demas, byte a byte iguales."""
    n = len(pk.chunks); plain = [None] * n
    for voff, data in edits:
        end = voff + len(data)
        for ci, (cp, dp, sz, zs, vs) in enumerate(pk.chunks):
            if vs + sz <= voff or vs >= end: continue
            if plain[ci] is None: plain[ci] = bytearray(pk._chunk_plain(ci))
            a, b = max(voff, vs), min(end, vs + sz)
            plain[ci][a - vs:b - vs] = data[a - voff:b - voff]
    ver, ztype, maxs, maxz, _n = struct.unpack_from('<HBHHH', buf, pk.sig + 8)
    tbl, body, newmaxz = b'', b'', maxz
    for ci, (cp, dp, sz, zs, vs) in enumerate(pk.chunks):
        if plain[ci] is None:
            data, crc, z = bytes(buf[dp:dp + zs]), bytes(buf[cp:cp + 4]), zs
        else:
            data = bytes(plain[ci]); z = sz; crc = struct.pack('<I', _adler0(data))
        tbl += struct.pack('<HH', sz, z); body += crc + data; newmaxz = max(newmaxz, z)
    return bytes(buf[pk.sig:pk.sig + 8]) + struct.pack('<HBHHH', ver, ztype, maxs, newmaxz, n) + tbl + body


def ap_append_entry(fh, buf, ent, new_payload):
    """Copia la entrada al final de `fh` con el payload nuevo y repunta indice, registro de nombre y FILEDATA."""
    fh.seek(0, 2); end = fh.tell()
    new_off = (end + AP_ALIGN - 1) // AP_ALIGN * AP_ALIGN
    if new_off >> 32: raise ValueError('el forge supera 4 GB: el indice no puede apuntar mas alla')
    fd = bytearray(buf[ent['off']:ent['off'] + AP_FD])
    if fd[:8] != b'FILEDATA': raise ValueError('FILEDATA no encontrado en %s' % ent['name'])
    if struct.unpack_from('<I', fd, 395)[0] != ent['size']: raise ValueError('tamano en FILEDATA@395 no coincide en %s' % ent['name'])
    nsz = len(new_payload)
    fd[395:399] = struct.pack('<I', nsz)
    blob = bytes(fd) + new_payload
    blob += b'\x00' * ((-len(blob)) % AP_ALIGN)
    fh.seek(end); fh.write(b'\x00' * (new_off - end)); fh.write(blob)
    fh.seek(ent['rec']); fh.write(struct.pack('<IIII', new_off & 0xFFFFFFFF, new_off >> 32, ent['id'], nsz))
    fh.seek(ent['nrec']); fh.write(struct.pack('<I', nsz))
    fh.flush()
    return new_off, nsz


def ap_verify(dst, src, packs, log):
    """Relee el forge nuevo y comprueba indice, registro de nombre, FILEDATA, paquetes y audios. packs: {sig: [(voff, data)]}.
    Devuelve la lista de problemas (vacia = todo OK). Un CRC de chunk sin tocar que ya era invalido en el original
    no cuenta como problema (se deja igual y solo se avisa)."""
    probs = []
    def fail(m): probs.append(m); log('  !! ' + m)
    with open(dst, 'rb') as f, open(src, 'rb') as g:
        nb = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ); ob = mmap.mmap(g.fileno(), 0, access=mmap.ACCESS_READ)
        try:
            ne, oe = ap_load_entries(nb), ap_load_entries(ob)
            if len(ne) != len(oe):
                fail('distinto numero de entradas (%d nuevo, %d original)' % (len(ne), len(oe))); return probs
            for a, b in zip(ne, oe):
                if a['off'] != b['off']:
                    if not (struct.unpack_from('<I', nb, a['nrec'])[0] == a['size'] and struct.unpack_from('<I', nb, a['off'] + 395)[0] == a['size']
                            and nb[a['off']:a['off'] + 8] == b'FILEDATA' and a['off'] % AP_ALIGN == 0):
                        fail('campos de tamano incoherentes en %s' % a['name'])
                elif a['size'] != b['size'] or a['id'] != b['id']:
                    fail('entrada cambiada sin querer: %s' % a['name'])
            for a, b in zip(ne, oe):      # las entradas no movidas son identicas (muestreo de cabecera y cola)
                if a['off'] == b['off'] and a['size']:
                    # la ventana se recorta al tamano REAL de la entrada: antes se leian 4096 B aunque la entrada fuera
                    # mas chica, y en la ultima entrada del forge eso pasaba del final del archivo original (que al
                    # agregar al final ya habia crecido en el nuevo) -> falso 'alterados' (SolomonTemple, Arsuf)
                    n = b['size']; hw = min(n, 4096)
                    if (nb[a['ds']:a['ds'] + hw] != ob[b['ds']:b['ds'] + hw]
                            or nb[a['ds'] + n - hw:a['ds'] + n] != ob[b['ds'] + n - hw:b['ds'] + n]):
                        fail('datos de %s alterados' % a['name'])
            for sig, edits in packs.items():      # cada audio nuevo se lee igual desde el forge nuevo
                old_ent = [x for x in oe if x['ds'] <= sig < x['ds'] + x['size']][0]
                new_ent = ne[next(i for i, x in enumerate(oe) if x is old_ent)]      # misma posicion en la tabla (los nombres se repiten)
                found = False; p0 = new_ent['ds']; pk = None
                while not found:
                    pos = nb.find(COMP_SIG_OGG, p0, new_ent['ds'] + new_ent['size'])
                    if pos < 0: break
                    try: pk = OggPack(nb, pos)
                    except Exception: p0 = pos + 8; continue
                    try: found = all(pk.read(voff, len(data)) == data for voff, data in edits)
                    except Exception: found = False
                    if not found: p0 = max(pk.end, pos + 8)
                if not found:
                    fail('audio distinto o paquete no encontrado tras escribir (entrada %s, paquete @%d, %d audios)' % (old_ent['name'], sig, len(edits)))
                    continue
                try: old_pk = OggPack(ob, sig)
                except Exception: old_pk = None
                for ci, (cp, dp, sz, zs, vs) in enumerate(pk.chunks):
                    if struct.unpack_from('<I', nb, cp)[0] == _adler0(bytes(nb[dp:dp + zs])): continue
                    pre = False                # chunk sin tocar cuyo CRC ya era invalido en el forge original
                    if old_pk is not None and ci < len(old_pk.chunks):
                        ocp, odp, _sz, ozs, _vs = old_pk.chunks[ci]
                        pre = (nb[cp:dp + zs] == ob[ocp:odp + ozs]
                               and struct.unpack_from('<I', ob, ocp)[0] != _adler0(bytes(ob[odp:odp + ozs])))
                    if pre: log('  (aviso) chunk %d del paquete @%d: el CRC ya era invalido en el original; se deja igual' % (ci, sig))
                    else: fail('CRC malo en chunk %d (paquete @%d)' % (ci, sig))
            pk = old_pk = None
        finally:
            nb.close(); ob.close()
    log('  verificacion %s: %s' % (_bn(dst), 'TODO OK' if not probs else '%d problemas' % len(probs)))
    return probs


def _wav_fmt(path):
    """(rate, canales) del WAV de entrada o None si no se puede leer con el modulo wave."""
    try:
        with wave.open(path) as w: return w.getframerate(), w.getnchannels()
    except Exception:
        return None


def _ogg_append_jobs(ogg_jobs, forge_dir, langs, dest_dir, backup, dry_run, log, progress, report):
    """Inyecta los WAV Ogg con el metodo 'agregar al final'. dest_dir: copias modificadas alli (originales intactos);
    vacio/None: se modifica el forge en su sitio (se escribe un temporal, se verifica y se sustituye; .bak del original)."""
    lname_of = {v: k for k, v in OGG_LANGS.items()}
    idx = ogg_index_forges(forge_dir, {j[2] for j in ogg_jobs}, log)
    opened = {}
    def getbuf(fp):
        if fp not in opened:
            f = open(fp, 'rb'); opened[fp] = (f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ))
        return opened[fp][1]
    groups = collections.OrderedDict()            # forge -> {sig: [(voff, nuevo)]}
    rows = collections.defaultdict(list)          # forge -> filas del informe (para marcar error si falla la verificacion)
    seen, ok = set(), 0
    try:
        for n, (wp, hdr, dn) in enumerate(ogg_jobs, 1):
            fname = os.path.basename(wp)
            if progress: progress(n, len(ogg_jobs))
            locs = idx.get(dn) or []
            if not locs:
                report.append([fname, hdr, dn, '', '', '', 'ERROR: BAO de datos no encontrado en ningun forge'])
                log('  %s: no encontrado %s' % (fname, dn)); continue
            got = None
            for fp, t in locs:
                try: g = ogg_variants_at(getbuf(fp), t, dn)
                except (ValueError, OSError): g = None
                if g: got = (fp, g); break
            if not got:
                report.append([fname, hdr, dn, '', '', '', 'ERROR: no se pudo leer el paquete (chunk LZO?)']); continue
            fp, (pk, vs) = got
            wfmt = _wav_fmt(wp)
            for lg in langs:
                lname = lname_of.get(lg, str(lg))
                try:
                    if lg not in vs: raise ValueError('el BAO no tiene la variante %d (%s)' % (lg, lname))
                    voff, size = vs[lg]
                    if (fp, pk.sig, voff) in seen: continue
                    seen.add((fp, pk.sig, voff))
                    old = pk.read(voff, size)
                    new, info = encode_ogg_slot(wp, old)          # rate/canales/muestras del Ogg original, calidad maxima
                    nch, nrate = ogg_stream_info(new[HEADER_SKIP:])[:2]
                    if (nch, nrate) != (info['ch'], info['rate']) or len(new) != size:
                        raise ValueError('rate/canales/tamano distintos tras encodear (bug)')
                    msg = 'OK%s [%d Hz, %d can.]' % (' (simulado)' if dry_run else '', info['rate'], info['ch'])
                    if wfmt and wfmt[0] != info['rate']: msg += ' | WAV %d Hz -> %d Hz' % (wfmt[0], info['rate'])
                    if wfmt and wfmt[1] != info['ch']: msg += ' | WAV %d can. -> %d' % (wfmt[1], info['ch'])
                    if info['cut']: msg += ' (RECORTADO: WAV %.2fs, hueco %.2fs)' % (info['dur_in'], info['dur_slot'])
                    row = [fname, hdr, dn, lname, _bn(fp), info['q'], msg]
                    report.append(row); rows[fp].append(row); ok += 1
                    groups.setdefault(fp, collections.OrderedDict()).setdefault(pk.sig, []).append((voff, new))
                except Exception as ex:
                    report.append([fname, hdr, dn, lname, _bn(fp), '', 'ERROR: %s' % ex])
                    log('  %s [%s]: %s' % (fname, lname, ex))
    finally:
        for f, m in opened.values():
            try: m.close()
            except Exception: pass
            f.close()
    if dry_run or not groups: return ok
    inplace = not dest_dir
    if not inplace: os.makedirs(dest_dir, exist_ok=True)
    for fp, packs in groups.items():
        dst = fp + '.append_tmp' if inplace else os.path.join(dest_dir, _bn(fp))
        try:
            log('Copiando %s -> %s (puede tardar)' % (_bn(fp), _bn(dst) if inplace else dst))
            shutil.copyfile(fp, dst)
            with open(fp, 'rb') as sf:
                sbuf = mmap.mmap(sf.fileno(), 0, access=mmap.ACCESS_READ)
                try:
                    ents = ap_load_entries(sbuf); by_entry = collections.defaultdict(list)
                    for sig, edits in packs.items():
                        e = [x for x in ents if x['ds'] <= sig < x['ds'] + x['size']]
                        if not e: raise ValueError('el paquete @%d no pertenece a ninguna entrada' % sig)
                        by_entry[next(i for i, x in enumerate(ents) if x is e[0])].append((sig, edits))      # clave = posicion, no nombre
                    with open(dst, 'r+b') as fh:
                        for ei, plist in by_entry.items():
                            ent = ents[ei]; name = ent['name']
                            payload = bytearray(sbuf[ent['ds']:ent['ds'] + ent['size']])
                            for sig, edits in sorted(plist, key=lambda x: -x[0]):
                                pk = OggPack(sbuf, sig)
                                newpack = ap_rebuild_pack(sbuf, pk, edits)
                                payload[sig - ent['ds']:pk.end - ent['ds']] = newpack
                                log('  paquete @%d: %d -> %d bytes (%d audios)' % (sig, pk.end - sig, len(newpack), len(edits)))
                                pk = None
                            off, nsz = ap_append_entry(fh, sbuf, ent, bytes(payload))
                            log('  entrada %s: %d -> %d bytes, nueva posicion %d' % (name, ent['size'], nsz, off))
                finally:
                    sbuf.close()
            bad = ap_verify(dst, fp, packs, log)
            if bad: raise ValueError('la verificacion encontro %d problema(s): %s; no se usa este forge' % (len(bad), ' | '.join(bad[:3])))
            if inplace:
                bak = fp + '.bak'
                if backup and not os.path.exists(bak):
                    log('Copia de seguridad: %s.bak' % _bn(fp)); os.replace(fp, bak)
                    try: os.replace(dst, fp)
                    except Exception:
                        os.replace(bak, fp); raise
                else:
                    os.replace(dst, fp)
                log('Forge actualizado: %s' % _bn(fp))
        except Exception as ex:
            log('ERROR en %s: %s' % (_bn(fp), ex))
            for r in rows[fp]: r[-1] = 'ERROR: %s' % ex
            ok -= len(rows[fp])
            try:
                if os.path.exists(dst) and (inplace or os.path.abspath(dst) != os.path.abspath(fp)): os.remove(dst)
            except OSError: pass
    if not inplace: log('Forges modificados en: %s (el original no se toco; copia el que quieras probar sobre el original)' % dest_dir)
    return ok


def collect_wavs(path):
    """Un WAV, o todos los .wav de una carpeta y sus subcarpetas (estructura Audio/<categoria>/<BAO>/..., o cualquier subcarpeta)."""
    if os.path.isfile(path): return [path]
    out = []
    for r, ds, fs in os.walk(path):
        ds.sort(); out += [os.path.join(r, f) for f in sorted(fs) if f.lower().endswith('.wav')]
    return out


def import_wavs_auto(files, forge_dir, out_dir, langs=(3,), stream_forge_fn=None, backup=True, dry_run=False,
                     log=print, progress=None, plantilla=None, modo='hueco', dest_dir=None):
    """Importa WAV de una carpeta (nombres = los de la carpeta wav). Ogg -> forges (por idioma); IMA -> forge de voces.
    modo='hueco'  : escribe en el mismo hueco (mismo tamano; los chunks LZO se recomprimen al tamano original).
    modo='append' : agrega al final del forge y repunta (calidad completa). dest_dir: carpeta para copias modificadas
                    (originales intactos); vacio = en su sitio, con .bak. El rate de cada audio es el del Ogg original."""
    hdr2data = _load_ogg_names(out_dir, plantilla, log)
    ogg_jobs, ima_files, report = [], [], []
    done_slots = set()
    try: files = sorted(files, key=lambda q: -os.path.getmtime(q))   # si un audio esta repetido, gana el WAV mas reciente (el editado)
    except OSError: pass
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
    if ogg_jobs and modo == 'append':
        ok += _ogg_append_jobs(ogg_jobs, forge_dir, langs, dest_dir, backup, dry_run, log, progress, report)
        ogg_jobs = []
    if ogg_jobs:
        idx = ogg_index_forges(forge_dir, {j[2] for j in ogg_jobs}, log)
        by_forge = collections.defaultdict(list)
        for wp, hdr, dn in ogg_jobs:
            if not idx.get(dn):
                report.append([os.path.basename(wp), hdr, dn, '', '', '', 'ERROR: BAO de datos no encontrado en chunks sin comprimir de ningun forge'])
                log('  %s: no encontrado %s' % (os.path.basename(wp), dn)); continue
            for fp, t in idx[dn]: by_forge[fp].append((wp, hdr, dn, t))
        total = sum(len(v) for v in by_forge.values()); done = 0
        for fp, tasks in sorted(by_forge.items()):
            if backup and not dry_run and not os.path.exists(fp + '.bak'):
                log('Copia de seguridad: %s.bak (puede tardar)' % _bn(fp)); shutil.copyfile(fp, fp + '.bak')
            fh = open(fp, 'rb' if dry_run else 'r+b')
            try:
                with mmap.mmap(fh.fileno(), 0, access=mmap.ACCESS_READ) as buf:
                    for wp, hdr, dn, t in tasks:
                        fname = os.path.basename(wp)
                        got = ogg_variants_at(buf, t, dn)
                        if not got:
                            report.append([fname, hdr, dn, '', _bn(fp), '', 'ERROR: no se pudo leer el paquete (chunk LZO?)'])
                        else:
                            pk, vs = got
                            for lg in langs:
                                lname = {v: k for k, v in OGG_LANGS.items()}.get(lg, str(lg))
                                try:
                                    if lg not in vs: raise ValueError('el BAO no tiene la variante %d (%s)' % (lg, lname))
                                    voff, size = vs[lg]
                                    key = (fp, pk.sig, voff)
                                    if key in done_slots: continue
                                    done_slots.add(key)
                                    old = pk.read(voff, size)
                                    new, info = encode_ogg_slot(wp, old)
                                    ops = None; budget = size; layout = 0
                                    for attempt in range(16):
                                        try:
                                            ops = pk.prepare(voff, new); break
                                        except LZOOverflow as ov:
                                            if ov.over > 24 or attempt >= 9: budget -= ov.over + 12
                                            else: layout = (layout + 1) % 3
                                            if budget < 64: break
                                            new, info = encode_ogg_slot(wp, old, audio_budget=budget, layout=layout)
                                    if ops is None: raise ValueError('el chunk LZO recomprimido no cabe en su hueco original (ni bajando la calidad)')
                                    if len(new) != size: raise ValueError('tamano distinto (bug)')
                                    modes = [o[4] for o in ops if o[4] != 'directo']
                                    if not dry_run: pk.commit(fh, ops)
                                    msg = 'OK' + (' (simulado)' if dry_run else '')
                                    if modes: msg += ' [LZO %s%s]' % (','.join(sorted(set(modes))), ', calidad reducida' if budget < size else '')
                                    if info['cut']: msg += ' (RECORTADO: WAV %.2fs, hueco %.2fs)' % (info['dur_in'], info['dur_slot'])
                                    report.append([fname, hdr, dn, lname, _bn(fp), info['q'], msg]); ok += 1
                                except Exception as ex:
                                    report.append([fname, hdr, dn, lname, _bn(fp), '', 'ERROR: %s' % ex])
                                    log('  %s [%s]: %s' % (fname, lname, ex))
                        done += 1
                        if progress: progress(done, total)
            finally:
                fh.flush(); fh.close()
    if ima_files and modo == 'append' and dest_dir:
        for wp in ima_files: report.append([os.path.basename(wp), '', '', '', '', '', 'OMITIDO: con carpeta de destino solo se procesan los Ogg (el forge de voces IMA no se toca)'])
        ima_files = []
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
    p.add_argument('--ratefix', default='16000:11025', help='regla fija 16000:11025 (solo para pruebas)')
    p = sub.add_parser('wav', help='exportar WAV espanol (necesita haber hecho fast)')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('--data', default=None)
    p.add_argument('--vgm', default=''); p.add_argument('--ratefix', default='16000:11025')
    p = sub.add_parser('import', help='importar WAV editados (carpeta o archivos)')
    p.add_argument('forges'); p.add_argument('out'); p.add_argument('wavs', nargs='+')
    p.add_argument('--data', default=None); p.add_argument('--no-backup', action='store_true')
    p.add_argument('--dry-run', action='store_true')
    p.add_argument('--lang', default='esp', help='idioma destino: esp, eng o esp,eng (variantes Ogg)')
    p.add_argument('--plantilla', default=None, help='_plantilla.csv (opcional; por defecto spanish_map.csv / out/spanish/ogg/_plantilla.csv)')
    p.add_argument('--modo', choices=('hueco', 'append'), default='append', help='append = agregar al final y repuntar (calidad completa); hueco = mismo tamano')
    p.add_argument('--destino', default=None, help='(append) carpeta para las copias modificadas; vacio = modifica el forge en su sitio (con .bak)')
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
            files += collect_wavs(w)
        langs = [OGG_LANGS.get(x.strip().lower(), int(x) if x.strip().isdigit() else None) for x in a.lang.split(',') if x.strip()]
        if not langs or None in langs: raise SystemExit('--lang invalido (esp, eng)')
        import_wavs_auto(files, a.forges, a.out, langs, lambda: locate_stream_forge(a.forges, load_plan(a.data, a.out)),
                         not a.no_backup, a.dry_run, plantilla=a.plantilla, modo=a.modo, dest_dir=a.destino)


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
         (('forges', ''), ('out', ''), ('data', ''), ('vgm', 'vgmstream-cli'), ('wavdir', ''), ('ratefix', '16000:11025'), ('labels', '1=eng,3=esp'), ('plantilla', ''), ('modo', 'append'), ('destino', ''))}
    V['backup'] = ctk.BooleanVar(value=cfg.get('backup', True))
    V['dry'] = ctk.BooleanVar(value=False)
    V['lang_esp'] = ctk.BooleanVar(value=cfg.get('lang_esp', True))
    V['lang_eng'] = ctk.BooleanVar(value=cfg.get('lang_eng', False))
    V['variants'] = ctk.BooleanVar(value=True)      # v2.5: por defecto guarda todos los idiomas (esp, eng, L2, L4...)
    V['vwav'] = ctk.BooleanVar(value=True)          # y sus WAV (necesita ffmpeg)

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
        build_map(V['out'].get(), plan, sf, log, rate_fix=dict(RATE_FIX))
        log('Listo. Siguiente: pestaña 2 (WAV).')

    def do_wav_vgm():
        need('out', 'vgm')
        export_wavs_vgm(V['out'].get(), V['vgm'].get(), rate_fix=dict(RATE_FIX), log=log, progress=prog)

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
        files = collect_wavs(d)
        import_wavs_auto(files, V['forges'].get(), V['out'].get(), langs,
                         lambda: locate_stream_forge(V['forges'].get(), get_plan()), V['backup'].get(), V['dry'].get(),
                         log, prog, V['plantilla'].get().strip() or None,
                         modo=V['modo'].get(), dest_dir=V['destino'].get().strip() or None)

    def do_restore():
        need('forges')
        restore_all_backups(V['forges'].get(), log)

    def do_check():
        need('forges', 'out')
        sf = locate_stream_forge(V['forges'].get(), get_plan())
        vgm_crosscheck(V['vgm'].get(), V['out'].get(), sf, 5, log)

    def do_organize():
        need('out')
        organize_audio(os.path.join(V['out'].get(), 'spanish'), log)

    def do_full():
        need('forges', 'out')
        langs, stats = extract_all(V['forges'].get(), V['out'].get(), log, prog)
        log('Extraccion completa: %s' % stats)

    field(t1, 0, 'Carpeta de los .forge del juego', V['forges'], 'dir')
    field(t1, 2, 'Carpeta de salida (aquí se guarda todo)', V['out'], 'dir')
    field(t1, 4, 'Carpeta con los CSV (data.zip descomprimido) - opcional si ac1_spanish_plan.json.gz está junto al script', V['data'], 'dir')
    ctk.CTkCheckBox(t1, text='Guardar todas las variantes de idioma en una carpeta por BAO', variable=V['variants']).grid(row=8, column=0, sticky='w', padx=10, pady=(10, 0))
    field(t1, 9, 'Etiquetas de idioma por índice (ej. 1=eng,3=esp,2=fra)', V['labels'], 'text')
    ctk.CTkCheckBox(t1, text='Decodificar las variantes Ogg a WAV (necesita ffmpeg)', variable=V['vwav']).grid(row=11, column=0, sticky='w', padx=10, pady=(6, 0))
    action(t1, 12, 'Extraer español rápido (solo las entradas necesarias)', do_fast,
           'Descomprime solo las entradas del plan en vez de los 18 forges y arma spanish_map.csv (stream ↔ header ↔ rate).')
    field(t2, 0, 'vgmstream-cli', V['vgm'], 'file')
    action(t2, 2, 'Exportar WAV con vgmstream (completo: header + prefetch + stream)', do_wav_vgm,
           'Recomendado: igual que tu batch original, pero con la variante de idioma correcta. Salida: <salida>/spanish/Audio/<OST (48000) | Historia (24000) | NPC (11025) | Extras>/<BAO>/<archivo>.wav')
    action(t2, 4, 'Exportar rápido sin vgmstream (IMA sin prefetch + Ogg en memoria)', do_wav,
           'IMA -> Spanish_BAO_0x<id>.wav en <salida>/spanish/Audio/<OST|Historia|NPC|Extras>/<BAO>/. Los audios en memoria son Ogg Vorbis: se guardan como .ogg en <Forge>/OGG/<BAO>/ (y su WAV en Audio/... si hay ffmpeg).')
    field(t3, 0, 'Carpeta con los WAV editados (mismos nombres que la carpeta wav: BAO_0x<header>.wav, esp_0x........wav, Spanish_BAO_0x........)', V['wavdir'], 'dir')
    field(t3, 2, '_plantilla.csv (opcional: se usa spanish_map.csv / spanish/ogg/_plantilla.csv si existen)', V['plantilla'], 'file')
    ctk.CTkLabel(t3, text='Idioma donde inyectar (puedes marcar los dos):', anchor='w').grid(row=4, column=0, sticky='w', padx=10, pady=(10, 0))
    ctk.CTkCheckBox(t3, text='Español (variante 3)', variable=V['lang_esp']).grid(row=5, column=0, sticky='w', padx=10, pady=2)
    ctk.CTkCheckBox(t3, text='Inglés (variante 1)', variable=V['lang_eng']).grid(row=6, column=0, sticky='w', padx=10, pady=2)
    ctk.CTkCheckBox(t3, text='Crear copia de seguridad .bak de cada forge que se modifique (primera vez)', variable=V['backup']).grid(row=7, column=0, sticky='w', padx=10, pady=(10, 0))
    ctk.CTkCheckBox(t3, text='Solo simular (no escribe nada)', variable=V['dry']).grid(row=8, column=0, sticky='w', padx=10, pady=4)
    ctk.CTkLabel(t3, text='Método de inyección (Ogg):', anchor='w').grid(row=9, column=0, sticky='w', padx=10, pady=(10, 0))
    ctk.CTkRadioButton(t3, text='Agregar al final y repuntar (recomendado: calidad completa, sin recortes)', variable=V['modo'], value='append').grid(row=10, column=0, sticky='w', padx=10, pady=2)
    ctk.CTkRadioButton(t3, text='Mismo hueco (tamaño idéntico; los chunks LZO se recomprimen)', variable=V['modo'], value='hueco').grid(row=11, column=0, sticky='w', padx=10, pady=2)
    field(t3, 12, 'Carpeta de destino de las copias (solo "agregar al final"; vacío = modifica los forges en su sitio, con .bak)', V['destino'], 'dir')
    action(t3, 14, 'Encodear e importar al forge', do_import,
           'Ogg: encodea a Vorbis con el rate (48000, 44100...), canales y muestras del Ogg original de cada audio, sea cual sea el rate del WAV (se remuestrea solo). "Agregar al final": el forge crece y se repunta el índice; "Mismo hueco": no cambia de tamaño. IMA: igual que antes (solo español).')
    action(t3, 16, 'Restaurar forges desde .bak', do_restore)
    field(t4, 0, 'vgmstream-cli (solo para comprobar el decodificador)', V['vgm'], 'file')
    action(t4, 2, 'Comprobar decodificador vs vgmstream', do_check,
           'Compara 5 streams: si coinciden ~100% el encoder genera lo que el juego espera.')
    action(t4, 4, 'Escaneo completo antiguo (todos los forges)', do_full)
    action(t4, 6, 'Reordenar WAV ya extraídos en Audio/OST|Historia|NPC|Extras', do_organize,
           'Mueve lo que haya en <salida>/spanish/<Forge>/WAV/<BAO>/ a spanish/Audio/<categoría>/<BAO>/ según su frecuencia (48000 OST, 24000 Historia, 11025 NPC, resto Extras). Se puede repetir.')
    app.protocol('WM_DELETE_WINDOW', lambda: (save_cfg(), app.destroy()))
    app.mainloop()


# =====================================================================
#  Datos incrustados (la herramienta funciona sin archivos auxiliares; si existen junto al script o en la
#  carpeta de salida, esos archivos tienen prioridad).
# =====================================================================
# Plan de extraccion espanol (ac1_spanish_plan.json.gz) en base64
_EMB_PLAN = (
    'H4sICFr/7GoC/2FjMV9zcGFuaXNoX3BsYW4uanNvbgBs3bsOJLu2Zud32XYbxTt5POkFZMhsQ+C1uwHhSFBDQgN6ea1K6+SXcude'
    'Fcn5MzNijsGo2v/vv/6f+3/99//2f/z7v/4t/Kd//e/z3//L/z3/y/3Xv/3rf/0/57//t//+X//1n/71X+88//w3//q3//yv//l/'
    '+l/+tz//I/6Jf/6EP/ef/+2r8CiEPxaChWghWcgWioVqoVnoFoaFaWFZ2BaOBfMI5hHNI5pHNI9oHtE8onlE84jmEc0jmkc0j2ge'
    '0TyieUTziOaRzCOZRzKPZB7JPJJ5JPNI5pHMI5lHMo9kHsk8knkk80jmkc0jm0c2j2we2TyyeWTzyOaRzSObRzaPbB7ZPLJ5ZPPI'
    '5lHMo5hHMY9iHsU8inkU2y+2X+y22G2x22K3xW6L3Va7rXZb7bbabbXbarfNrWw212yu2VyzuWZzzea6zXWb6zbXba7bXLe57le7'
    'u7fdve3m0c2jm0c3j24e3Ty6eQzzGOYxzGOYxzCPYR7DPIZ5DPMY5jHMY5jHMI9hHsM8hnlM85jmMc1jmsc0j2ke0zymeUzzmOYx'
    'zWOaxzSPaR7TPKZ5LPNY5rHMY5nHMo9lHss8lnks81jmscxjmccyj2UeyzyWeWzzOH7K8VOOn3L8lOOnXD/lmvo19Wvq19SvqV9T'
    'v6Z+Tf2a+jX1ax7XPJ69PHt59vLs5dnLs5dnL89enr08e3n28n56cW8fexv/BAvRQrKQLRQL1UKz0C0MC9PCsrAtHAs/3fJNjqJX'
    'FL2i6BVFryh6RdErik1RSopSUhR5osgTRZ4o4UQJJ0o4UcKJEk6UcKKEEyWcGH96cRsknCjhRAknSjhRwokSTpRwooQTJZwo4UQJ'
    'J0o4UcKJEk6UcKKEEyWcKOFECSdKOFHCiRJOlHCihBMlnCjhRAknSjhRfonyS5RfovwS5Zcov0T5Jcovsdic/BLll1hsrtpcdbOr'
    '3Va7rXbb7LbZbbPbZrfNbpt722y/2X6zfZEnijxR5IkiTxR5osgTRZ4o8kSRJ4o8UeSJIk8UeaLIE0WeKPJEkSeKPFHkiSJPFHmi'
    'yBNFnijyxPVTMCBn3OiMG51xozNudMaNzrjRGTc640Zn3OgYGB0Do2NgdAyMTmzxmuk102umzwi/hrz0zwTzRSefwrZwLFwLj8LX'
    'zn0KfuzXzn0KyUK2UCy49OXSl0vffsr2U7afsquFZqFbGBamBZe+Xfp26celH5d+WHqPy8K2cCxcC+xtT8lCtuA6UrXQLHQLwwIR'
    '9hwsRAuuNLvS7EqzK80GlA0oG1D5Y8F1FNdRXEdxHcXEiokVEysmVvw6FL8OxW6L3Ra7rXZb3ZfqvlTzqOZRzaOaR7XbarfVbqvd'
    'VrttLr259ObSm0tvLr27ju46upkO1zFcx3Adw3UM1zG96PSi04tOLzp/Luo2TLfB50v3+dJ9vvTlRb3Rd2/0ff1cwy/uMmQfBd1H'
    'QfdR0H0UdB8F3UdB91HQfRR07+vd+3r/ua8f13Fcx3Edx3Uc1/H8L97Pf+E2PLfhuQ3PbXhsw/jzx0KwEC0kC9lCsVAtNAvdwrKw'
    'LRwL14LdBpceXHpw6cGlB5cevWj0otGLRi8afy5qHnFY4PsxkoklE0smlkwsmVj2++Fzf/jcH9l1ZNfhU334VB8+1YcP8eFDfPgQ'
    'Hz7Ehw/x4ZNw+CQcPgmHT8JRfy5q+z74hg++UW2/2n7zos2LNi/avGjzot297e5td2+7iXUT6ybWTaybWPe73v2ud7/rPtWHT/XR'
    'zaObh8/94VN9+FQfPtXHsLlhc8OVDlc6XOlwpcOVOioMR4XhqDCmK52udLoNThfD6WJIjUNqHFLjWK5juY7lOhxIxnIdx0yPiV3X'
    'cV3HdR3Xbbhe9PkDerb//Njnpzy79SE+fIhPn9nTZ/b0eTt93k6ft/PPsDAtLAvbAgHN4Ep9vE4fr9PH6wx+bPBjA4lNcXb6aJw+'
    'xaZPsSm9zmwe+eeiLkwUncWP9bE2faxNuXLKlbP8fKx5iIDTB9/0wTd98E0ffNMH36ym7pNw+iScEt+U+KbEN5sf2/zYZmLek+fw'
    'j4yfP2LI3san9+Q53WyJb0p809v49J48vSdP78nTe/KU+KZ6cKoHp3pwqgenN/rpXXt6157etad37SlXTnluynNTnpvy3FTtTeFs'
    'CmdTOJvC2Tw/FzXTa6bXTK+ZXjP1CTSvK72u9LrS60p9aE0fWlMnPZ8rfa5UjFw+kpaPpCVGLjFy+YxaPqOWz6jlM2r5jFo+Tlbw'
    'osGLBi8afi5q+9H2o+1H25calwi4RMAlAi4RcGmcl/p4JVeaXGlypRrnpT5ePm+X+nipj5dP5CV5Lslz+cxePrOXz+wlRi6fyMsn'
    '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'
    '4KwdnLWDs3Zw1g7O2sFZOzhrB2ft4Kz9LUM/BfPI5pHNI5tHNo9iHsU8HPGDI35wlPx2W38Ljl/B8ev7MPZvwWEiOEwEh4ngMBEc'
    'JoLDRHCYCMuNcroIThfB6SIsN+rrhdR8ROIjEh+R+IjERyQ+ougRRf8pfH+ljjz3T6G4juI6iusoruOb+A6v3n8Kw4ILK/ZS7OUb'
    '3474dsS3w+v7n4K9VJdeXfo3zx15TrWXVXtZtZdVe1m19ynYfrXbZrfNbpvdNneu2X6z/Wb7zfab7Tfbb7bfbL/ZfrP95u438+g2'
    '1+2lu9LuSr9QtET0z6ewLRwL18Kj8PVI+hSChWghUfhyKJ9CtzAofAHvp+A1htcYP9cwoGFAw/bPT8E8rt1+vSLxt/D82OfHPvfl'
    'uS/PdTzW8T3RfwrBQrSQLGQLxUK10Cx0C9PCsrAtHAvXgu0Huw12G+w22G0YFlx6cOnBpQeXHlx6cOnRnYv2Eu0l2ku0l+jORXcu'
    'unPRnYv2Eu0l2kuyl2QvyV6SvSR7SfaS7CXZS7KX5N4m99a7ZfBuGbzTBe90wTvd9/D9KdhLtpdsL9lesr1ke8n2kn96cW+ze5vd'
    '2+LeFnsp9uKNPnijD97ov98i+BTspdhLsZdiL8Veqr1U97a6t9W9re5ttZdqL9Veqr1Ue6n2Uu2l2Uuzl2YvzV6avTT3trm3zb1t'
    '7m0zj2YezTyaeTTzaObRzKObRzePbh7dPLp5dPPo5tHNo5tHNw8ntu93vj8F8+jm0c2jm8cwj2EewzyGeQzzGObhgBYc0IIDWnBA'
    'Cw5owQHt+0XyT8E8HOG+X8T4W5jmMc1jmsd0HdN1TNcxXcd0Hct1LNexXMdyX5b7styX5b4s92W5L8t9We7LMo9lHss8lnks89jm'
    'sc1jm8c2j20e2zy2eWzz2OaxzWObx3Edx3Uc13Fcx3Edx3Uc13F+1uG+HPfluC8STpBwvt8b/xTcFxno+73xT8E8rnlc87jmcc3j'
    'msc1j2se1zyueVzzuObxzOOZxzOPZx7PPJ55PPN45vHM45mH5BkkzyB5BskzSJ5B8oySZ5Q8oxgZxcgoRkYxMv4ZFqaFZWFbOBau'
    'BZsLNic1xmBzweaCzQWbkzyj5Bklzyh5RskzSp5R8oySZ5Q8o+QZJc8oeUbJM0qeUfKMkmeM5hHNI5pHNA/pNUqvUXqN0muUXqP0'
    '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'
    'Pfmx2Y/NblR2o7LdZjcqu1HZTLMLyy6suLBiHsV1FNdRDKgYUHH3iystLqy6sGq31d2v7lx1YdWFVb+n1ZVWV1rNtJlYc2+bEX6N'
    '571w0vwpBAvZQrFQLTQL3cLPOpaFbeFYuBYehWBzwea+b1uFB9+n4Eq/bznFW07xllO85fxTiCYW/dhoYtF1xJ+Lmkey/eTSk0vP'
    '7m12pdmVZleaXWlxHcVt+BIAn4KfUn4uai/V72m1l+pFq0uv7lw15GrIzeaazTW/Y81umyE3V9pc6c8PuZlHc2+bzXWv0b1G9xrd'
    'PLp5dH+Ew20Ydjvsdtjt8KLT1KepT1Ofpj79wkx7mX7s8mOXH7v8lOWnLPNY5rHMY5n6cqXLlW5Xul3pNqDt0rdL3y59u/Tt0rdb'
    'uf3Sbb9j2+/ptv1t+9v2j+0f2z82d2zu2NyxuWNzx+aOv6hjc8fmjs0dm7s2d23uurfXvb12e23u2ty1uedFn5k+P+WZ6fNjnx/7'
    'jPAZ4TPCZ4SPCINjT3Ds+X4h5FNIFoqFaqFZ6BaGhWlhWdgWaD849gTHnuDY8/3PjX0KNhdszknp+/WXT8HmHIxC+Fn6teDORZuL'
    'NudwFRyugsNVcLj6fk38U3Abor04jwXnse9/f+xvwQHt+98f+xTcqORGpWzBnUvmkczDMfD7HxP7FGwu2VyyuWxz2eayzWWbyzbn'
    'fBqcT4PzaXA+Dc6n3/8g2adgHtk8snlk88jm4RQcnIKDM25wxv3+18U+BRdWXFhxYcWFVRdWXVh1o6ob5fD9/Y+JfQou3Vk7OGsH'
    'Z+3vN7v+Fhy+g7P297/qNRp/4fJTKBaqhWZhWzgWroVH4etr+Sm40q+v5aewKBR7KfZS7KXYS3EdxXUU11F+1mEexTyKeRTz+PoW'
    'fgrBQrSQLJhHNY9qHtU8qr1Ue6n2Uu2l2Uuzl2YvzV6GvQx7GfYy7GW4t8O9He7tcG+HeQzzGOYxzGOaxzSPaR6TPErsFoaFaWFZ'
    '2BaOhWuBXkrKFoqFaqFZcB3JdSTXkVxH/mMhWIgWzDTbS7aXbC/ZXrx/FO8fxftH8f5R/O0Xf/vF337xt1+q66iuo7qO+rMO98Xf'
    'fvG3X/ztF3/7xd9+8bdf/O2X5r4096W5L819aebhk7A082jm0e2l20u3l24v3V66vXR76fbS7aXbS7eXbi/TdUzXMV3HdB3T78f0'
    '+zH9fky/H8t1LNexXMdyHct1LNexXMdyHdu93e7tdm+3e7vtZdvLtpdtL9u93e7tdm83e1v97Vd/+9Xffq0/19gWjoVrgUyrv/3q'
    'b7/626/+9qu//epvv/rbr/72q7/96m+/+tuv/vZrM49mHs08mnl4/6jeP6r3j+r9o3r/qN4/qveP6v2jXvO45nHN45rHNY9rHtc8'
    'rnk883jm8czjmcezl2cvz16evTx7efby7OXRS/vzx0KwEC0kC93CsDAtLAvbwrFwLdhLsJdgL8Fegr2EbKFYqBaaBfMI5hHMI5hH'
    'MI9gHsE8gnnIyE1GbjJyk5Gb83pzXm/O6815vTmvN+f15rzenNdbcm+Te5vc2+TeOvM3Z/7mzN+c+Vsyj2QeyTySecgNTW5ockOT'
    'G5rc0OSGJjc0uaHJDU1uaHJDkxua/qPpP5r+o+k/WjaPbB7ZPLJ5FPMo5lHMo5iHHqbpYZoepulhmhzV5KgmRzU5qulhmh6m6WGa'
    'HqbpUJoOpelQmg6lOY8157HmPNacx5rzWHMea85jzXmsOUs1Z6nmLNWcpZqzVHOWas5SzVmqOUs1Z6nmLNWcpZqzVHOWas5SzVmq'
    'OUs1Z6nmLNWcpZos1mSxJos1WawNexn2Muxl2It+rOnHmn6s6ceafqzpx5p+rI2fXtxb/VjTjzX9WNOPNf1Y0481/ViTb5t82+Tb'
    'Jt+2aR7TPKZ5TPOQkZuM3GTkJiO3ZR7LPJZ5LPOQs5uc3eTsJme3ZR7LPJZ5LPOQs5uc3eTsJmc3GbnJyE1GbvtnHe7Ldl+2+7Ld'
    'l2Mvx16OvRx7Oe7LcV+O+3Lcl2MexzyOeRzzOOZxzOOYxzGPax7XPK55XPO45nHN45rHNQ/5tsm3Tb5t8m2Tb5t82+TbJt82+bbJ'
    't02+bfJte+bxzOOZxzMPGbnJyE1GbjJyk5GbjNxk5CYjdxm5y8hdRu4ycpeRu4zcZeQuI3cZucvIXUbuMnKXkbuM3GXkLiN3GbnL'
    'yF1G7jJyl5G7jNxl5C4jdxm5y8hdRu4yco/mEc0jmkc0Dxm5y8hdRu4ycpdvu3zb5dsu33b5tsu3Xb7t8m2Xb7t82+Xbnn56cV/k'
    '2y7fdvm2y7ddvu3ybZdvu3zb5dsu33b5tsu3Xb7t8m2Xb7t82+XbLt92+bbLt12+7fJtl2+7fNvl2y7fdvm2y7ddvu3ybZdvu3zb'
    '5dsu33b5tsu3Xb7t8m2Xb7t82+XbLt92+bbLt12+7fJtl2+7fNvl2y7fdvm2y7ddvu3ybZdvu3zb5dsu33b5tsu3Xb7t8m2Xb7t8'
    '2+XbLt92+bbLt12+7fJtl2+7fNvl2y7fdvm2y7ddvu3ybZdvu3zb5dsu3/bx04t7K992+bbLt12+7fJtl2+7fNvl2y7fdvm2y7dd'
    'vu3ybZdvu3zb5dsu33b5tsu3Xb7t8m2Xb7t82+XbLt92+bbLt12+7fJtl2+7fNvl2y7fdvm2y7ddvu3ybZdv+/5Zh/si33b5tsu3'
    'Xb7t8m2Xb7t82+XbLt92+bbLt12+7fJtl2+7fNvl2y7fdvm2y7ddvu3ybZdvu3zb5dsu33b5tsu3Xb7t8m2Xb7t82+XbLt92+bbL'
    't12+7fJtl2+7fNvl2y7fdvm2y7ddvu3ybZdvu3zb5dsu33b5tsu3Q74d8u2Qb4d8O+TbId8O+XbIt0O+HfLtkG+HfDvk2yHfDvl2'
    'yLdDvh3y7ZBvh3w75Nsh3w75dsi3Q74d8u2Qb4d8O+TbId8O+XbIt0O+HfLtkG+HfDvk2yHfDvl2yLdDvh3y7ZBvh3w75Nsh3w75'
    'dqSfXtwX+XbIt0O+HfLtkG+HfDvk2yHfDvl2yLdDvh3y7ZBvh3w75Nsh3w75dsi3Q74dsumQTYdsOmTTIVcOuXLIlUOuHL7DOnyH'
    'dfgO6/Ad1iGbDtl0yKZDNh2y6ZBNh2w6ZNMhmw7ZdMimQzYdvgs3fBdu+C7c8F24Id8O+XbIt0O+HfLtkG+HfDvk2yHfDvl2yLdD'
    'vh3y7ZBvh3w75Nsh3w75dsi3Q74d8u2Qb4d8O+Tb0c2jm0c3j24eMvKQkYeMPGTkISMPGXnIyENGHvLtkG+HfDvk2yHfDvl2yLdD'
    'vh3y7ZBvh3w75Nsh3w75dsi3Q74d8u2Qb4d8O+TbId8O+XbIt0O+HfLtkG+HfDvk2+F70sP3pIfvSQ/fkx6+4zx8x3n4jvPwHech'
    '3w75dsi3Q74d8u2Qb4d8O+TbId8O+XbIt0O+HfLtkE2HbDpk0yGbDtl0yKZDNh2y6ZBNh2w6ZNMhmw7ZdMimQzYdsumQTYdsOmTT'
    'IZsO2XTIpkM2HbLpkE2HbDpk0yGbDtl0yKZDNh2y6ZBNh2w6ZNMhmw7ZdMimQzadsumUTadsOmXT+SdbKBaqhWahWxgWpoVlweaE'
    '1SmsTmF1CqtTWJ3C6hRWp7A6hdUprE5hdQp405d8py/5Tl/ynb7kO4XEKSROIXEKiVNInELiFBKnkDiFxCkkTiFxyoRTJpwy4ZQJ'
    'p0w4ZcIpE06ZcMqEUyacMuGUCadMOGXCKRNOmXDKhFMmnDLhlAmnZ57TM8/pmef0zHPKlVOunHLl9LxyypVTrpxy5ZQrp1w55cop'
    'V065csqVU66ccuWUCadMOGXCKRNOmXDKhFMmnDLhlAmnTDhlwikTTplwyoRTJpwy4ZQJp0w4ZcIpE06ZcMqEUyacMuGU56Y8N+W5'
    'Kc9NeW7Kc1Oem/LclOemPDfluSnPTXluynNTnpvy3JTnpmee0zPP6Znn9MxzyoRTJpwy4ZQJp0w4ZcIpE06ZcMqEUyacMuGUCadn'
    'fNMzvukZ3/SMb8pRU46actSUo6bnhNNzwuk54fSccMpiUxabstiUxaYsNmWxKYtNWWzKYlMWm7LYlMWmLDY9J5yeE07PCafnhFMW'
    'm7LYlMWmLDZlsSmLTVlsymJTFpuy2JTFpiw2ZbEpi01ZbMpiUxabstiUxaYsNmWxKYtNWWzKYlMWm7LYlMWmLDZlsSmLTVlsymJT'
    'Fpuy2JTFpiw2ZbEpi01ZbEkFy+On5fHT8vhpefy0PH5aHj8t/xrj8q8xLv8a4/KvMS6PsJZHWMsjrCXhLAlnSThLwlkSzpJwloSz'
    'JJwl4SwJZ0k4S8JZEs6ScJYj/nLEX474yxF/OeIvx/PleL4cz5fj+XI8Xx77LF9JXL6SuHwlcTniL0f8VX56cW8d8Zcj/nLEX474'
    'yxF/OeIvR/zliL88OloeHS2PjpZHR0tMWGLCEhOWmLDEhCUmLDFhiQlLTFhiwhITlpiwxIQlJiwxYYkJS0xYYsISE5aYsMSEJSYs'
    'MWGJCcujo+XR0fLoaHl0tESNJWosUWOJGkvUWKLGEjWWqLFEjSVqLFFjiRpL1FiixhI1lqixRI0laixRY4kaS9RYosYSNZaosUSN'
    'JWosUWOJGkvUWKLGEjWWqLFEjeXx0/L4aXn8tDx+Wh4/LY+flsdPy+On5fHT8vhpefy0PH5aHj8tj5+Wx0/L46clei3Ra4leS/Ra'
    'otcSvZbotUSvJXot0WuJXkv0WqLXEr2W6LVEryV6LdFriV5L9Fqi1xK9lui1RK8lei2PwZbHYEtcWeLKEleWuLLElSWuLHFliStL'
    'XFniyhJXlriyxJUlrixxZYkrS1xZ4soSV5a4ssSVJa4scWWJK0tcWeLKEleWuLLEle3R0fboaHt0tD062h4dbY+OtkdH26Oj7dHR'
    '9uhoe3S0PTravhq5fTVy+2rk9rRpe9q0PW3anjZtT5u2p03b06btadP2tGl72rTlyu1p0/bVyO2rkdtXI7dsumXTLZtu2XTLpls2'
    '3bLplk23bLpl0y2bbtl0y6ZbNt2y6ZZNt2y6ZdMtm27ZdMumWzbdsumWTbdsumXTLZtuT9+2p2/bVzS3x3Hb47jtcdz2OG57HLc9'
    'jtsex22P47bHcdvjuO1x3PY4bnsct2X1LatvWX3L6ltW3x7HbY/jtsdx2+O4Le9veX/L+1ve3/L+lve3vL/l/S3vb3l/y/tb3t/y'
    '/pb3t7y/5f0t7295f8v7W97f8v6W97e8v+X9Le9veX/L+1ve3/L+lve3vL/l/S3vb3l/y/tb3t/y/pb3t7y/5f0t7295f8v7W97f'
    '8v6W97e8v+X9Le9veX/L+1ve3/L+lve3vL/l/S3vb3l/y/tb3t/y/pb3t7y/5f0t7x+fDcdnw/HZcHw2HJ8Nx2fD8dlwfDYcnw3H'
    'Z8PxXni8Fx7vhcd74fFeeLwXHu+Fx3vh8V54vBce74XHe+HxXni8Fx7vhcd74fFeeLwXHu+Fx3vh8V54vBce74XHe+HxXni8Fx7v'
    'hcd74fFeeLwXHu+Fx3vh8V54vBce74XHe+HxXni8Fx7vhcd74fFeeLwXHu+Fx3vh8V54vBce74XHe+HxXni8Fx7vhcd74fFeeLwX'
    'Hu+Fx3vh8V54vBce74XHe+HxXni8Fx7vhcd74fFeeH7uhbrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6'
    'z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6'
    'z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zy6z6P7PLrPo/s8us+j+zz+FYDjXwE4vrpyfHXl+OrK8dWV46srx1dXjq+uHF9d'
    'Ob66cnx15fjqyvHVleOrK8dXV44u+OiCjy746IKPLvjogo8u+OiCjy746IKPLvjogo8u+OiCjy746IKPLvjogo8u+OiCjy746IKP'
    'Lvjogo8u+OiCjy746IKPLvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKv'
    'Lvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKvLvjqgq8u+OqCry746oKv'
    'Lvjqgq+8f+X9K+9fef/K+1fev/L+lfevvH/l/asLvrrgqwu+uuCrC7664KsLvrrgqwu+uuCrC7664KsLvrrgqwu+uuCr/7j6j6v/'
    'uPqPq/+4+o+r/7j6j6v/uPqPq/+4+o+r/7j6j6v/uPqPq/+4+o+r/7j6j6v/uPqPq/+4+o+r/7j6j6v/uPqPq/+4+o+r/7j6j6v/'
    'uPqPq/+4+o+r/7j6jyvvX3n/yvtX3r/y/pX3r7x/5f0r7195/8r7V96/8v6V96+8f+X9K+9fef/K+1fev/L+lfevvH/l/SvvX3n/'
    'yvtX3r/y/pX3r7x/5f0r7195/8r7V96/8v6V96+8f+X9K+9fef/K+1fev/L+lfevvH/l/SvvX3n/yvtX3r/y/pX3r7x/5f0r7195'
    '/8r7V96/8v6V96+8f+X9K+9fef/K+1fev/L+lfevvH/l/SvvX3n/yvtX3r/y/pX3r7x/5f0r7195/8r7V96/8v6V96+8f+X9K+9f'
    'ef/K+1fev/L+lfevvH/l/SvvX3n/yvtX3r/y/pX3r7x/5f0r7195/8r7V96/8v6V96+8f+X9K+9fef/K+1fev/L+lfevvH/l/Svv'
    'P3n/yftP3n/y/pP3n7z/5P0n7z95/8n7T95/8v6T95+8/+T9J+8/ef/J+0/ef/L+k/efvP/k/SfvP3n/yftP3n/y/pP3n7z/5P0n'
    '7z95/8n7T95/8v6T95+8/+T9J+8/ef/J+0/ef/L+k/efvP/k/SfvP3n/yftP3n/y/pP3n7z/5P0n7z95/8n7T95/8v6T95+8/+T9'
    'J+8/ef/J+0/ef/L+k/efvP/k/SfvP3n/yftP3n/y/pP3n7z/5P0n7z95/8n7T95/8v6T95+8/+T9J+8/ef/J+0/ef/L+k/efvP/k'
    '/SfvP3n/yftP3n/y/pP3n7z/5P0n7z95/8n7T95/8v6T95+8/+T9J+8/ef/J+0/ef/L+k/efvP/k/ef7Ds/3HZ7vOzzfd3i+7/B8'
    '3+H5vsPzfYfn+w7P9x2e7zs833d4vu/wfN/h+b7D832Hp/94+o+n/3j6j6f/ePqPp/94+o+n/3j6j6f/ePqPp/94+o+n/3j6j6f/'
    'ePqPp/94+o+n/3j6j6f/ePqPp/94+o+n/3j6j6f/ePqPp/94+o+n/3j6j6f/ePqPp/94+o+n/3j6j6f/ePqPp/94+o+n/3j6j6f/'
    'ePqPp/94+o+n/3j6jyfvP3n/yftP3n/y/pP3n7z/5P0n7z95/8n7T95/8v6T95+8/+T9J+8/ef/J+0/ef/L+k/efvP/k/SfvP3n/'
    'yftP3n/y/pP3n7z/4P3wh7nwn0K2UCxUC81CtzAs/KxjWdgWjoVr4VFgLvynECxEC+ZRzKOYRzGPYh7FPIp5FPMo5lHMo5hHMY9i'
    'HtU8qnlU86jmUc2jmkc1j2oe1TyqeVTzqOZRzaOaRzWPah7NPJp5NPNo5tHMo5lHM49mHs08mnk082jm0cyjmUczj2Ye3Ty6eXTz'
    '6ObRzaObRzePbh7dPLp5dPPo5tHNo5tHN49uHsM8hnkM8xjmMcxjmMcwj2EewzyGeQzzGOYxzGOYxzCPYR7TPKZ5TPOY5jHNY5rH'
    'NI9pHtM8pnlM85jmMc1jmsc0j2keyzyWeSzzWOaxzGOZxzKPZR7LPJZ5LPNY5rHMY5nHMo9lHts8tnls89jmsc1jm8c2j20e2zy2'
    'eWzz2OaxzWObxzaPbR7HPI55HPM45nHM45jHMY9jHsc8jnkc8zjmcczjmMcxj2Me1zyueVzzuOZxzeOaxzWPax7XPK55/MzJ1zyu'
    'eVzzuOZxzeOZxzOPZx7PPJ55PPN45vHM45nHM49nHs88nnk883jmwblYCJyL/VMIFqKFZCFbKBaqhWahWxgWpoVlYVs4Fq4F8wjm'
    'EcwjmEcwj2AewTyCeQTzCOYRzCOYRzCPYB7BPIJ5BPOI5hHNI5pHNI9oHtE8onlE84jmEc0jmkc0j2ge0TyieUTzSOaRzCOZRzKP'
    'ZB7JPJJ5JPNI5pHMI5lHMo9kHsk8knkk88jmkc0jm4f+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPo'
    'P4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPo'
    'P4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPo'
    'P4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPo'
    'P4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C/iPoP4L+I+g/gv4j6D+C7iLoLoLuIugugu4i6C6C7iLoLoLuIugugu4i7J9e3Fvd'
    'RdBdBN1F0F0E3UXQXQTdRdBdBN1F0F0E3UXQXQTdRdBdBN1F0F0E3UXQXQTdRdBdBN1F0F0E3UXQXQTdRdBdBN1F0F0E3UXQXQTd'
    'RdBdBN1F0F0E3UXQXQTdRdBdBN1F0F0E3UXQXQTdRdBdBN1F0F0E3UXQXUTdRdRdRN1F1F1E3UXUXUTdRdRdRN1F1F1E3UXUXUTd'
    'RdRdRN1F1F1E3UXUXUTdRdRdRN1F1F1E3UXUXUTdRdRdRN1F1F1E3UXUXUTdRdRdRN1F1F1E3UXUXUTdRdRdRN1F9n6av++n/Q83'
    'g7+FY+FaeBS+bwZ/C8FCtdAsuLDvH/LfwrSwLNjLs5dnL49e+CH/LQQL0UKykC0UC9VCs9AtDAvTwrKwLRwL14J5BPMI5hHMI5hH'
    'MI9gHsFegr0Eewn2Euwl2Eu0l2gv0V6ivUR7ifYS3dvo3kb3Nrq30TyieUTziOYRzSOaRzKPZB7JPJJ5JPNI5pHMI5lHMo9kHsk8'
    'knkk80jmkcwjmUc2j2we2TyyeWTzyOaRzSObRzaPbB7ZPLJ5ZPPI5lG9RvUa1WvUn2uYaTXTZqbNTJuZNjNtZtrMtJlpM9Nmps1M'
    'm3k082jm0cyjmUczj24e3Ty6eXTz6ObRzaObRzePbh7dPLp5dPPo5tHNo5tHN49hHsM8hnkM8xjmMcxjmMcwj2EewzyGeQzzGOYx'
    'zGOYxzCPaR7TPKZ5TPOY5jHNY5rHNI9pHtM8pnlMe1n2suxl2cuyl2Uvy16WvSx7Wfay7GXZy3Jvl3u73Nvl3i7z2OaxzWObxzaP'
    'bR7bPLZ5bPPY5rHNY5vHNo9tHts8tnkcezn2cuzl2MuxF4EmHns59nLs5djLsZfz04t7e93b695e9/aaxzWPax7XPK55XPO45nHN'
    '45qHTBhlwigTRpkwyoRRJozPPJ55PPN45iFXRrkyypVRroxyZZQro1wZ5cooV0a5MsmVSa5McmWSK5NcmeTKJFcm+SXJL0l+SfHn'
    'Gs1CtzAsTAvLwrZwLFwLZiq/JPklyS9JfknyS5JfkvyS5JckvyT5JckvSX5J8kuSX5L8kuSXJL8k+SXJL0l+SfJLkl+S/JLklyS/'
    'JPklyS9JfknyS5JfUjaPbB7FPIp5FPMo5lHMo5hHMY9iHsU8inkU8yjmUcyjmEcxj2Ie1TyqeVTzqOZRzaOaRzWPah7VPKp5yKZJ'
    'Nk2yaZJNk2yaZNMkVya5MsmVSa5McmWSK5NcmeTKJFcmuTLJlUmuTHJlkiuTXJnkyiRXJrkyyZVJrkxyZZIrk1yZ5MokVya5MsmV'
    'Sa5McmWSK5NcmeTKJFcmuTLJlUmuTHJlkiuTXJnkyiRXJrkyyZVJrkxyZZIrk1yZ5MokVya5MsmVSa5McmWSK5NcmaZ5TPOY5jHN'
    'QzZNsmmSTZNsmmTTJJsm2TTJpkk2TbJpkk2TbJpk0ySbJtk0yaZJNk2yaZJNk2yaZNMkmybZNMmmSTZNsmmSTZNsmmTTJAMlGSjJ'
    'QOn+XMNMZaAkAyUZKMlASQZKMlCSgZIMlGSgJAMlGSjJQEkGSjJQkoGSDJRkoCQDJRkoy0BZBsoyUJaBsgyUZaAsA2XP1rJna9mz'
    'tezZWvZsLXu2lj1by56tZc/Wsmdr2bO17Nla9mwte7aWPVvLwTyCeQTzCObh+Vz2fC57Ppc9n8uez2XP57Lnc9nzuez5XJZvs3yb'
    '5dss32b5Nsu3Wb7N8m2Wb7N8m+XbLN9m+TbLt1m+zfJtlm+zfJvl2yzfZvk2y7dZvs3ybZZvs3yb5dss32b5Nsu3Wb7N8m2Wb7N8'
    'm+XbLN9m+TbLt1m+zfJtlm+zfJvl2yzfZvk2y7dZvs3ybZZvs3yb5dss32b5Nsu3Wb7N8m2Wb7N8m+XbLN9m+TbLt1m+zfJtlm+z'
    'fJvl2yzfZvk2y7dZvs3ybZZvs3yb5dss32b5Nnv2mj17zZ69Zs9es4ycZeQsI2cZOcvIWUbOMnKWkbOMnGXkLCNnGTnLyFlGzjJy'
    'lpGzjJxl5CwjZxk5y8hZRs4ycpaRs4ycZeQsI2cZOcvIWUbOMnKWkbOMnGXkLCNnGTnLyFlGzjJylpGzjJxl5CwjZxk5y8hZRs4y'
    'cpaRs4ycZeQsI2cZOcvIWUbOMnKWkbOMnGXkLCNnGTnLyFlGzjJylpGzjJxl5CwjZxk5y8hZRs4ycpaRs4ycZeQsI2cZOcvIWUbO'
    'MnKWkbOMnGXkLCNnGTnLyFlGzjJylpGz57fZ89vs+W3e5nHM45jHMQ/PgLNnwNkz4OwZcPYM+Oel1uwZcPYMOHsGnD0Dzp4BZ8+A'
    's2fA2TPg7Blw9gw4ewacPQPOngFnz4CzZ8BZ/5H1H1n/kfUfWf+R9R9Z/5H1H1n/kfUfWf+R9R9Z/5H1H1n/kfUfWf+R9R9Z/5H1'
    'H1n/kfUfWf+R9R9F/1H0H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0'
    'H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1H0'
    'H0X/UfQfRf9R9B9F/1H0H0X/UfQfRf9R9B9F/1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0'
    'G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0'
    'G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0'
    'G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0'
    'G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0'
    'G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0'
    'G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G0W7UbQbRbtRtBtFu1G0G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1'
    'G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1'
    'G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1G1W7UbUbVbtRtRtVu1G1G1W7UX27o/p2R9V/VP1H'
    '1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H'
    '1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H'
    '1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H'
    '1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1T9R9V/VP1H1X9U/UfVf1TtRtVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F'
    '1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F'
    '1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F1V1U3UXVXVTdRdVdVN1F'
    '1V003UXTXTRFRFNENEVEU0Q0RURTRDRFRFNENEVE0yo0rULTKjStQtMqNK1C0yo0rULTKjStQtMqNK1CCz/NXQvunFahaRWaVqFp'
    'FZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFp'
    'FZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFp'
    'FZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFp'
    'FZpWoWkVmlahaRWaVqFpFZpWoWkVmlahaRWaVqFpFZpWoWkVmoqgqQiaiqCpCJqKoKkImoqgqQiaiqDJ+03eb/J+k/ebvN/k/Sbv'
    'N3m/yftN3m/yfpP3m7zf5P0m7zd5v8n7Td5v8n6T95u833zfofm+Q9MINN93aL7v0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0'
    'Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0'
    'Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0Bk1n0HQGTWfQdAZNZ9B0'
    'Bk1n0HQGTWfQdAZdZ9B1Bt33HbrvO3Tfd+hqhq5m6GqGrmboaoauZuhqhq5m6GqG7vsO3fcduu87dM1E10x0zUTXTHTNRFczdDVD'
    'VzN0NUNXM3Q1Q1czdDVDVzN0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B'
    '1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B'
    '1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B'
    '1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUHXGXSdQdcZdJ1B1xl0nUH3TYTumwjdNxG6mqGrGbqaoasZupqhqxm6'
    'mqGrGbqaofsmQvdNhO6bCF0z0TUTXTPRNRNdM9HVDF3N0NUMXc3Q1QxdzdDVDF3N0NUMXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1'
    'Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1'
    'Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZ9B1'
    'Bl1n0HUGXWfQdQZdZ9B1Bl1n0HUGXWfQdQZdZzB0BkNnMHQGQ2cwdAZDZzB0BkNnMHQGQ2cwdAZDZzB0BkNnMHQGQ2cwdAZDZzB0'
    'BkNnMHQGQ2cwfJth+DbD8G2GoWYYaoahZhhqhqFmGGqGoWYYaoahZhi+zTB8m2H4NsPQTAzNxNBMDM3E0EwMNcNQMww1w1AzDDXD'
    'UDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXD'
    'UDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXD'
    'UDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXD'
    'UDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcNQMww1w1AzDDXDUDMMNcPwBYjhCxDDFyCGZmJoJoZmYmgmhmZiaCaG'
    'ZmJoJoZmYvgCxPAFiOELEEOZMZQZQzMxNBNDMzE0E0MzMTQTQzMxNBNDMzHUDEPNMNQMQ80w1AxDzTDUDEPNMNQMQ80w1AxDzTD2'
    'T3PunJphqBmGmmGoGYaaYagZhpphqBmGmmGoGYaaYagZhpphqBmGmmGoGYaaYagZhpphqBmGmmGoGYaaYagZhpphqBmGmmGoGYaa'
    'YagZhpphqBmGmmGoGYaaYagZhpphqBmGmmGoGYaaYagZhpphqBnGt2YYf/58G4G/hWAhWkgWsoVioVpoFrqFYeFn6V879/5Z6LLw'
    '818cCt9M+LcQLEQLyUK2UCxUC81Cp1BcR/GixYtWL1q96Pfg/LcwKTSbazbXXEdzHc11NNfRXEf7WYdb2dzK5lZ+D6x/C49Cd7O7'
    'IXc3u5tHN49uHt08unl0FzZc2HBhw4UN1/E1KM4/fMc+hW5hWJgWloVN4csIfArZggv7MgKfgiv9MgIzcpf6FIKFSCFQCF968FO4'
    'FL7E3d9C/GMhWPBTvnTYp1AtNAvdggv7Ull/C8mFJT822UtyHcl1JNfx/f34W1gWzDQbUDag7EqzK80uzK9D+PJBn8K2YGLFxIor'
    'LS7sy+V8Cq6jGFAxoOLCiokVN7u6juo1qteoXqO5juY1mgF1A+oG1N2o7qd0P6W7sO7HDj92+LHDb9AwoOFGDfdl+IUZLn249GHI'
    'w16GvUx7mfYy7WXay7SXaerTH/L09zL9nk7zmOYxzWOaxzSPaR7TPJZ5LPNY5rHMY5nHMo9lHss8lnks81jmscxjmccyj2Ue22ts'
    'r7G9xv65hpkeMz1mesz0mOkx02NAx4COAR2bO/Zy7OXYy7WXay/XXq69XHu5fj+u34/r9+Pa/rX9a/vX9q97e83jmsc1j2cezzye'
    'eTzzeObxzOOZxzOPZx7PPJ55PPN45vHM45FH/JMsZAvVQrPQLQwLy8K2cCy40vDHQrAQLdhcsLn/j7G715lt17YyfC8nRmh2/5sU'
    'LgDphAgh/4wBBBwQGyJunjk/EuqpFaxgJ117fmW/Hqt6a80eZdVnCmcbzjacbTjbWBacfjj9cPrxNX0e3KROTurkpE5O6uSU5JHk'
    'oZJOKumkkk5JHkkeSR5JHkkeyvOUnW12tsrzlJ2tej2p15N6PanXk3o9ZWergE/Z2aro08e28Rq/fn32qD8F/x+fPepPISwkC9lC'
    'sVAtNAvdwrAwLSwL28KxcC3I48rjkccjj0cejzweeTzyeOTxyOORxyOPRx6P03+c/uP0X2f7OtvX2b7MNuJYuBYeC1DHvA/N+9C8'
    'D837n0KxsCxsCw49OfTk0JNDzw49O/Ts0LNDzw49VwvNQrcwLEwL8sjyyPLI8sjy8CsnijyKPIo8ijyKPIo8ijyKPIo8ijyKPIo8'
    'ijyKPIo8ijyqPKo8qjyqPKo8qjyqPKo8qjyqPKo8qjyqPKo8qjyqPJo8mjyaPJo8mjyaPJo8mjyaPJo8mjyaPJo8mjyaPJo8ujy6'
    'PLo8ujy6PLo8ujy6PLo8ujy6PLo8ujy6PLo8ujyGPIY8hjyGPIY8hjyGPIY8hjyGPIY8hjym45j+k/n1T0Q4RThFOEW4RLhEuES4'
    'RLgc+hLhEuES4RLhEuGSx5LHkseSx5LHkseWx5bHlseWx5bHlseWx5bHlseWx5bHlseWx5bHlseWx5HHkceRx5HHkceRx5HHkceR'
    'x5HHkceRx5HHkYceKPRAoQcKPVDogUIPFHqg0AOFHij0QKEHCj1Q6IFCDxR6oNADhR4o9EChBwo9UOiBQg8UeqDQA4UeKPRAoQcK'
    'PVDogcj6hlnfMOsbZn3DrG+Y9Q2zvmHWN8z6hlnfMOsbZn3DrG+Y9Q2zvmHWN0zhhqHbMHQbZmzDSO1PAUBkbMOMbZixDTO2YcY2'
    'zNiGGdswYxtmbMOMbZixDTO2YcY2zNiGGdswYxtmbMOMbZixDTO2YcY2zNiGGdswYxtmbMOMbZixDTO2YcY2DLuGYdcwyhrfuVTS'
    'JCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLS'
    'JCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLSJCZNYtIkJk1i0iQmTWLS'
    'JCZNYtKtJd1a0oslvVjSi6Xhx46vj5X6lPoU8hSyji9N5zKdyxTyFPJ0ttrIpI1M2sikjUzayKSNTNrIpI1M2sikjUzayKSNTNrI'
    'pI1M2sikjUzayKSNTNrIpI1M2sikjUzayKSNTNrIpI1M2sikjUzayKSNTHqPpPdImoCkCUiagKQJSJqApAlImoCkCUiagKQJSMri'
    '9H79P+ShLE7K4qQsTsriHF+FbeFYuBYeCyDMysCsDMzKwKwMzKq+rOrLqr6s6suqvqzqy6q+rOrL7oxkd0ayOyPZnZHszkh2ZyS7'
    'M5LdGcnujGTlaFaOZndGsjsjWcGa1WNZPZbVY1k9ltVjWT2W1WNZPZbVY1k9luvX0F1K9VhWj2X1WFaPZfVYVo9l9VhWj2X1WFaP'
    'ZfVYVn5l5VdWfmXlV1Z+ZeVXVn5l5VdWfmXlV1Z+ZeVX/pRfkxcefgrXwmPhpfD5n9jklYifQrKQLTiwz//EJq9E/BS6hUGh+LHN'
    '/8fnUk7eb/gpbAsSaxJrEmsS6xLrEusOvUvscyn/HIJ/KXwGIn8KYSFZyBb8lM9A5E+hWdgWjoVr4bHgXJJzSc4lOZf8VXBy2cll'
    'J5ed3OdDt3w3YfluwvLdhD+FaWFZEGERYRFhEWERYRVhFWF1LtW5VOdSnUt1HNVxNMfRHEdz5Zor11y55so159KcS3Muzbk016W5'
    'Ls11aa5Lk0eTR/djux/b/ZTup3Q/pfspQ+pDyEPInxuY25dqti/VbF+q2bz691P4+qPVQrPQLQwL08KysC0cC9fCY+GlEPIIeYQj'
    'DUcajjQcaTjScKThSMORJkeaZJocaXKkyZEmR/opJo6LfVzsI+Qj5CPkI9Mj0yPTI9Mj0yPTI9Mj0yPTPwVnm5ztp206LsNxGY7L'
    '8LuQHWl2pNmRfubaR2F0fCnv+FLe8aW8Y+M7Nr5j4zs2vmPjOza+Y+M7Nr5j4zs2vmPjOza+PwV5VHlUeVR5VHlUeVR5VHlUeTTH'
    '0RxHcxzNP9q+/qiQm5C7kLtMh0yHTIdMh3MZzmU4lyHCIcLhbIeTG05uOLnhEzSc7XS209lOZzud7XS209lOn6Dp9Kdzmc5lOpfp'
    'XJZzWc5lOZflOJbLsJ3cdnLbyW3/6P76o67tdnLbyR0nd5zc57mLq6i5ipqrqLkKkqsgudqmq2262qY/Bf9ofP3RaWFZ+Hj4X7vY'
    'axd77WIvxmoHPH4KyUK2UCxUC81CtzAsTAvLwrZwLFwLj4WXQjj0cOjh0MOhh0MPhx4OPRx6OPRw6OHQP9b2p+BSJpcyuZTJpUzy'
    'SPJI8kjySPJI8kjySPJI8qh+SvVTqp9Sv/6GTKtMm0ybTJtMm0ybTJtMm0ybTJuzbc62Odsm0ybTJo8mjyaPLo8ujy6PLo8ujy6P'
    'Lo8ujy6PLo8ujy6PLo8ujy6PLo/h0IdDHw59OPTh0IdDHw59OPTh0IdDHw59upTTpZwu5XQpp0s55THlMeUx5THlMeUx5THlMeUx'
    '5THlseSx5LHksf0n23+yv/6JCLcIjwO7fsr1U66fcv2U66dcF+q6UNeFui7UdaGuC3VdqOtCPQ79ceiPQ38c+uPQH4f+OPTHoT8O'
    '/XHoz9fQfcYen7HHpXxdytelfOXxyuOVxyuPVx6vPF55vPJ44RHKnrDNh20+bPNhmw/bfNjmP1+G+ynA9PNluJ9CWEgWsoVioVpo'
    'FuSR5ZHlkeWR5ZHlkeVRHHpx6MWhF4deHHpx6MWhF4deHaniKhRXobgKxVUorkJxFYqrUFyF4ioUV6G4CsVVKK5CcRWKq1BcheIq'
    'FFehuArFVSiuQnEViqtQXIU6KNRBoQ4KdVCogz5fdvopSF0dFOqgUAeFOijUQaEOCnVQqINifA1d6uqgUAeFOihUF6G6CNVFqC5C'
    'dRGqi8/3o34KUl9SX1JfUl9SX1JfUl9SX1Jf8ljyWPJQOoXSKZROoXQKpdPn+1E/BXlseWx5bHlseWx5bHlseWx5bHkcP+X4KcdP'
    'OX7K8VOUkqGUDKVkKCVDKRlKyVBKhlIylJKhlAylZCglQykZSsnPt45+CvK48njk8chDfRrq01Cfhvo0Xj42/fplISwkC9lCsVAt'
    'NAvdwrAwLSwL28KxwDJ8vnbzU3Dohm7J0C2pPpMJWjJBS/E1jseC62KClkzQkglaMkFLJmjJBC2ZoCUTtKS0TkrrpLROSuuktE5K'
    '66S0TkrrpLROSuuktE5K66S0TkrrpLROSuuktE5K2qSkTeXrn4hQSfv57spPwU+pfoohZDKETPXrU1wolXRSSSeVdFJJJ5V0Ukkn'
    'lXRSSSeVdFJJJ5V0UkknlXRSSSeVdFJJJ5V0UkknlXRSSSeVdFJJJ5V0UkknlXQypkzGlMmYMiudstIpK52y0ikrnbLSKSudstIp'
    'K52y0imrcrIqJ6tysionq3KyKicfh34c+nHox6Efh36qhWbBdTnDwrQgD/VYVo9l9VhWj2X1WFaPZfVYVo9l9VhWj2X1WFaPZfVY'
    'Vo9l9VhWj2X1WFaPZfVYVo9l9VhWj2X1WFaPZfVYVo9l9Vg2L8zmhdm8MJsXZvPCbF6YzQuzeWE2L8zmhdm8MJsXZvPCbF6YzQuz'
    'eWE2L8zmhdm8MJsXZvPC/Mrjlccrj1ceCueihCtKuKKEK0q4ooQrSriihCtKuKKEK0q4ooQrSriihCtKuKKEK3b1YlcvdvViVy92'
    '9WJXL3b1YlcvdvViVy929dK+5nItuLZ29WJXL3b1YlcvdvViVy929WJXL3b14uZjcfOxGLoVQ7di6FYM3YqhW3Hzsbj7Vtx9K+6+'
    'FXffirtvxd234u5bcfetuPtWzMeK+VgxHyvmY8V8rJiPFfOxYj5WzMeK+VgxHyvmY8V8rJiPFUVeUeQVRV5R5BVFXlHkFUVeMcoq'
    'RlnFKKso8ooiryhIioKkKEiKgqQoSIqCpChIioKkKEiKgqQoSMr9movLoCApCpKiICkKkqIgKQqSoiApCpKiICkKkqIgKQqSonYo'
    'aoeidihqh6J2KLb5Ypsvtvlimy+2+WKbL7b5Ypuv5mPVfKyaj1XzsWo+Vs3HqvlYNbmqHherHher4UhVKFWFUlUoVYVSVShVhVJV'
    'KFWFUlUoVYVSVShVhVJVKFWFUlUo1ZCpGjJVQ6ZqyFQNmaohUzVkqoZM1ZCpGjJVQ6ZqyFTdv63u31b3b2tx6MWhu39b3b+t7t9W'
    'I6RqhFSNkKoRUjVCqkZI1QipKjarYrMqNqtisyo2q2KzKjarYrMqNqtisyo2q2KzKjarYrMqNqtisyo2q2KzqgururCqC6u6sKoL'
    '6/BThtTdjK1uxlY3Y6ubsdXN2OpmbHUztroZW8fX0KXuZmx1M7a6GVtVsFUFW1WwVQVbVbBVBVtVsFUFW1WwVQVbVbBVBVtVsFUF'
    'W1WwVQVbVbBVBVtVsFUFW1WwVQVbVbBVBVtVsFUFW1WwVQVbjSmrMWU1pqzu8FZ3eKuyuCqLm8qgqQyayqC5c9Z+ff3RaWFZ2BaO'
    'hWvhsQDkpv5oERaShWxBHm7HNbfjmttxzTPwzTPwzTPwzR285g5ecwevKa6a4qoprpr6o6k/mvqjqT+a+qN5KqtlPyX7KcVPUSo0'
    'pUJTKjSlQlMqNPfFmvtizX2x5r5Yc1+sFRequFBFHkUeRR5VHlUeVR5VHlUe7uA1d/CaO3jNHbzmDl5TfjXlV1N+NeVXU3415VdT'
    'KTWlQlMqNKVCM0JqRkjNCKkNl2G4DOqPpv5o6o+m/mjqj6b+aOqPpv5o6o+m/mjqj6b+aOqPpv5o6o/mYbDmYbDmofhmLNeM5Zp9'
    'v9n32/r6JyK07ze7abObNrtps5s2u2nbX5/iQhkyNUOmZsjU3Els7iQ2dxKbO4nNncTmTmJzJ7G5k9jcSWzuJDZ3Eps7ic2dxOZO'
    'YnMnsbmT2NxJbO4kNncSmzuJzeCuGdw1g7tmcNcM7poZWzNja4ZMzZCpGTI1N6iaG1TNDarmBlVzg6oZMjVDpmbI1A2ZuiFTN2Tq'
    'hkxdKdmVkl0p2ZWSXSnZlZJdKdmVkl0p2ZWSXSnZlZJdKdlNnbqpUzd16mZK3Uypmyl1M6VuptTNlLqarivhuhKuK+G6EVI3QupG'
    'SN0IqRshdSOkboTUlXBdCdeVcF0J15VwvXx9ipCVcF0J15VwXQnXlXBdCdeVcF0J15VwXQnXlXBdCdeVcN3+0u0v3f7S7S/d/tLt'
    'L93+0u0v3f7S7S/d/tLtL93+0u0v3f7S7S/d/tLtL93+0u0v3f7S7S/d/tLtL93+0u0v3Y2h7sZQd2OouzHU3Rjqz1dBQB7V6B7V'
    '6B7V6G63dLdbup2w2wm7nbDbCbudsNsJu52w2wmH38nDnYCRvv7JsDAtLAvbwrFwLTwWQDj8Gh9+jQ+/xodf48Ov8eHX+PBrfPg1'
    'PvwaH36ND3cChjsBwze5hpnBMDMYZgbDzGCYGQwzg2FmMGw4w4YzbDjDhjNsOMOGM2w4w4YzbDjD7YXh9sJwe2G4vTA0zcPtheH2'
    'wnB7Ybi9MNxeGG4vjPY1F9fW7YXh9sJwe2G4vTDcXhieZRmeZRmeZRmeZRmeZRnuWQz3LIZBxDCIGAYRwyBiGEQMg4hhEDEMIoZB'
    'xDCIGAYRwyBiGEQMg4hhEDEMIoZBxDCIGAYRwyBiGEQMg4hhEDEMIoZBxDCIGAYRwyBiuLsy3F0Z7q4Md1fG+ioIyO2F4fbCcHth'
    'uL0w3F4Ybi8MtxeGgcgwEBkGIsNAZBiIDAOR4QmR4QmR4QmR4QmR4QmR4QmR4QmR8XyNw4VSBw110FAHDXXQUAcNddBQBw110FAH'
    'DXXQUAcNddBQBw110PjSQZ5lGZ5lGZ5lGZ5lGZ5lGcYMw5hhGDNMY4ZpzDCNGaYxwzRmmMYM05hhGjNMY4ZpzDCNGaYxwzRmmB5d'
    'mR5dmbbGaWuctsZpa5y2xmlrnLbGaWuctsZpa5y2xmlrnLbGaWuctsZpa5y2xmlrnLbGaWuctsZpa5y2xmlrnLbGaWuctsZpa5y2'
    'xmlrnLaTaTuZtpM5v/6GTN2sn27WTzfrp5v103x9mq9P8/Xpvvq08U0b37TxTRvftPFNG9+08U0b37TxTRvftPHN81Xw+TCqmEYV'
    '06hiGlVMo4ppVDGNKqZRxTSqmEYV06hiGlVMo4rpN//0m3/6zT/95p9+80+/+Zff/Mtv/uU3//Kbf/nNv/zmX37zL7/5l9/8y2/+'
    '5Tf/8pt/+c2/DJiXAfMyYF4GzMuzCsuzCsuzCsuzCsuzCsuzCsuzCsuzCsuzCsuzCsuzCsuzCsvGt0zPl+n5MqlZJjXL/GOZfyzz'
    'j2X+scw/Vv76FAGZfyzzj2X+scw/lvnHMv9Y5h/L/GOZfywTgWUisEwElonAMhFYJgLLRGCZCCwTgWUisJQ9S9mzlD1L2bOUPUvZ'
    's5Q9S9mzlD1L2bOUPUsxsRQTSzGxFBNLMbHG16dIXTGxFBNLn7302UufvfTZS5+99NlLS7zUMEsNs9QwSw2z1DBLDbPUMEsNs9Qw'
    'ywOHywOHywOHy4MHy4MHS2G0FEZLYbQURkthtBRGS2G0FEZLYbQURmt/FQTkHs5yD2e5h7MURkthtBRGS2G0FEZLYbQURkthtBRG'
    'S2G0tMRLS7y0xEtLvLTES2G0FEbr/RqHC6UwWgqjrTDaCqOtMNoKo60g2QqSrSDZCpKtINkKkq0g2QqSrSDZCpKtINkKkq0g2QqS'
    'rSDZCpKtINkentwentwentzu8mx3eba7PNtdnu0uz3aXZ7vLs1U5W5WzVTlblbNVOVuVs1U5W5WzVTlblbNVOVuVs1U5W5WzVTlb'
    'lbPd5dnu8mx3eba7PNtdnu0uz3aXZ7vLs93l2e7ybHd5trs822MF22MF22MF22MF22MF22MF22MF22MF22MF22MFu30VBKRQ3ArF'
    'rVDcCsWtUNwKxa1Q3ArFrVDcCsWtUNwKxa1Q3OqPrf7Y6o+t/tjqj63+2OqPrf7Y6o+t/tjqj63+2OqPrf7Y6o+t/tjqj63+2AYz'
    '22BmG8xsg5ltMLPdkdjuSGx3JLY7EtsjmtsjmtsjmtsjNNsjNNsjNFv5tZVfW/m1lV9b+bWVX1v5tZVfW/m1lV9b+bU9MrI957g9'
    '57h9l3j7LvF2U2e7qbPd1Nlu2Wy3bLZbNtstm+2WzX6+BuZCuWWz3bLZbtlst2y2WzbbLZutPt3q060+3erTrT7d6tOtPt3q060+'
    '3erTrT496tNjCndM4Y4p3DGFO6ZwxxTumMIdU7ij6D2K3hNfhceCs/WVmeOmzjHbOmZbx2zrmG0ds63jKaTjKaTjKaSjPj3q06M+'
    'PerToz496tOjPj3q06M+PerToz496tOj+jyqz6P6PKrPo/o8qs+j+jyqz6P6PKrPo/o8qs+j+jyqz6P6PKrPo/o8qs+j+jyqz6P6'
    'PKrPo/o8qs+j+jyqz6P6PKrPo/o8qs+j+jweaj2+l3R8L+n4XtLxvaTje0nH95KO7yUd30s6vhZ+PLd1PLd1TGmPKe0xpT2K76P4'
    'Porvo/g+iu+j+D6K76P4Porvo/g+iu+j+D6K76P4PorvY0p7TGmPKe1xc/q4OX3cnD5uTh83p4+b08fN6ePm9HFz+rg5fcyTj3ny'
    'MU8+BqrHQPUYqB4D1aOhORqao6E5GpqjoTkamqOhORqao6E5GpqjoTkamqOhORqao6E5GpqjoTkamqOhORqao6E5GpqjoTkamqOh'
    'ORqao/c4eo+j9zh6j6P3ONqEo0042oRjSntMaY8p7TGlPW5fH7evj9vXx+3r4/b18aT98aT98aT98aT98aT98aT98aT90TYdbdPR'
    'Nh1t09E2HX+C6fgTTMcDdscDdscDdkcvdvRiRy92PGB3PGB3dBZHZ3F0FkdncXUW1+T7mnxfk++rGbmakasZuZqRqxm5mpGrGblq'
    '3KvGvWrcawZ7zWCvKviqgm/+Gse2cCxcC48F10UVfFXBVxV8VcFXFXxVwVcVfBWsV8F6FaxXwXoVrFfBehWsV8F6FaxXwXoVrFfB'
    'ehWsV8F6FaxXwXoVrFfBehWsV8F6lYFXGXiVgVcZeJWBVxl4lYFXGXiVgVcZeJWBVxl4lYFXGXiVgVcZeJWBVxl4lYFXGXiVgVcZ'
    'eJWBVxl4lYFXGXiVgddjBddjBddjBddjBddjBddjBddjBddjBddjBddjBVfBehWsV8F6FaxXwXrn16dIXcF6FaxXwXoVrFfBehWs'
    'V8F6FaxXxXZVbFfFdlVsV8V2TYuvafE1Lb6mxde0+CoDrzLwKgOvMvAqA68y8CoDrzLwKgOvMvAqA68y8CoDrzLwKgOvMvAqA68y'
    '8CoDrzLwKgOvMvAqA68y8CoDrzLwKgOvMvAqA68y8CoDrzLwKgOvMvAa2l+j8GsUfo3Cr1H4NQq/79enSN0o/BqFXwXrVbBeBetV'
    'sD4K1kfB+ihYHwXro2B9z1ehWmgWuoVh4Vi4Fh4LzPb1v7nXJ+j1CXp9gl6foNcn6PUJet32ed32ed32ed32ed32ed32ed32ed32'
    'ed32ed32eX3WX5/112f99Vl/fdZfn/XXZ/31WX991l+f9ddn/fVZf3nW4xfPengFeXgFeXgFeXgFeXgFeXgFeXgFefwKx8GxpD+X'
    'YFrIFoqFaqFZ6BaGBXmEPEIeIY+QR8gj5JHkkeSR5JHkkeSR5JHkkZxccnLJySUnl5xccnLZyWUnl51cdnLZdckOPTv07NCzQ88O'
    'PTv04tCLQy8OvTj04roU16W4LsXntPicFnkUeRR5FHkUeRR5FHlUeVR5VHlUeVR5VHlUeVTH0RwHWzbhNW/hNW/hNW/hNW/hNW+/'
    'C48FBpb8Ykt+sSW/2Lw7Lrw7Lrw7Lrw7Lrw77ndhWJCHX2xeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxde'
    'NxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeNxdeN/e7IA+/YJPflslvy+S3ZfLbMvltmfy2TH5b'
    'Jr8tvRgvvBgvvBgvvBgvvBjvd8HF9tsy+W2Z/LZMflsmvy2T35bJb8vkt2Xy29Ir/MIr/MIr/MIr/MIr/MIr/MIr/MIr/MIr/MIr'
    '/MIr/MIr/CJ9fWs3eTR5NHk0eTR5NHk0eTR5NHk0eTR5NHk0eTR5dHl0eXR5dHl0eXR5dHl0eXR5dHl0eXR5dHl0eXR5dHkMeQx5'
    'DHkMeQx5DHkMeQx5DHkMeQx5DHkMeQx5DHkMeUx5THlMeUx5THlMeUx5THlMeUx5THlMeUx5THlMeUx5LHkseSx5LHkseSx5LHks'
    'eSx5LHk8juNxHI/jeBzH4zgex/E4judrHK7L47o8rsvjujyuy+O6vK7L6+ReJ/c6udfJvU7udXKvk3ud3OvkXif3Ojkjk2xkkokH'
    'fxeShWyhWKgWmoVu4bHgSPUeWe+R9R5Z75H1HlnvkfUeWe+R9R5Z75H1HlnvkfUeWe+R9R5Z75H1HlnvkfUeWe+R9R5Z75GVxVlZ'
    'nJXFWVmclcVZWZyVxVlZnJXFWVmclcVZWZyVxVlZnJXFWY2b1bhZjZvVuFmNm9W4WY2b1bhZjZvVuFmNm9W4uX5NzodOjZsVrFnB'
    'mhWsWcGaFaxZwZoVrFnBmhWsWcGaFaxZwZrb1+R8khWsWR2U1UFZHZRVF1l1kVUXWXWRVRd5fn2Kk1NdZNVFVl1k1UVWXXiBdHiB'
    'dHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHiBdHj/bXj/bXj/'
    'bXj/bXj/bXj/bXj/bXj/bXj/bRTjn2L8U4x/ivFPMf4pxj/F+KcY/xTjn2L8U/LX0LeFY+FaeCywtsXWWGyNxdZYbI3F1lhsjcXW'
    'WGyNxdZYDHeK4U6x8RUbX7HxFRtfsfEVG1+x8RUbX7HxFRtfsfEVG1+x8RUbX7HxFcOdYrjjTc7hTc7hTc7hTc7hTc7hTc7hTc7h'
    'Tc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7hTc7htczhtczhtczhtczhtczhtczhtcxRTGqKSU0xqSkmNcWk'
    'ppjUFJOaYlJTTGqKSU1RoRQVSlGhFJOaYlJTTGqKSU0xqSkmNcWkxquuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uu'
    'w6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw6uuw4usw4usfxec7Xa229luZ7ud7Xa229luZ7udrQq2qGDL'
    '/pqtq6+CLSrYooItKtiigi0q2KKCLSrYooItKtiigi0q2KKCLSrYooItKtiigvXG8fDG8ShfCvbK48rjyuPK48rjyuPK48rjyuPK'
    '48rjyuPK45HHIw/zU28cD28cD28cD28cD28cD28c/12Qh/lpMT8t5qfF/NRrzMNrzMNrzMNrzMNrzH8X5GHkWoxci5FrMXL1bvTw'
    'bvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTwbvTfhW5hWJgWloVt4Vi4Fh4L8jDYrQa71WC3GuxWg91qsFsN'
    'dqvBbjXYrQa71WC3GuxWg91qsOv18uH18uH18uH18uH18uFN8OFN8OFN8OFN8OFN8OH96uH96uH96uH96uH96lHLV8GP9SRC1axW'
    'zWrVV1Z9ZdVXVn1l1Vd6v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v3p4v/rv'
    'gjy0gFULWN3fr+7ve2l7eGl7eGl7eGl7eGn774I8dI1V11h1jVXX6E3w4U3w4U3w4U3w4U3w4U3w4U3w4U3w4U3w4U3w4U3w4U3w'
    '4U3w4U3w4U3wvwvy0DVWXWPVNVZdo9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fL'
    'h9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLh9fLRz1fBQFprKrGqmqsqsaqaqyqxqpqrKrGqmqsqsaqaqyqxqpq'
    'rKrGqmqsqsaqaqyqxqpqrKrGqmqsqsaqaqyqxqpqrKrGqmqsqsaqvl8FAeksqs6i6izar69Cs9AtDAvTwrKwLRwL18JjAWJNad2U'
    '1k1p3ZTWTWndlNZNad2U1k1p3ZTWTWndlNZNad2U1k1p3ZTWTWndlNZNad3cW2vurTX31pp7a829taZeb+r1pl5v6vWmXm+e126e'
    '126e125u2DU37Jobds0Nu+aGXXPDrrlh13QWTWfRdBZNZ9F0Fs0Nu+aGXXPDrrlh19ywa27YNTfsmht2zQ275oZdc8OuuWHX3LBr'
    'nmVpnmVpGqumsWoaq6axahqr5i5gcxewuQvY3AVs7gI23VrTrTXdWtOtNd1acxewuQvY3AVs7gI2dwGbFrBpAZsWsGkBmxawaQGb'
    'FrBpAZsWsGkBmxawaQGbFrBpAZsWsGkBm3alaVeadqVpV5p2pWlXmnalaVeadqVpV5p2pY2vubi22pWmXWk6i6azaDqLprNoOoum'
    'CWiagKYJaJqApglomoCmCWiagKYJaJqAtr6GLnVNQNMENE1A0wQ0TUDTBDRNQNMENDeXmptLzc2l5uZSc3OpubnU3Fxqbi41N5ea'
    'm0vNzaXm5lJzc6m5udTcXGp6oKYHanqgpgdqeqCmB2p6oKYHanqgpgdqeqCmB2p6oKYHanqgpgdqeqCmB2p6oKYHanqgpgdqeqCm'
    'B2p6oKZdadqVpl1p2pX2ZVfcCGluhDQ3QpobIc2NkK4H6nqgrgfqeqCuB+q/vj5lWzgWrgWeoK5d6dqVrl3p2pWuXenx9Sk8p11n'
    '0XUWXWfRdRZdZ9F1Fl1n0XUWXWfRdRZdZ9F1Fl1n0XUWXWfRdRZdZ9F1Fl1n0XUWXWfRdRZdZ9F1Fl1n0XUWXWfRdRZdZ9F1Fl1n'
    '0XUWXWfRdRZdZ9F1Fl1n0XUWXWfRdRZdZ9F1Fl1n0XUWXWfRdRZdZ9F1Fl0T0DUBXRPQNQFdE9A1AV1p3ZXWXWndldZdad3b16cI'
    'SGndldZdad3dXenurnR3V7q7K93dle7uSnd3pbu70t1d6e6udHdXursr3d2V7u5Kd3elu7vS3V3p7q50d1e6uytdu9K1K1270rUr'
    'XbvStStdu9K1K1270rUrXbvStStdu9K1K1270t1d6e6udHdXunala1e6GyHdjZDuRkjXrnTtSteudO1K16507UrXrnTtSteudO1K'
    'X19Dl7p2pWtXunala1e6dqVrV7p2pWtXunala1e6dqVrV7p2pWtXunala1e6dqVrV7p2pWtXunala1e6dqVrV7p2pWtXunala1e6'
    'dqVrV7p2pWtXunala1e6dqVrV7p2pWtXunala1e6dqVrV7p2pWtXunalu2XT3bLpbtl0t2y6Wzbds3Dds3Dds3Dds3Dds3Ddg23d'
    'g23dg23dg23dg23dg23dg21dP9f1c10/1/VzXT/X9XNdP9f1c10/17/8nAfbugfbugfbRv0qPBYANIxLh3HpMC4dxqXDuHSo6Yaa'
    'bqjYhoptqNiGim2o2IaKbajYhoptqNiGim2o2IaKbajYhoptqNiGim2o2IaKbajYhoptqNiGim2o2IaKbajYhoptqNiGim2o2IaK'
    'bajYhoptqNiGim2o2IaKbajYhoptqNiGim2cr4J/wy+U4RfK8Atl+IUyDRGmIcI0RJiGCNMQYRoiTEOEaYgwDRGmIcI0RJiGCNMQ'
    'YRoiTEOEaYgwDRGmIcI0RJiGCNMQYRoiTEOEaYgwDRGmIcI0RJiGCNMQYRoiTEOEaYgwDRGmIcI0RJiGCNMQYRoiTEOEaYgwDQCm'
    '3WPaPabdY9o9pt1j2j1m+/pYZ2siMO0v0/4y7S/T/jLtL9P+Mu0v0/4y7S/T/jLtL9P+Mu0v0/4y7S/T/jLtL9P+Mv3Wnn5rT7+1'
    '16+vwrAwLSwL28KxcC08FliG5Zma5Zma5Zma5ZmaZUi9DKmXIfUypF6G1MszNcszNcszNcszNcszNcvke5l8L5PvZfK9TL6Xyfcy'
    '+V42rWXTWjatZdNaNq1l01o2rWXTWjatZdNaNq1l01o2rWXTWjatZdNaNq1l01o2rWXTWjatZdNaNq1l01o2rWXTWjatZdNaNq1l'
    '01o2rWXTWjatZdNaNq1l01o2rWXTWjatZdNaJt/L5HuZfC/P1CzP1CzP1CzP1CzP1Czj9GU3Xcbpyzh9Gacv4/TlmZrlmZqlSVya'
    'xKVJXLb5ZZtftvllm1+2+WWbX7b5ZZtftvllm1+2+WWbX7b5ZZtftvllm1+2+WWbX7b5ZZtftvllm1+2+WWbX7b5ZZtftvmljVza'
    'yKWNXNrIpY1c2siljVxf2kHHt3R8S8e3dHxLx7d0fEvHt3R8S8e3zOiXGf0yo19m9Ms3IJZvQCzPKS3PKS3PKS2D/2Xwvwz+l8H/'
    'MvhfvgGxfANiefhpefhpefhpuZuw3E1Y7iYsdxOWuwnL3YTlbsJyN2G5m7DcTVjuJix3E5a7CcvdhOVuwnI3YbmbsNxNWO4mLHcT'
    'lrsJy92E5W7CcjdhuZuw3E1Y7iYsdxOWgchyN2G5m7DcTVjuJix3E5a7CcvdhOVuwnI3YbmbsNxNWO4mLHcTlmnPcjdhuZuw3E1Y'
    '7iYsdxOWuwnL3YTlbsJyN2G5m7DcTVjuJix3E5a7CcvdhOVuwnI3YbmbsNxNWO4mLHcTlrsJy92E5W7C8s365Zv1yzfrlxsQyw2I'
    '5QbEcgNiuQGx3IBYbkAs88JlXrjMC5d54XIDYrkBsdyAWG5ALDcglhsQyw2I5QbEcgNi+Wb98s367Zv12zfrt2/Wb9+s375Zvz36'
    'tj36to0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrY'
    'RhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1U'
    'sY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYRhXbqGIbVWyjim1UsY0qtlHFNqrYpgrb'
    'VGGbKmxThW2qsE0VtqnCNlXYpgrbVGGbKmxThW2qsE0VtqnCNlXYpgrbVGGbKmxThW2qsE0VtqnCNlXYpgrbVGGbKmxThW2qsE0V'
    'tqnCNlXYpgrbVGGbKmw3p7eb09vN6e02x3abYxtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOK'
    'bVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthG'
    'FduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSx'
    'jSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduoYhtVbKOKbVSxjSq2UcU2qthGFduo'
    'YhtVbKOKbVSxjSq2UcU2qthGFduoYhtVHB+640N3fOiOD925X390WJgWloVt4Vi4Fh4LQD4+dMeH7vjQHR+640N3fOiOD93xoTs+'
    'dMeH7vjQHR+640N3fOiOD93xoTs+dMeH7vjQHR+640N3fOiOD935eujMx4752DEfO+Zjx3zsmI8d87FjPnbNx6752DUfu+Zj13zs'
    'mo9d87FrPnbNx6752DUfu+Zj13zsmo9d87FrPnbNx6752DUfu+Zj13zsmo9d87FrPnbNx6752DUfu+Zj13zsmo9d87FrPnbNx675'
    '2DUfu+Zj13zsmo9d87FrPnbNx6752DUfu+Zj13zsmo9d87FrPnbNx6752DUfu+Zj13zsmo9d87FrPnbNx6752DUfu+Zj13zsmo9d'
    '87FrPnbNx6752DUfu+Zj13zsmo9d87FrPnbNx6752DUfu+Zj13zsmo9do6xrlHWNsq5R1jXKukZZ1yjreurmeurmeurm1q+hu5Tm'
    'Y9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52'
    'zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d8'
    '7JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu'
    '+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zceu+dg1H7vmY9d87JqPXfOxaz52zcfuZz6WfqVPSfun0C0M'
    'C9PCsrAtHAtf43gsvBQ+Je2fQlhIFrKFYqFakEeWR5ZHlkeWR5ZHlkeWR5ZHlkeRR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5FH'
    'kUeRR5VHlUeVR5VHlUeVR5VHlUeVR5VHlUeVR5VHlUeVR5VHk0eTR5NHk0eTR5NHk0eTR5NHk0eTR5NHk0eTR5NHk0eXR5dHl0eX'
    'R5dHl0eXR5dHl0eXR5dHl0eXR5dHl0eXx/VTrp9y/ZTrp1w/5fopj9QfqT9Sf6T+SP2R+iP1R+qP1B+pP/J45PHI45HHI49HHq88'
    'Xnm88njl8crjlccrj1cerzxeebzyeOXxyuOVxyuPFx7c4v6nEBaShWyhWKgWmoVuYViYFpaFbeFYuBYeC/IIeYQ8Qh4hj5BHyCPk'
    'EfIIeYQ8Qh4hj5BHyCPkEfJI8kjySPJI8kjySPJQBWdVcFYFZ1VwVgVnVXBWBWdVcFYFZ1VwVgVnVXBWBedPFVx+/fp81v8UpoVl'
    'YVs4Fq6Fx8JL4fNZ/1MIC8mCc/l81v8UqoVmoVuQR8gj5BHyCHmEPEIeIY8kjySPJI/k5JKTywLKAsr+jfz1NwSUBZQFlAWUBZQF'
    'lAWUBVQEVARUBFQcenHoxaEXh14cenHoxaEXh14denXo1aFXn/XqUlaXsrqU1aWs8qjyqPKo8qjyqPKo8qjyaE6/Odvm5JpzaY60'
    'OdLmSJsjbY60OdIh0+E4hkyHTIcjHY50ONLhSIcjHY50+jemf2P6N6Z/Y/mcLtdl+RQuF2pJbElsSWxJbElsSWw52+Vsl7NdznY7'
    '2+1juf2vcstjy2PLY8tjy2PLY8tjy2PLY8tjy2M7/eNIjyM9jvQ40uNIjyM9jvQ40uNIjyt3HPp15a4rd12o60Jdp3+d/nX61+lf'
    'p3+d/nX61+lfp3+d/nX6j9N/nP7jg/vI45HHI49HHo88Hnk88njk8cjjkccjj0cejzxeebzyeOXxyuOVxyuPVx6v03+d/uv0X6f/'
    'Ov1PF11/C+dmoVsYFqaFZWFbOBYcx6c+rerTqj79U8gWioVqwdkmZ5ucbXK2ydkmZ5ucbfqa7WPhpZDlkeWR5ZHlkeWR5ZHlkeWR'
    'HVhxYMWBFQdWHFhxYMWBFQdWHFhxoYoLVVyo4kIVF6q4UMWFKvKo8qjyqPKo8qjyqPKo8qjyqPKo8miOtDnS5kibI22OtDnS5kib'
    'I22OtH2N1JVrrlxz5Zor11y55sp1eXR5dHl0eXR5dHl0eXR5dHl0eXR5dHl0eXR5dHl0eQx5DHkMeQx5DHkMeQx5DHkMeQx5DHkM'
    'eQx5DHkMeQx5THlMeUx5THlMeUx5THlMeUwHtpzccnLLyS3/xnZy27ls57Kdy3Yu27ls57Jd2+PArgO7Ur+O9DrS60ivI72O9DrS'
    '60ivTK9Dfxz649Afh/744D6u7ePaPo7jcRyv43gZR/z6ZeHr/5EsZAvdwrDw8d9t+636flkIC8lCtlAsVAvNQrcwLHyNdFnYFo6F'
    'a+Gx8FIIeYQ8Qh4hj5BHyCPkEfIIeYQ8Qh4hj5BHyCPkEfJI8kjySPJI8kjySPJI8kjySPJI8kjySPJI8kjySPJI8sjyyPLI8sjy'
    'yPLI8sjyyPLI8sjyyPLI8sjyyPLI8sjyKPIo8ijyKPIo8ijyKPIo8ijyKPIo8ijyKPIo8ijyKPKo8qjyqPKo8qjyqPKo8qjyqPKo'
    '8qjyqPKo8qjyqPJoTr85/eb0m9NvTr85/eb0m9NvTr85/eb0m9NvTr85/fY1fR+HLo8ujy6PLo8ujy6PLo8ujy6PLo8ujy6PLo8u'
    'jy6PLo8hjyGPIY8hjyGPIY8hjyGPIY8hjyGPIY8hjyGPIY8hjymPKY8pjymPKY8pjymPKY8pjymPKY8pjymPKY8pjymPJY8ljyWP'
    'JY8ljyWPJY8ljyWPJY8ljyWPJY8ljyWPJY8tjy2PLY8tjy2PLY8tjy2PLY8tjy2PLY8tjy2PLY8tjyOPI48jjyOPI48jjyOPI48j'
    'jyOPI48jjyOPI48jjyOPK48rjyuPK48rjyuPK48rjyuPK48rjyuPK48rjyuPK49HHo88Hnk88njk8cjjkccjj0cejzweeTzyeOTx'
    'yOORxyOPVx6vPF55vPJ45fHK45XHK49XHq88Xnm88njl8crjlccLjzDuCOOOMO4I444w7gjjjjDuCOOOMO74CmbCuCOMO8K4I4w7'
    'wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7'
    'wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7'
    'wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOMO8K4I4w7wrgjjDvCuCOqPMw/wvwjzD/C/CPMP8L8I8w/wvwj'
    'zD/C/CPMP8L8I8w/wvwjzD/C/CM+84/5K39ajT+FbmFYmBaWhW3hWLgWHgsvhePQP63Gn0KykC0UC9WCPI48jjyOPI48jjyOPI48'
    'jjyOPK48rjyuPK48rjyuPK48rjyuPK48rjyuPK48rjyuPK48Hnk88njk8cjjkccjj0cejzweeTzyeOTxyOORxyOPRx6PPF55vPJ4'
    '5fHK45XHK49XHq88Xnm88njl8crjlccrj1ceLzzKr18WwkKykC0UC9VCs9AtDAvTwrKwLRwL18JjQR4hj5BHyCPkEfIIeYQ8Qh4h'
    'j5BHyCPkEfIIeYQ8Qh5JHkkeSR5JHkkeSR5JHkkeSR5JHkkeSR5JHkkeSR5JHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5Z'
    'HlkeRR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5VHlUeVR5VHlUeVR5VHlUeVR5VHlUeVR5VHlUeVR5VHk0eTR5NHk0e'
    'TR5NHk0eTR5NHk0eTR5NHk0eTR5NHk0eWo3S5dHl0eXR5dHl0eXR5dHl0eXR5dHl0eXxudW6PC+1PC+1PC+1PC+1PB61PB61PB61'
    'PB61PB61PB61PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0'
    'PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0'
    'PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0PMm0fIV5'
    'ebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpebRpeaZmeaZmeaZm'
    '2/i2jW97UHh7Ynd7HnfbxbZdbNu0rkerr0erryepryepryepryepryepr8rg8Z88/pPnr/7JtLAsbAvXwmPhpfApJh7FxOPB6UfI'
    'j8rgURk8KoNHZfCoDB7b/OtSvi7l6yn517V9XdvXtX1dqNd1eV2X13V5XZfXZ/11oV7W5fxitj+FsJAsZAvFQrXQLHQLw8K0sCxs'
    'C8fCtfBYkEc40vBjw48NPzb82PBjw49NLkNyGZLLkFyGJPUPOXrCxQ4XO1zscLHDxQ4XO1zbcG2T40h+bPJjkx+b/NjkM5b82OzH'
    'Zqef/djsx2Y/Nvux2ennvxrHtPDxjBVHWhxpkVhx6MWBFQfmj0Udfyzq+ONIxx9HOv4W0vG3kI6/hfSnkPzY5Kd8WJ6fwsenVAFV'
    'AVUBVQFV17a6tr6df3w7//h2/vHt/OPb+ce3849v5x/fzv8pPBZeCiGPkEfII+QR8gh5hDxCHiGPkEfII+QR8vh8xnyR7fgi2/G9'
    'teN7a8fX1I6vqR1fUzu+pnZ8Te34mtrxNbXja2rH19SOr6kdX1M7vqZ2fKPsdAF1AXX/8+gS6xLr/ufRRdhF2EXYRdhF2EXYRdhF'
    '2EXYRdhF2EXY/c+j+59H9z+P7n8e3f88+l+sS8gj5BHyCHmEPEIeIY/Pr+Ah5CHkIY8hjyGPIY8hjyGPIY8hjyGPIY8hjyGPIY/x'
    'Fzw+5ddQfg3l11B+DYzET0EeSR5JHkkeSR5JHkkeSR5JHkkeSR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHkUeRR5F'
    'HkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeVR5VHlUeVR5VHlUeVR5VHlUeVR5VHlUeVR5VHlUeVR5NHk0eTR5NHk0eTR5NHs3Z'
    'NmfbnG1ztt2hd4feHXp36N2hd4feHXp3KbtL2Z1cd3LdyfWvybmU3aXsLuXwY6cjnY50fv0TRzod6XSk05FORzod6XLllgu1XKjl'
    'Qi0XarlQy+kvp7+c/nL6y+kvp7+c/nL6y+lvp799cLc8tjy2PLY8tjy2PLY8tjy2PLY8tjy2PLY8tjyOPI48jjyOPI4jPY70ONLj'
    'SI8jvTK9Mr0yfVyX5+v/IfXHoT8O/XHoj0N/HPoj5FfIr5BfIb9Cfp3cK6BXQK/T/zj4eKbmbGrOpuZs6pKmLmnqkqauYOoKpq5g'
    '6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g'
    '6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g'
    '6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYOoKpq5g6gqmrmDqCqauYHKK4KcgjyaPJo8mjyaPJo8mjyaP'
    'Lo8ujy6PLo8ujy6PLo8uj+5chh87/Njhxw4/dvixw48dLsNwGYbLMFyG8TV0l2G4DMNlmC7DdBmmPKY8pjymPKY8pjymPKY8pjym'
    'PKY8pjyWf2P5N5aAtoC2gLaAtoC2gLYj3Y50u3LbgR0HdhzYcWDHgR0Hdly548odV+64cseVO87lOJfrXK5zuc7lOpfrXK5zuc7l'
    '8W88/o3Hv/F8/Q15PPJ45PH4FH66k+WGzFLALwW854KPZ3qPZ3qPZ3qPZ3qPZ3p/CtlCsVAtOPRw6OHQPyW+B4WPB4WPB4WPB4WP'
    'B4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WP'
    'B4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPB4WPx4CPh3yPh3yPh3yPh3yPh3yPh3yP'
    'h3yPh3yPh3yPh3yPh3yPh3yPh3yPh3yPh3yPZ2mPZ2mPZ2mPR2ePR2ePR2ePJ2WPJ2WPJ2WPJ2WPJ2WPJ2WPJ2WPJ2V/Cs62O9vu'
    'bKfjmI5jOo7pOKbjmI5jOo75NQ4Xe7oM02WYLsN2GbbL8KmUjicijicijg34eADimLEd2+uxvR7b67G9Htvrsb0e2+uxvR7b67G9'
    'Htvrsb0e2+uxvR7b67G9Htvrsb0e2+uxvR7b67G9Htvrsb0e2+uxvR7b67G9Htvrsb0e2+uxvR7b67G9Htvrsb0ee9SxRx171LFH'
    'HXvUsSUdW9KxJR1b0rElHVOnY+p0bFrHkOnYxY5d7NjFjl3s2MWOXezYxY5d7NjFjl3s2MWOXezYxY5d7NjFjiHTMWQ6hkzHkOkY'
    'Mh1DpmPIdAyZjiHTsb0e2+sxUzq212N7PbbXY6Z07JXHXnnslcdeeeyVx1557JXHrefj1vNx6/mYKR23no9bz8et58MP5v4UXMoh'
    'jyGPIY8hjyGPIY8hjyGPIY8hjyGPIY8hjyGPKY8pjymPKY8pjymPKY/p0KdDnw59OvTl0JdDXw59OfTluizXZbkuy3VZrstycsvJ'
    'LSe3nNx2ctvJbSe3ndx2Xbbrsl2XLY8tjy2P7Vy+dOFx6MehH4d+HPpx6Ne/cf0b179xv/6G079O/+OXjo5vlB3fKDu+UXZ8o+z4'
    'RtlPYVpYFr7GcSxcC4+Fl8Knkr4q6auSvirpq5K+Kumrkr4q6auSvirpq5K+KumrcL4K56ssvgrWq2C9CtarYL0K1qtgvQrWq2C9'
    'CtarYL0K1msedM2DrnnQNQ+65kHXPOiaB13zoGsedM2DrnnQVWtftfZVa1+19lVrX/Ogq/i+iu+r+L6K76v4vorvq/i+iu/rlu9V'
    'jV/V+FWNX9X4VY1f1fhVjV/V+FWNX9X4VY1f1fhVjV/V+FWNX9X4VY1f1fhVjV/V+FWNX9X4VY1f1fhVjV/V+FWNX8Ouqzy/yvOr'
    'PL/K86s8v6rxqxq/qvGrGr+q8assvsriqyy+yuKrLL7K4qssvsriqyy+yuKrLL7K4qssvsriqyy+yuKrLL7K4qssvsriqyy+yuKr'
    'LL7K4mu0d432rtHeNdq7RntXGXiVgVcZeJWBVxl4lYHXA5jXA5jX3dnr7uxVSl4zx6u2vGrLq7a8asurtrxqy+vu7HVr8fJT6T8F'
    'h/4y9M+fSv8phIVk4WPojwnrY8L6mLA+vnP2qGAfFaw/TnD8cYKfwrFwLTwWXgrhXMK5hHMJ5xLOJZzLp/p8VJ+P6vNRfT6qT381'
    '4firCcdfTTj+asLxVxOOv5rwU5BHkkeSR5JHkkeSR5JHkkeSR5JHkkeSR5JHkkeSR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZH'
    'lkeWR5ZHkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeVR5VHlUeVR3Vy1clVJ1edXHVy1clVJ1edXHVyzck1J9ecXHNy'
    'zcVuLnZzsZs8mjyaPJo8mjy6c+nOpTuX7ly6c+mOozuO/jUO16W7Lt11GQ59OPTh0IdDHw59yHQ4l+FchnMZzmU4l+FcpiOdjnQ6'
    '0ukDM31gpg/MdHLTyc2vgfnwL6l/Bruv2uFVO7xqh1ft8KodXrXDq3Z41Q6v2uFVO7xqh1ft8KodXrXDq3Z41Q6v2uFVO7xqh1ft'
    '8KodXrXDq3Z41Q6v2uFVO7xqh1ft8KodXrXDq3Z41Q6v2uFVO7xqh1ft8KodXrXDq3Z41Q6v2uFVO7xqh9c+99rnXvvca5977XOv'
    '8c9r/PMa/7y2xtfW+NoaX1vja2t8bY2vrfG1Nb62xtfW+NoaX1vja2t8bY2vbe21rb22tdfo5jW6eT3J9HqS6bU1vrak15b0Gt28'
    '9qjXHvXao1571GuPeo1uXqOb1+jmta29trXXtvba1l7b2mtbe21rr9HNa3TzGt28dsLXTvjaCV874WsnfO2Er53wtRO+RjcvrfH6'
    'Q3HXH4q7/lDc9Yfirj8Ud/2huOsPxV1/KO76Q3HXH4q7/lDc9Yfirj8U9/PrjQ4sHFg4sHBg4cDCgYUDCwcWXwNzGT767fWn5K4/'
    'JXf9KbnrT8n9FFyoJI8kjySPJI8kjySPJI8kjySPJI8kjyyPLI8sjyyPLI8sjyyPLI8sjyyPLI8sjyyPLI8sjyyPIo8ijyKPIo8i'
    'jyKP4lyKcynOpTiX4lyKc6nOpTqX6lyqc6nOpTqX6tpW17a6ttW1rfKo8qjyqPKo8qjyaPJo8mjyaPJo8mjyaPJo8mjyaPJo8mjy'
    'aPJo8mjyaPLo8ujy6PLo8ujy6PLo8ujy6PLo8ujy6PLo8ujy6PLo8hhOfzj94fSH0x9Ofzj94fSH0x9Ofzj94fSH0x9Ofzj94fSn'
    'j8OUx5THlMeUx5THlMeUx5THlMeUx5THlMeUx5dim/JY8ljyWPJY8ljyWPJY8ljyWPJY8ljyWPJY8ljyWPJY8tjy2PLY8tjy2PLY'
    '8tjy2PLY8tjy2PLY8tjy2PLY8tjyOPI48jjyOPI48jiO9DjS40iPIz2O9DrS60ivI72O9DrS68pdV+460utIryN9HOnjSB9H+jjS'
    'x5E+jvRxpI/P2OMz9viMPT5jjyv3uHKPPB55PPJ45fHK45XHK49XHq88Xnm88njl8crjlccrj1cerzxeebzw+NyK/ymEhWQhWygW'
    'qoVmoVsYFqaFZWFbOBauhceCPEIeIY+QR8gj5KG9D+19aO9Dex/a+9Deh/Y+tPehvQ/tfWjvQ3sf2vvQ3of2PrT3ob0P7X1o70N7'
    'H9r70N6H9j6096G9D+196OZDNx+6+dDNh24+dPOhmw/dfOjmQzcfuvnQzYduPnTzkb+m7+Ogmw/dfOjmQ/P+eQX5T8HZFienvQ/t'
    'fWjvQ3sfuvnQzYduPnTzoZsP3Xzo5kM3H7r50LyH5j0076F5D817aN5D8x6a99C8h+Y9NO+heQ/Ne2jeQ/MemvfQvIfmPTTvoXkP'
    'zXto3kPzHpr30LyH5j0076F5D817aN5D8x6a99C8h+Y9NO+heQ/Ne2jeQ/MeQx66+dDNh24+dPOhmw/dfOjmQzcfuvnQmodOPHTi'
    'oRMPnXjoxEMnHjrx0ImHTjx04qETD5146MRDJx468dCJh048dOKhEw+deOjEQyceGu/QeIfGOzTeofEOjXdovEPjHRrv0HiHxjs0'
    '3qHxDo13aLxD4x0a79B4h8Y7NN6h8Q6Nd2i8Q+MdGu/QeIfGO7SzoZ0N7WxoZ0M7G9rZuPK48rjyuPK48rjy0DSHHjn0yKFHDj1y'
    '6JFDjxx65NAjhx459MihRw49cuiRQ48ceuTQI4ceOfTIoSUOLXFoZ0M7G9rZ0M6Gdja0s6GdDe1s0s4m7WzSzibtbNLOJu1s0s4m'
    '7WzSzibtbNLOJu1s0s4m7WzSzibtbNLOJu1s0s4m7WzSzibtbNLOJu1s0s4m7WzSzibtbNLOJu1s0s4m7WzSzibtbNLOJu1s0s4m'
    '7WzSzibtbNLOJu1s0s4m7WzSzibtbNLOJnerk3Y2aWeTdjZpZ5N2Nmlnk3Y2aWeTdjZpZ5N2Nmlnk3Y2aWeT7jVpVpNbz0n3mtx6'
    'TtrZpJ1Nn/FgNkHLJmjZBC2boGUTtGyClk3QsglaNkHLJmjZBC2boGUTtGyClk3QsglaNkHLJmjZBC2boGUTtGwclo3DsnFYNg7L'
    'xmHZOCybbWWzrWy2lc22stlWNtvKZlvZbCubbWWzrWy29afg5LLLkJ1cdnLZkWZHmh1pdqTZkWZHmh1pcRmKz1jxGStOrji54uSK'
    'K/f5X7bXAF6vAbxeA3i9oO96Qd/1gr7rBX3XC/quF/RdL+i7Xr/3p/D5WFbPGHnt3fVCuuuFdNcL6a4X0v0phP+P+Pp/XAuPhZfC'
    'ZxNvHjlrHjlrHjlrHjlrAmoeOWseOWseOWseOWseOWseOWseOWseOWseOWseOWseOWseOWseOWseOWt/8ThkeWR5ZGebnW12ttnZ'
    'Zmdb/djqx1aXoboM1YFVB1YdWHVg9WtgLkNzGZrL0FyG5jI0l6G5DE0eTR5NHk0eTR5NHk0eTR5NHk0eXR5dHl0eXR5dHl0eXR5d'
    'Hl0eXR5dHl0eXR5dHl0eXR5DHkMeQx5DHkMeQx5DHsPpD6c/nP5w+sPpD6c/nP5w+tPpT6c/nf50+tPpT6c/nf70cZjymPKY8pjy'
    'mPKY8pjymPJY8ljyWPJY8ljyWPJY8ljyWPJY8ljyWPJY8ljyWPJY8tjy2PLY8tjy2PLY8tjy2PLY8tjy2PLY8tjy2PLY8tjyOPI4'
    '8jjyOPI48jjyOPI48jjyOPI48jjyuA79OvTr0K9Dvw79OvTr0K9Dvw79OvT7NXSX8rqUn4ewvMr4enPx9cbg643B1xuDrzcGX28M'
    'vt4YfL0x+Hpj8PXG4OuNwdcbg683Bl9vDL7eGHy9Mfh6Y/D1xuA/hSSPJI8kjySPJI/kXJJzSc4lOfTk0JNDzw49O/Ts0LND/1Tj'
    'Qy82dJ5D5zl0nsPHcvg61PA5Hb4ONXwdaugJh57Qy5+vlz//FK6Fx8JLIeQR8gh5hDxCHiGPcPrh9MPph9MPpx9OP5x+OP1w+snp'
    'J6efnH5y+snpJ6effBySPJI8kjySPJI8kjySPD7/m/MnIK8/AXn9CcjrT0BefwLy+hOQ1198vP7i4/UXH6+/53j9Pcfr7zlef8/x'
    '+nuOPwUnF04unFw4ueTkPh+Y6/NxfRyuj8P1cfBnJK8/I3n91cjrr0ZefzXy3r9Y/exIs8uQHXp26NmhZ4eeHWkRYRHhZ+b4+oz5'
    'Yw1P4nv9pxAW/v8/+mT/Sfaf5L/6J9lCsVAtNAvdwrAwLSwL28KxcC08Fl4KIY+QR8gjO/3s9LPTz04/O/3s9LPTz04/O/3s9LPT'
    'z06/OP3i9IvTLz4ORR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUe1ZFWR1odaXWk1ZFWR1odaXWk1ZFWR9pcuebKNVeuuXLNlWuuXJNH'
    'k0eTR5NHk0eTR5NHk0eTR5NHl0eXR5dHl0eXR5dHl0eXR5dHl8fwU4afMvyU4acMP2V8fYrUh9SH1IfUh9SH1KfUp9Sn1KfUpzym'
    'PKY8PmK5p9jWim2t2NaKba3Y1optrdjWim2t2NaqA3PT73HT73HT76dQLFQLzcK2cCxcC4+Fl0I4l3Aun72yO/3u9LvT707fQOSn'
    'UC00C93CsDAtLAvbwrFwLTwWXgohj5DHF8KQR8gj5BHyCHmEPEIeIY+QR8gj5BHyCHkkeSR5JHkkeSR5JHkkeSR5JHkkeSR5JHkk'
    'eSR5JHkkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5ZHlkeWR5FHkUeRR5FHkUeRR5FHkUeRR5FHkUeRR5/Nan//Ff/dM//tf/'
    'fNZ/+8c//Zv/80///D/Wv/zXf/yX//T//k81Srrntyb5N//hn/7d+l/r3//b//TPP//f5/7zf//f/3L/8Y//sf71+9//53/+DS1a'
    'pPn7j/EX3l1+/+/5e3/h10jff+H355fxW+T8jb8wevzFENods//+pvxbQxj91/df+L2Azx8B+Df+wky5fv+Bdetv2R5/bwil9e+/'
    '8PTc228x+Df+Qpql5u+/UMafrbG/tRIl9/kXK5HvKO2kvzWLnsZfgNyrl3V//a2/MEoe338hVs3t19/i0KPGX4DcpfT5tx6n389d'
    '/MUkRl7v/yXtSnJl2W3lliSKEsnlqN3/Esy8U8cDAnUMj/7HTZ/KlNhG84R6ghb0C+aumzoLMszH/z/hzHufcE+wgX7Ce3XfPanv'
    '0MzAd8hA2YOLDOgl9KH6ke2Yr/AxDMFrFDlvkF8BxZW4NwPDov6EZg18hxiZT+vivmSH0TH0xaFulIeCt/Du2CuLT+ZHWEfvscV+'
    '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'
    'UO8qO3KtpFxDh82U7uXHuX4Q9SG36ezcgjmgDt/nj6WFXH4oBJIfGVV/PYvT94zy83RpfZ6a6/3+X88qzjlFoGjQAKbfXVkwm0EP'
    'muyzm3ZymQmnS17tkHA4M4MrsH19cxJ+DVpy+tnC3UZzJA5QdznGvYmsbhHUdsbtjfsJCq3USxY6tn5XRv3UNpwTh2pQ6Wu0faaQ'
    'QopoSnhszVdJL3eUmmJoWSTaJGCF4P50crxFUySpFDffJMeUyoIIEmAlzzKnYAP9RvIgrsGVKO6ITlF22ZObtQ7oNTd1Z6XFfQPM'
    's7IPbk1SeNHmaJStTio8FDSkm3PuOrglohfokWbSyYfY0XRKdH9DWHJUitDab0/St/pDdaLX8Lm+VNrqGC2f9ElsklfjgreItXJ4'
    'wmxi0ZXOzukVLkVLaQi835a+SsLgHM69Sx/lddLYaqAEE2Oe9liuGCI0e8/SnxVBrA7js5zDIX4gsrMV79z2wCqcVX6VP9cAtoIO'
    '02vzmxRyB9oRgWHKW+OQLAwUWOp5o5MgX4P0pvNpqJMDDYHuYPvszspfB5xUDl9GYl0kpGNVq6isVG5HsiXWZumcvqqODo2SW9nC'
    'bbajItKfZSs9m5Li1R0B57MLJIHzGHDz7tmswRmcthZdNi8JBIQzkbrHbKQ2qlcEqfyYi9mUczg+VDDc7KTMSGAq9KZdvkmRtd6Q'
    'rOmoH7+LJF8KUgnITiw6KekUgm7l8+HBytrD2U6NzHRCgs4bGhPGaM+4hjzgg3y23ia9lsdAITpThHE9tRSoSXrsXiefQsYQhDZY'
    '2cqwcnWO0AJe1lscrlTrQIpGEWU3ToTmc89BVfTRzZJYS0XyIUtvdnQk287hnnm1NZUUv6iQgdB34ba83aCYz6emQ7pxdkNDqlFX'
    'D26hla09mk8cFRrJJrDuaDt7dlZEG8oinVKGcZSWUdCsaWfCZRekWfQjfaqpFkrWb3D8vrvUSxr1eoPLxbHfIL1TIhCj5byl07i2'
    'qrWAs54sn7hLoQVKT+SNaIPTUNSve0GSMLM5Z7X79XDQxGVEcKS/7zsgt4SjQXrS57tAmgkrk41yUiZ5oqBS17FNqoWp6oDWgepO'
    'CtuIoTCrsZpy2DQdEEzTbd99gnsOguLsfR4uHLAKOro3n08W6W/l6GL1PYW2GqgDkwAGueT8BLPQwtrs89phiX+BRTiEhA50iER5'
    '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'
    'KQF/f0BiN5Nt7B/XXdkHCa6seaquUoarWNOykncLaytKGF3Ziu5Y8AgLcq7PMZXVsVQ2ntM5yjqmIG8iGY5PIKlHZZVKIkhONqsr'
    'awkdl1752ocubY1lUzk83FdVy9RLtm9uvuroaTDdGZIPOtM5o0pKx4uJH1+GczJaWkZ5lAmDkoNTdnyKmS6TCyYYXZLw+EqkDx4C'
    '+BDr51j0ep4Gp+SDcRQTyEephaptLkMVAbuEY3frxhAd1iqlXZLOwoiGNEpMqXkd0a93mVz6Ph8KNZ2NwpQo1cRhdAi7rxgR4aCX'
    '1yK7bHGVKu5jbLXpqCGtP049oey6aVUX9HsY2zNSjcY8vLJGwqDh7EfNJSi7nPiMHCnbuRaLsi8f6XjTa1I2HLW2GuxGVryNSh42'
    'Uz3WGTR/7B5llMRht5GSaxhL2djtOJVEOrrX0MYf01Gs9f/8//73f/6v/3uu/+d//o//93/+8xFnnDH/aYvsz3+Z/7V/VWv/9/xz'
    'fk+I7JfIsRdA5Ku12T9fMShi/xFxfxWPIu4fEfNXrCji3yLFk0h4iSSXSSS+RUwkkfQSOSeSRPJr0ibgWMrrKyUEEqnvHzKFRNr7'
    'h3gs/SUSM35lvESyTyQy3yIJv7LeS1dwdfdLJGdaF2fENtJOO/sWSTRc9z4vtdJw3fu8ZNpo9z4uR/uRyPu4VIdD+XVcwl8BL4DL'
    'rwuQUKJcJepLIuMlcu0u8uuw+L8cnko37iLzJXIcXRJZd5H9WjjjaA+9uYvYl4izKOLuIv4tUlAkXPfZi9NS6bT49LpnPtHqeqFc'
    '8Pj78hJxeKF9fYsk0u6+CRE6/74L/YPr8lYuDi+0fysXj0fKv5VLzXRe/PsxOpcXRIIRS0cS9v2RQBMKTihUUmLBv0RwbUN461OL'
    'g43vjxiackhCceNQ3qclouoIRSwcfuX9FJWEIk0cblL/4X1ajnlOIkM8rrhF4imKOKP3aYn40If3U5RwF+P7KcqVtjG+n6KCdkkU'
    'T5GlbYzvpwgfqxiu9yxGcbZxKO+zYHko4ixEWrn4Vgu24FfeG+1w4YRWQOMyvvfZRboicQkR0lBxC/VDo01vreDxh5IVIvRDyQkR'
    'OrnJCxEcy3uj8VlM732OnnYoV/GI0NnO7030uCy5CxGac37vokeVm8Uu4lXM711MHn9IGI6VfqiI24rPYnnf1oS3tbxva0EVVbzQ'
    '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'
    '8HM48RERysXRnJMwF8h0sSn/jCl4RIRycShSfwS1PhIC6mJxzv1mW1pp2xccitAtuCrr+uYJ0x4ou46INO3pI8Ky96hasrtqnyxV'
    'C00oy1ZMtPw5XpdfJAXxComcIK9+Lj+je+pvOcGEEuKs4FgFKorOdZbcAbgm8zoQgQ81uD2iO5uh217Mz42lHhFhtJDV/p+az1/n'
    'Db8ijBbyd2RyMuH1KJfkWP0tT5RRr1dh2Bu6QXULBggabjOiGo02uonQA260ANSTW2vn1YGzAk//BxEv7Ceas8DTe7yHAizv8V19'
    'BQQcoUbq37GhfzwVfGNEk1WA/8+/SyR/1f+SRP2pydg0kpXt+2WeRpKyxe8RkGkkKdt3z2z+Xc32A8ni/Lua7Qc23/l3Nduv8BJ+'
    'Zfxchz//Lme7/JBgP/+eN3hERGN4khDdbFKl32mC/Px7VuwRiSK1QxJJcOziRwQjgKeDcCurnn+XxP3QqmD+XRL3ixMJf6j/3Lv8'
    'EblQhT8isi08/pBIRBkU2T+TfM+/y/N+6BAz/67I+vEaitQmDWS42zUc/noNRV4Tr+G4HqZxP0zjfpjGfY/HfY/HfY/HfY/HfY/n'
    'fY9fCTF3PDv/v06IhGzMq/FCMH+Zb57Ql8xUyCyFzL7LvJovBIB3fYnYu4i7i/i7SLiLxLtIuovku0i5i9S7SLuL9LvIc2aOZ/s3'
    '1tKSyPxHxB+RSiLrH5GnQB5/aP8j8ugGOi9f0bv/fuU7D++XiH2PpdBYvqJ3//3Kt5v/JeFfEt7jR8Lrd2qkCX0F7/4r8p3B/ksk'
    'vX6o4u/k1/J/xyp8iZS3SMBVqa/f+d5m6Uuk/yMS/jKRvhLvF+1Fg+z9X7SHr4Yff5K436F4v0Pxfofi/Q7F+x16sSD/aULjKjHv'
    'P7PuIvt1EAKe7GReu2wN7XLy76/goUy/Dn+E7MKXSHz9kMt0+FN63Q9r8Sv5JfK9l8eXyK/Tn/6qhtYl1deMSqEN+HIy/rmrHsfS'
    '3yKVRPL9guT7S5TvL1G+v0TFvtRpxitf3FVxlLcm/M5a+CUSXiKu4lfiW58WWrqSX8Mt+DvlrbZRKZf6fkJwo0t7fSXjc1bmeygO'
    'v7LEnHEs+z1nVNzVvH7oe6usL5H3Ln5v/vUl4t6TrviV903zLJLfG21RpIhrhCLvm/adP+JL5L0BHh/O2t+rG3DS4zUjhyeqzvfb'
    '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'
    '9KI0l+5sDUWC7GYUmU1l6mQ2pgq5d9tqFMmTSKUwXkhzpCnQ6fub7f9fTZMa07xeOo/lkH5G+KJTWk2SxIxAfhO8f0QksoAPmc+7'
    'iCYsS0FCRxFRYqJPznOZY+CnJClQpDWXs6ARtOnzrMSEFjdLBjOLNAk60vGcuyxuFJnze0YjFWXpz1xwLHImNpxd8Y/4RZcoAF90'
    'CwRDEvOeR4cvSLnehuaySHU/wXGhaHwOnyLeBB5EZS4oTgQShDLn5w98yDxx3ynxHxG58VQUmW88GP8PdQ4QZfT3ahAPioZb543G'
    'NrdKVAxdmyqlP2hcpgq5/AuVOFOTZmgF/ZE55yh2w200hd0blA5+RO5ZBA9G4XFraA2Fx43nbkK1qc3hR2Q4PHq0/7eO/fcYryTy'
    'NmOfpgOvH7e/f6zux+Z+PMWuRXrz5f5/ux8f8+PHXP7443A/zhv9m+H5I3KY/0vR7neE9yPiZrvMx8W35fyIuDkv7suL+/KPifvx'
    'R/vNp/txvh5999f4iDg9l0f+D3//mLKf/v4xYj/+GN2Pc4V2xdX7MVw//t+puc6hum+W8I+IU3N1U17dpqpusqvbVG1zwOdHwk12'
    'c5P9wQ5/+nG4aR5umgWF+i7Z/Yi4aR5uNw23m4bbTcPtpuFUO5xqh1PtcKrd3RbanVZ3p9V9drK/+cleIiWaGS5xuB939+Psxo4Y'
    '6M2n+//lfpzvq63iw81sl5Tdj8X9OEcQvoldPyLN/f8Ul7rQ/92Xp9v96L45b+7H4H6M7ke5i3+VcXxE5rt4wW/OEhXL+JTqRtHk'
    'Lk+vcOdyKXOBcO30d7fYi9zZOr3enZHFnZHFnZGlJgnm0nqs7sOr2+DVfXM9JI5Pc+bOyOLOyOLOyOLOyCJn5DcJ1kfEzbY7JIs7'
    'JEvL8mZ6sbMsza3vNq/v0ml/NKfm5tQ8cWa8LquNDolmzsvS3dLubrK7m+zuJlvIKhoeL93Ndnez3efo+kZLqLvJ7m6yu9tT3U3z'
    '7g6t3X3s7j52d8fV7nbwfknsjRbl7vbx7vbx4b72cF97uK895KAgt78c7psPZ7UO97WH+9rTbaFT4q2Z9ufpNtLpNtLp5vmco6ut'
    '45vFIaKT73QL7JxRqooH/+m207kvX3/I0Q67udYuIYdGIrODMHIkEbOzaz3cj6f78bIEHB+R2/3/ER1C9Kk2s/qqOy2rOy2rOy1r'
    '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'
    'x9P9eAkHNY75XvWYuYo0GKOA2uUy+C6pNi+ETF+u2vxy1eaX874uR/F8OcfrEserk7NyVadtR+t81X1V9nEJuXOmC/Ll6twvl5d3'
    'uby8qz5ShU3acg7W5bLzLudaXa64/XJO1SVOFXaSu1wq3iXuFJbFXy4V73Jl7Zfzoa4meqYs/cv5UJdLv7uc93S5xLvLJd5dzmO6'
    'JOUOe3Jezm+6nN90uZS7y3lMl/OYri7ZtnjASeIdlrdezm+6xG9q5IheUkWPCNblvKfL1c9fzm+6htym6ZJ7DYHX0CqMuCoYuVwq'
    '3uVS8S6Xine5VLzLpeJdkoqH9NPXcHvbVdFfrj3s5ernr+H07FrCXi7P7nJ5dpewO2Ok45I2sFhLfLlsu8tl210u2+5y2XbXLoV5'
    'aL1dzt3lcu4ul3N3OV7na5/3c4o4LKdn1/T12p2eXbvXy6XVXa7d63U43bpcusvl0l0ul+6SXDos2bkkmQ5p4i7X7/WSfq9bw1do'
    'jJwW/uH2s6OLvg6n58PpWagQCEC+XO7c5XLnLseBcJ1ZmGnI3zqdyl2+3OXy5a5TjmqKnFwua+46lTaRlC3c1IOKpS/hOki4ZFwG'
    '3eUy6C6XQXe5DLrrctp2uXOX8FFveEVzfNSXtLLFtOHLNbO9LqdzR6FwOQqFS1rXFnTsrmMRoL8cg8LlGBQux6BwXU7Nrlvtdc95'
    'cVg3fd1zvWRBgyXpkpGK5i4hwqZQ+3UL00nA9whnKmFqlzSxDRiDuCWaTSjldc+ZccjMft1zZlzKOHMzGw75g/dc0IrdV64pe7Jy'
    'D9dram3bXlOLE6cEu/Q9z1wen/EEEGLsgYvlkRwYyu+5JI2yB3xKnr6oUUuD65FrOqGWl2NguB5nJRz3wuW4Fy7HvXA57oXLcS9c'
    'jnvhctwLl+NeuLfN/Rjcj9H9mNyP2f1Y3I/V/djcj939ONyPu/vxcD8KhxEVPNzb5f4v9Y7krd4ur/F2eY23a4p7u4zGW5riIrP1'
    '7Zri3sFpODgNh7ZqJ3xLAuMPg3PaDsIaGfEVx4JM/5amuJh4cgetgMdx3pLTjk+RrCZcIVE6MVEc5Y5SE0+lP7ckNm6U4XG7Nrm3'
    'pDRWOlruqO0r6XNdYuPtEhtvSWzEZlO3a9Z7x33VW/N2LXvvKEUyCRXlTEG8JSkRVeRMgWsZfCeN1ZByNZ8RF1oSD5CyVm+X1Xgn'
    '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'
    'E956/eh0Xt2el/AW+VwvEaft6rRtwluvH52ehZo44m6pTtvNabu5Hd6i9GKiHdbcPm/CWB5oQpvTc3N6bk7Pzem5qW2ng0Pa18ZM'
    'G785bTen7ea0LY1ra8A3O20L7zChNS8Rp/M+335DoL3Znc679LKutP27tC8GQOolMtv2Esn8d+l0vqHIbOFro/WnbW3RWnW357tE'
    'SDL+X3oYVNpF3a2I7ux8d2thuJ0/3CoYzsIPp//h/LlRhDCLFvdwe36scotfIm7nm0jY60en5+F2+3C7fTjdDqfb4XS7O93uTre7'
    '0+3udLtL3CLQStaaEDQ/u9Pw7qz63pfnye40vGtSCS2f/Vhcp18i58y10HEWrjkQueGL5vZ0VPzyEhH260yfe8wRT2rn+hIRzqZO'
    'dvKYOZuoWvclkhbxlJeIJp7Q1B3akwJFqofxXhJuiRxu+x9Deo/QnB/OCBzOCBzOCBzOCBzOCEjxSG+km3Nb7rlT+5HRIjilJUkn'
    'DZ/OOEg/21TxFWIc0PE6nXE4neZPuc5F2gpSVkLU1i+R2fFraGLOOUGxbfgVp0SM8CmXMMaTiZBCk4b7XwpNqJNy2C53UFzuoLik'
    '9gDvQ3+Vm9BcSIBzw3UhHH5U7v0ScevicuvichbhcsfF5WzB5WzBJYTKG36QswiXswiXcwtup+3baVtDmBstpdvt/9s5fre75t1O'
    't1JjQvm1LxGn4Vvps8l+3k7P97G8T93O8t9Oz7fkoAUyArfT9rMt4rMvkbCosXmJiObxVH6c5h+n+acI/QDN3+P0/7i9/TjNP25v'
    'P07nj9vbWl5C5uxxKn/c1n4eqaiGxRpMjcnrx1Xb0ZdIXB3TQVsR07U5bHlB3PgSKW6g1f043+xLwq/o7v9j0eX8JTIf84luMsFU'
    'oLx+PBdlli8R6UKcSeJ2b5jp2iJgxCEECfWwyAxdBRxnmAM+GIwPIQnpG75ImxPShAYh7Qqklqkx8btAlCYtGHsQhNGPWBBfIkMW'
    'F36LErjhQN3iMC2JXz9e7kcN/tGLzXEQ4iYNtsl8xOD+H92Pyf2Y3Y/K1kaLMDp7ECUBnU7JEJ09MIUmrx/39cOPRY+Xl4hTeXQq'
    'F7Y+upKEOCc+bSSR3JmgJSeNFnxyek9O78npPbkTINUV2BKS2+rJaTw5jZsCk9ePbmMnp+XktJycqU9uT2en2+x2c3ZadZh8cJh8'
    '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'
    'BY196sWbZO6rSrxJrn01lDeJWIu4/RqSQpJnqy28KMTHnWiu4uJmZUFc3PyGSHo4BM3fJFqpjNajrceJoGx9Zm+KutcI3ySS7Hvi'
    'coRTAo4y9tmmbxIpP8X7du31+jfJ2nsE3iTCKvyhZ4+JfZFogf5K+18FG9GQxPoVKr2I1T5DGTUFzQ1H6ST+7YqPmeaGI2vX6t73'
    '2vYpq2+Svi+O8CaRIqsHrkiqIKLCXW1KxHHg1tl3iAV7veVDSPLsg3AvEkE2/0Iy9ziNN4lTHOFNIno7nrQgm1ulfZEkj4qq/a2d'
    'kOlDt7hKeJSwr8T3Jon71gVvEu1QgR/Ke//om6Ts6xq8SbT7DS5aOpqgkLq7JN4hyZDUL5yuvQEt4Cj6tBK/3CowiTE1y4PPSG4A'
    'qlnPsU8lfJNIoSS8JI+8rqisPeK3R2Z4pPgKGnGCbeZ79GhRLZIMT92jI94kbR/kf5M4VczfJGNfzOpNIpo7ml/P5fLuI5p7xDO6'
    'JbCO+/IIJApWFAXbnAKSSOZEK0TidNd6k0TPXxIF2wzl094k2jApEInUGaYnKx5WvqSMJOIXIC01HlIriacrWPiE0xXVnSRmFGxz'
    'Ies2Hmsfln2TiB8p4zFqDxYaRbDNhSRmFGxzJfaO0kW2MIlo73Rho3aRpf3XNrJk0kSpB5pxPXVfk+NNoj2HiaJLsIIotLsW7oko'
    '78gIUgwUlcd4rn2pqjeJFnbCD+2rsL0oguruxE1BS5jT/ZBaoKkgibAKvXlRaoH2StsSRLQUWnMoEk4iCikDRq9i/AZrxlEEcNBw'
    'KsPzz8Uw9+CHN8m1z2F6kwiUiad7S3wMp/uIfUX7Em1QEEWlOKh7RZLgmZQxOq3Y0uuX9xGF9D+drxHJ+4g++QWvH4/vP47dj3P3'
    '47X7ce1+vHc/PpsfPyL91x/Pf1vxBrsV2IqPMP/1/3H3Y7KD/9SV3iR59/+y+7Hufmy7H7s5/v4TQfMm2Z3wR0z/7/8AHXuT7M75'
    '3J3zuTvnc3fOYXfOH0n864+7E/4IxX+rjcQhYXcUn2jQrz/ujj/ujv8T+/nftKD8+ZvEXvPjpJnH3TWPOyaIu2sed8f/ifH8b1qA'
    'Xn+T7Jgg7pjgE9f535VrPx+FN8mOFdKOFVJz73PabWjabWjabWjabWja3ae028q028pst7LgK5F3W5l3W5l3cjPvrkzeXZm8uzK5'
    'uvchy5X5qZm8SXYnnHcnnHcnnHcnnHcn/AlaOMt67JXrdJRld5Rld1pldyBlJxrLbrfKbrfKbreKFTAl4WrtnrWfqu6bZHc3WpE9'
    'pye07Vbedu9z23FY2+1Z2+1Z2+1Z23FY28mQttunvvtm332z777Zd98cOz1g7Dh57OTO2LH52MmdseOEseOEseOEseOEseOEsTuV'
    'sTuVsTuVsTuVuTuVeZrrlOnCzt1jMneHOneHOneHOneHOneHOneHOq36DXVA3iS7o527o527o527o52707t2+3Tt9una7dO126dr'
    'x/zXboeu3Q5dux26djt07Zj/eqxuGOhU1+4KrN37+6ni9L/B408sxptkx+Zrd3xrd3xrd3xrd3xrd3xrd3xrd3xrd3xrd3xrd3xr'
    'x/337uDu3cHdO7F1R6tEFFJC7t2p3rtTvXeneu9O9d6d6r071Xt3qrf1GtRAKtO9O9t7d7b37mzv3dk+u7N9dmf77M72sTe2oVL+'
    '7M722Z3tszvbZ3d8TzfTAifwm2RYWXPgzKcliSTrPjHAfyToI3qWJflZpDO/fvl1oe8f6+7Htvux734cux/n7sdr9+Pa/Pi76yr/'
    '57r6pxz9tDXyfw6sf9wWkSTuPpF2P+bdj7sTCrsTCrsTCrsTCrsTCrsTCrsTCtsTusXnWWmHn83/4+6E47n7Mex+3J1qtO7n+jMo'
    'lHf+x7zzP+b//I+//rjbirTbirTbirTbirTbirRj8LTbhLTbhLTbhLRj8LRj8LRj8LRj8LRj8LRj8N/9hHnnJ8z/+Ql//XF3nnl3'
    'nnl3njnZ6/gTs5F3fsK88xPm//yEv/64O9W8O9UirumfmJe8c8K9f9ztVtntVtlx/8d997+tTCTYym6zSrVC5mdSwZtkt2Vlu2W7'
    'i1B2F6HsLkLZXYSyuwhldxHq7iJU+4pDF983ye6A6+6A6+6Aqz1gaI76JtmdcN1dh7o727o727o722o1zPITcPUmufxl7c657s65'
    '7s657c657a5w251w251w251w24k646rGBOD/z97bNUmyG9mBf4XG51Fb4Bt4JDmaXc3YNY1ESg+7JmtDfHHapm83rftypJFs//tm'
    'RmdVwStPedYpZFMaNh6r4kQk4F9wdzgcQUtVBy1VHbRUdbikqnUmZk2Hs6bDWeNt1nibNd4WjbdF423ReFs03haNt0XjbdH0tiR9'
    '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'
    'oFlMNKL3RT+Pqw3rA1K1n5i1h4v2cNUebtrDXXloNM6/eC5+eygPevGh0x567WHQHkbtocZbk7WHRXuo8dNo/DQaP43GT9NWk5kJ'
    'SbLo2pOgsIq2PVNGKmONUDxkG0TbnuvNgy2JjVbzgvpaL3qUwbFonG8vjUGxfVLOUx4PNf5bjf9W47/V+C82Uq+vWt7Ss/OUzsFp'
    'tbIQPKScpuFO03BxVQykqtPUXPToub7LeEvP8qMZGUyn8d1pGu80jjuN407juNM47jSOO03jnabxTrPgTuOvFzeHe8RDLxsyBQSx'
    '6m26B0QwG/6OZthlhx6DjISXJ9aQTRP3wxTojHiN8V5jvNcY7zXGe8n4/+9vfv2nL5//ZftUP53vjP1fj9j4sFf1//76b+sv9R9/'
    '927//OWP26//5tf/V/15+9VvP3/+5esvX+qffvX77ZdfPnz649df/7fml+LDbtib3z6W3je9nR/y8W9+++Du23977/rtqevt0PP2'
    'kV1989upi2OHWr/9t9/8dlouq+rb365dIzddVHNvHvl88dTf/nbuedu8mWOuXHrwvplqNne9nbp0bHnr23W9hK9vp/mbqebXi3v2'
    '9rdN19u26+2+ea89b4cuex5K19u1Z+TH8fe3v710vd1F87R3vf1m36GWnnWs2svNHW96O9jLMeW3vu3z0iNrfbYldklL7JKW3KUl'
    'OXe93aXfvsvjsl1+quuya29fDVyezNsl9Xh77Xp763q7dL1du96ee95OXSNPXSNPfSPvkpbUJS2pS1pS7Ho7db2du972XW+HLjnv'
    'olruolruolp2XW930Ty/mea19mRMjqhm6nq7K7KIvuvt0PV27Ho7dcUlXT5y7IoFYx/HumLB0Pd2l5cbumQthJ7Y4O1R7PH21vX2'
    '3vP22zOi56im5J7ffnv8fbydut7OXdFcXyy4d9F86omB365jp7e/3bTx9rdDz8hL7fntaev57dl35R16OGaN6xp5F83n0sXv1PPb'
    'vovfLnZxrEtayto18tz1ds9vf7vO7u1vd8naPne9Xbve7uL3Xrrezl1vd+nYHrssU5ekmrnr7S7rYLo4tnXRfOvi99Yl51vfvLus'
    'w9al31uXhm5dVnHbu3Ssy1/bTdfIu1bBvcvz2Lt8pr1rp6d0/fbWNe+ta+RbH7+7ZG3tkvOtj+ZdvkMNXbFB6nq7y57PXfyuXatB'
    '7rLnuYtjS9dqULvsee2yiqWLaqVrBS59VOvbPe+T1C6bWt5smeZ6qet/+293eR5r12+vXbZl7ZKWtcu21K6R1y6q1S7/vC5dkUXX'
    'Gjr35bj6Rt63hnZZ5LlLUueueU9zV31ql8fV93ZfPtV3vR27rGLskpbYtQL7Lstku/TbdeU8rO16u2v9Ln3rd1801zXy3MWx3JcJ'
    '7tur6cuvdWWhzdaVhe6yyK4v89+1lqS+kXf5LbFvb67n7Y46j2q7akzs5V7ft9vzLm/P9Wlo136o7bKpvmsV7JKWjprBYw3tiyT7'
    '9qC71lDXNfK1K0PWtYNtbd/+d9/bXXbNdFFt7lsFu2zL3OX1zF1ZSdOV45r73u7yW6aumoOpa+S5x651nLrLrqdesdqes2uHRe7S'
    '777Y3/RVDXTpt+3y9myfben77S4ds106Zrssk+2qObBdWSrbF3/3eXtdUc3bM0U+9dRKHm/brre3rrdLz9sdp0tTT12uTz11uf6h'
    'hcib3/ZdHHv7uXefeiqK/UOPkre/7bveDl1vx663uzT07TlN/9AM5e1vzz1v2y45t136bbv023bpd+nSktKlJaXLOuS+t7tsS+7S'
    '79yl37mL5rlLv3OXfucu/e44wZ0ujXLf/naXhnZk/pee00jH277r7dD1dux6O3W9PfW87beut/v4bbretl0jX7reXrveLl1v1663'
    'u86em65z76bvt7vOvfd1aHh7Dvt4u+sc9NT3dtcp6qnr5Lrp6jVgunoNvL0q6OBYF9VcF9Vc13n/qe/trm4BU0+3gI5T1MfbPRra'
    'sfofb8eut1NXp4Kl6+216+2t6+295+0Or6f2rILH230cy11vl663axfNu/gduvgdu/jd4WnWLu++9up36JKWt+dynZ22t+9wHW+7'
    'rre7ornSFZfUroiqdkU1tSuqiV0RdOyieeyKoHNXDPz2bM3xdlc8lrtonrto3nciKPXVaXbVcWXTVXPQVd8y9dW3dM27dtF86apA'
    'W7qqBpauioXQVacZuqrfQhfVQhfVQhfVfFf1W1/vVt9Vr7h2UW3to1qXjoW++tQujnV1IjF9tdB9/Vv6Os90VagY2/fbfadT+qrA'
    '+nSs67fXrt9eunRs7Ts13+U7mL63+zpLdXn3HbWSy+WOzbe/3bXjkbt2mfp2FUtXNFe6ornSxe/SFVmUvgi6K5orXfuhJXVkDpau'
    'nMfy9nzL8XbtenvuenvpenvtefvtlVjH21389l0c813S4rv43ZeF7jhXU3vuEDne9l1vd/Vmdl3ZWNeVjTVdOWzblcO2XTls2yUt'
    'pivzb7rk3HTtcJmuHS7TpSWmS0tMl5aYLi2ZuuTcdMm56ZJz07NnMb+9c9z57bd3zDve3nvWEjN1vW263u7yckNX7j505e5DVy2V'
    '6YrHTFc8ZrrisdL126Xvt7vWkti1fseu3dTYJWtTVww8dcXApisGNl0jN10jt10jd12S6rrm7brsue96O3StBqFrNXB9kWTXyL3r'
    'ett3vR26aN73dlf8Hbaut7skNXbRPHZRLXblHWJX3iF2aUns4ljs4ljq0tDUZVuS7Xq7yzqkLh1LPbK2uaXr7S5pSV15xdQl56lr'
    '5LlLWnKXtHTcXmZNR3+H4+3a9fbc9fbS9XYPv9c9dr2dut7OPfN2XRxzc1feoStjsrmut7tW/6nv7dBDc7t1vb138Xvq6Z+qZGv+'
    '7sP/kD+2TpPS0vgKnqdJ6QQM4YWDVw6eXw0/U0axugiuJM0gfOIGs3Ffd6+Gny+ZNJWDzxw8cPDIwRMH9xw8c/DXC/CRDMkcvHJw'
    'Ups89fXKjZ2wBJs/yXvk4IGDv36q+dzbiyOkUqCC4GXi2PR61Z6jmhmG8IWDzxy8cvDCwTMHTxw8cvDAwT0HJ4XAcnDDwScKPu0c'
    'fOPgnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLxPnLw7jk2OY5Pj2OQ4NjmOTY5jk+PY5Dg2OY5NljNLljNL'
    'ljNLM/f1mRv7wlFm4YRg4URs4QR44dRj4ZSvUIQ0nH033OphyLVpI+GcRG6cRG6cRO6cRO6UJTCcFTOcjTScBTacfTfc6qEd+oFw'
    'ToDdxsE5bfKOg3Nc9RwhPUdIS8KJzFVRL2d8Dl+d2g8awjcOXjn4zMEXDk5SxnNwx8EzB08cPHLwwsFfr6v27P2sHHzj4DMH58ZO'
    'LDYH3FAZcsK5OuDk17l0/eI4uKfgTLp+5dL1K5VgPNlIxoU44IaCE/J+wDcOvnOU2Tg49/WZ2JmYqTTaAV+owRROxAonYmXmCBk4'
    'eOTgiRs7JwSFpPvKwUkB5mxkpXTVEJH8Ge4mDk4OZuO+bjm44+CBg3sOHjl44uDccrBVDj5z8IWDBw4eOXji4CQhyUWeNKmcWaqc'
    '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'
    'W5P9S+ALJ+ovHz5/ev+H+rF+fO3v/G39uX5d/vz1tfi/+1i//tNcl39+/4/1S10/fH02o8n5Cb/599uXP3+tH7efX/tT//Dh0x/X'
    'z8/gwccXvv9T/fqvdX81evv585d/ff+7z1++fFg/f3l87dn/21d+//nj558/f/rD9vOfPt6YdaMK80nbcF75R1aFV5P/OSXToOSd'
    'KJkHJe9EyTIoeSdK1kHJO1HSDEreiZJ2UPJOlHSDknei5Ait7kXJMCh5H0raYSfvRclhJ+9FyWEn70XJYSfvRcmRC7oXJUcu6F6U'
    'HLmge1Fy5ILuRcmRC7oXJedByftQEh8HHpR8g0wug5J3ouQ6KHknSm6Dknei5D4oeacVZ3jm96Lk2BG7FyVHpvdelByZ3ntRcmR6'
    '70XJkem9FyVHpvdelByZ3ntRcuQn70XJkZ+8FyVH3H0vSo64+06U9CPTey9Kjrj7XpQccfe9KDni7ntRcsTd96LkiLvvRckRd9+L'
    'kiPuvhMl69Due1FyaPe9KDm0+16UHLu096LkyE/eiZJlVP3di5KjVu1elBy1avei5MiZ34uSI2d+L0qOTO+9KDkyvfei5Mj03ouS'
    'I9N7L0qOXNC9KDl2ae9EyTz8yXtRcviT96LkyAXdi5KjVu1elBxZtXtRcmTV7kXJkVW7lz859nHuRcmxS3svSo5d2ntRcviT96Lk'
    '8CfvRMkwvKB7UXJ4Qfei5MgF3YuSIxd0rz69I9N7r5reEePci5LDn7wXJYc/eS9KjvzkvSg5PPN71fSOtftelBwVVvei5Kiwuhcl'
    'R4XVvSg5KqzuRMk0Vpx7UXJEi/ei5Fi770XJsXbfi5Jj7b4XJcfafS9Kjuroe1Fy1GDci5KjBuNelBw583tRcuTM70XJkTO/FyVH'
    'zvxelBzVLPei5KhmuRclRzXLvSr2R37yXpQcWbV7UXJk1e5FyZFVu1f95LCT96pmGf7kvSg5/Ml7UXL4k/eyk8MLuhclhxd0L0oO'
    'L+helBx7i/ei5NhbvBclx97ivSg5KqzuRcmxS3svSo5d2ntRcuzS3ouSY5f2TpSchnbfi5JDu+9FyaHd96LkqMG4FyVHzvxeO2Ij'
    'g3EvSo4Mxr0oOTIY96LkiLvvRcmRC7oTJc3YfXhGyd99/vnnz58eAf/P/3j/f3/+8nX7ehdqj/X9L0nt4QP8Jak9/IS/JLWHL/EX'
    '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'
    '3cfRq/s4enUfR6/u4+jVfRy9uo+jV/dx9Oo+jl7dx9Gr+zh6dR9Hr+7j6NV9HL26j6NXD3H06iGOXj3E0auHOHr1EEevHuLo1UMc'
    'vXqIo1cPcfTqIY5ePcTRq4c4evUQR68e4ujVQxy9eoijV49x9Ooxjl49xtGrxzh69RhHrx7j6NVjHL16jKNXj3H06jGOXj3G0avH'
    'OHr1GEevHuPo1WMcvXoMo1fHrovzqCnOo+Y4j9rHedQS51FrnEdtcR51iPOoY5xHneI86ibOo27jPOouzqPu4zzqIc6jxtGrKY5e'
    'TXH0aoqjV1McvZri6NUUR6+mOHIlxZErKY5cSXHkSoojV1IcuZLiyJUcR67kOHIlx9mtchx3JcdxV3IcdyXHkSs5jlzJceRKjiNX'
    'chy5kuPIlRxHrvRx5EofR670cdyVPo670sdxV/o4erWPo1f7OHq1j6NX+zh6tY+jV/s4erWPo1f7OHq1j6NX+zh6tcTRqyWOXi1x'
    '9GqJo1dLHL1a4ujVEkevljh6tcTRqyWOXi1x9GqJo1dLHL1a4ujVEkevljh6tcbRqzWOXq1x9GqNo1drHL1a4+jVGkev1jh6tcbR'
    'qzWOXq1x9GqNo1drHL1a4+jVGkev1jh6tcXRqy2OXm1x9GqLo1dbHL3a4ujVFkevtjh6tcXRqy2OXm1x9GqLo1dbHL3a4ujVFkev'
    'tjh6dYijV4c4enWIo1eHOHp1iKNXhzh6dYijV4c4enWIo1eHOHp1iKNXhzh6dYijV4c4enWIo1eHOHp1jKNXxzh6dYyjV8c4enWM'
    'o1fHOHp1jKNXxzh6dYyjV8c4enWMo1fHOHp1jKNXxzh6dYyjV8c4enWKo1enOHp1iqNXpzh6dYqjV6c4enWKo1enOHp1iqNXpzh6'
    'dYqjV6c4enWKo1enOHp1iqNXpzh6dRNHrmziyJVNHLmyiSNXNnHkyiaOXNnEkSubOHJlE0eubOLsVts47so2jruyjeOubOPIlW0c'
    'ubKNI1e2ceTKNo5c2caRK9s4cmUbR65s48iVbRx3ZRvHXdnGcVe2cfTqLo5e3cXRq7s4enUXR6/u4ujVXRy9uoujV3dx9Ooujl7d'
    'xdGruzh6dRdHr+7i6NVdHL26i6NXd3H06j6OXt3H0av7OHp1H0ev7uPo1X0cvbqPo1f3cfTqPo5e3cfRq/s4enUfR6/u4+jVfRy9'
    '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'
    '48fNf93NHZsfThLzqXC2dt23D6HOERY9OLawkCjDkGtOys6MP80MNr5H41MqIxtfhysL6crqwQcV7g0K9zQl+oF8dUq/4sYTTOYN'
    '7EZoNrykDM4O5H4io+d7lHwh2yzZSraSrWQr2a5Ptk8UibCEyrTcxJ/18h4a2wOyTX28pMNU4fiJkXLHkho1MdJMuUDSp+PhpkKb'
    'i11dEqTvyttz61Omf4H+hoR/w9S/yN6/z7ZFtpVtZVvZVra9ANsOGgkaCRoJGgkaCesbCaNkK9lKtpKtZLs+2U76CPoI+gj6CPoI'
    'F/ARNrKtbCvbyray7fpsW3uNBI2E12okZHgbmc6DzsM1OQ+1yM6ys+wsO8vOV8jOTadCp0KnQqdCp2IFp4JdoHOfm0e5WW6Wm+Vm'
    'ufnquNkMn9wsN8vNcvP1cfNWx1nHWcdZx1nH+Qod553sLDvLzrKz7HyF7LzX19DX0NfQ19DXuDZfY7eTm+VmuVlulpvXP1WyUwnL'
    'trKtbCvbXoJtD7KtbCvbyray7dX5Dke5WW6Wm+VmufnauHnfyc1ys9wsN8vNV8fNSW6Wm+VmuVluvjpuznKz3Cw3y81y89VxszeM'
    'ys1ys9wsN18fN3sfqdwsN8vNcvP1cXOVm+VmuVlulpuvjpvtsyw3y81ys9x8fdw8yM1ys9wsN8vNV8fN9sCXm+VmuVluvsAp7P0k'
    '28q2sq1sK9tegG29Q0S2lW1lW9n2Emy7lW1lW9lWtpVtL8C29iqWbWVb2Va2vQTb2qtYtpVtZVvZdmW2rbXrNk85CX1dzjKzL+SF'
    'bMtuxqvr3KJHWPwyN+79+lXuTq/yiSMzKY3D8j/Vp3V+QusX1dP8/J/v370b0vt/+/Dx43cfPm8+P/LjzxmjracEYs83VYOqQdXw'
    'xusef/uBf/zL+3cnLvzvnz7cvn/34e7uw83nf//b4fNhP8fah9P0eIq10zQtj/Xm5tpDY+tilUDu8O1qW/69rQ7Lx7blCiiRnY4o'
    'tqn/9ncZX0t8PA6r3h08u/t/s7uDz7Sz/Gb83//hRB79+//14f9+ODxCH//8nj9+3Nz9ZbvZ/fX9nza3m/2Hu98wx9ztzk9+Mo/9'
    'sz9J99MOXpichww34B7+hX6Alz4XusXXrr+6Lb7QK5m7ce1bopdvwE8suQevZU7jhO6I7seJDC9zSv3B4WXM3fJTFmmcu+j9wdFT'
    '7dDocfnonFNZPrq0PDOPv7v5ePPp5vOfD5/+9vE3PJamxwTUXgGlgFJAKaAUUAooBZQCSgHFBNRBAaWAUkApoBRQCigFlAJKAcUE'
    '1FEBpYBSQCmgFFAKKAWUAkoBhQRU6RRQCigFlAJKAaWAUkApoBRQTEAlBZQCSgGlgFJAKaAUUAooBRQTUFkBpYBSQCmgFFAKKAWU'
    'AkoBtVhAtS81UE9diNrSckEyFrDBZ9Clh4y9TPefX8N47LrdOTv/Ab24Wr+f9fRXwN5AGWq7GryX0LX1BsLadOVeQrQ10CUa91S4'
    '288u8PMplnUFSGkjuN+w1Cmh0ZnvtN3c8z+6PXfP+Et5qI9tRgc3IzcjNyM3IzcjN6NvvRkd3YzcjNyM3IzcjNyMvvFmtO/cjNyM'
    '3IzcjNyM3Iy+9WaU3IzcjNyM3IzcjNyMvvVmlN2M3IzcjNyM3IzcjL71ZtS7GbkZuRm5GbkZuRl9682ouBm5GbkZuRm5GbkZfdvN'
    'KLWnzhn1/fLNqG/Lz4/3UwJjwTOA8/l1AufdwZn7Vhs4R7/8tw19Xn50LoGxYLPvpgLO/VcwtoEeAUCcAMHBjhC2MwiO27sf7tHJ'
    '2Eq3fPDQxqWD8wk1pjX6jmmZfmpQKyWoZdj3135k40eolUb2/W1kv3dgLRe6oUJt1cGWESmx8UwL45YUVBumITOt1z23YUNK43M/'
    'Obcm5vRlarRhQ9fR7ggj/EAPf0Ot9C80+htGiFKjPSQaDQxmN/4zNp2Aonp2wc53qaCxCpytpzVLu1SkgX5g/VilY50qRjJ8GNG3'
    'T0Nmw1mcVRMZPmT07QMC8jS8opYfiTxMzXVEw9uEhs8R1sPDS0pseEbDS2XDQTeU3A1o9JjQ6AxGp7lQ9+HRBfVlaeS7e4RgGciv'
    'rH0+R4eYh0dP4LtPKwj0qqmzXZ0eHl0edT0Ouh66Hroeuh66Hroeuh66Hroeuh66Hroeuh66Hroeuh6v0vU46nroeuh66Hroeuh6'
    '6Hroeuh66Hroeuh66Hroeuh66Hq8Rtdj6HQ9dD10PXQ9dD10PXQ9dD10PXQ9dD10PXQ9dD10PXQ9XqXrkXQ9dD10PXQ9dD10PXQ9'
    'dD10PXQ9dD10PXQ9dD10PXQ9XqPrMQ7na629WrvsV98Cewre0jqX2C2w125pnft+3R7YJw3dra6hV++ynelfoL8h4d8w9S+SxPfZ'
    'dpJtZVvZVraVbS/AthvZVraVbWVb2fYCbLuVbWVb2Va2lW0vwLY72Va2lW1lW9n2Amy7l21lW9lWtpVt12fb/VM1CS3V5RX9pV+p'
    '6h2M7dM6DNpYWXRrsGy5ZFhWDMuop/48Zchz4+cqIGcqzVANXi1fF5nfn8Sjk9hJHH0ST05iJ3H0SbxxEjuJo0/irZPYSRx7EudO'
    'OfHCSfws1N3/vgXqEva3QH0n6t8A9b2ofwPUD6L+DVA/ivrlUc9PpQT6Chr3DOMqydo8dSBZW99KYvf+qxx9la/lVU6+ylfyKofj'
    '+SpcujK1b18NQyBP7bKvxwoXK1yscHmzFS557GRb2Va2lW1l2wuwbbJ62+pt2Va2lW0vwLZZtpVtZVvZVra9ANv2sq1sK9vKtrLt'
    'Bdi2yLayrWwr28q2F2DbKtvKtrKtbCvbXoBtm2wr28q2sq1sewG29d4l2Va2lW1l20uw7SjbyrayrWwr216Abb3lTraVbWVb2fYS'
    'bOstd7KtbCvbyraXYFtvuZNtZVvZVra9BNt6y51sK9vKtrLtJdjWW+5kW9lWtpVtL8G2B9lWtpVtZVvZ9gJse5RtZVvZVraVbddn'
    '26mTbWVb2Va2lW0vwLb2t5VtZVvZVrZdg23/+YF3m7sfN8f7F5d9/dbuc7PdcOVmuVlulpuvj5vtnSs3y81ys9x8fdxsp125WW6W'
    'm+Xm6+Nm+/LKzXKz3Cw3Xx8328VXbpab5Wa5+fq4efDWd299l5vlZrn5AlVxo2wr28q2sq1sewG2nWRb2Va2lW1l2wuw7Ua2lW1l'
    'W9lWtr0A225lW9lWtpVtZdsLsO1OtpVtZVvZVra9ANvuZVvZVraVbWXbC7DtQbaVbWVb2Va2XZ9tN0/0d0hpHJazTJ/WOVvQ5sbe'
    '3v3wdX1xTsMcdc1N1Fkumv1AX+A7m2OL2Q80OlGnRD8A/0KexsemUXEaOY1ePo2q08hp9PJp1JxGTqOXT6PBaeQ0evk0Gp1GTqMX'
    'TaNhOMXTT3V7aqku9sXGsnxq5AymHBl7mal8H8YqjOeAcRTGc8A4CeMLYRxz13VP3lzVg5zB3N7z0Nhal+cMSFeRAr63LYc8T911'
    '5Bcqyy/UjPz2E8uz/MIwJ8Fm/f/KxteRjR9hvmNOnMzlCzr2/X2C+YsynSd/8cePm7u/bDe7v77/0+Z2s/9wd38F5hEmMkqfoBbN'
    'VIvWCVr0HUwCzKYJ/+3D5//a39wbnvu52fTw8DKn1h/q55G7uWd5aHSpc2T18Oivp/U91k+drC/ry/qyvqz/hlg/yfqyvqwv68v6'
    'b4j1s6wv68v6sr6s/0ZYv3Zd99TJqzRNgPXb8rHLU/JdI2cM0A4BvnfswNjl5QZpGlZJKaFdinRCv3R389+WR3Rj6wcwuHRLB6ex'
    '5mF5lUY3e0blocHLHyOnBvf2vrLTIWVkWqOWgWmHiWmNIY9Qa/RwPMNnmFs9s1pmXPe0Sleh1oCnW/q8sjbpvs3pnCe1T0rDsz85'
    'PveTczz+tFKDFU8n3VLpBxr9wAjFY+5pbdtI1Sb9CyP80Q2e1UrdUGm5HT221NrK5XZ9qvQD45nuOZj9QO3oBwqQ8fevUnhcaqfZ'
    'M50Pjh4qkPFpHDs0eiCjJxCspIlcRpFPeykZPTQyegQI5lRJSJYbGd0X8OYLmlWlTCjcyxMZXclz13F8fuD5xKUluXRk9Nwynhk9'
    'PBYCHwyBDYENgQ2BDYENgQ2BDYENgQ2BDYENgQ2BDYHfRgh8NAQ2BDYENgQ2BDYENgQ2BDYENgQ2BDYENgQ2BH4TIfCTR90NgQ2B'
    'DYENgQ2BDYENgQ2BDYENgQ2BDYENgQ2BX0kInAyBDYENgQ2BDYENgQ2BDYENgQ2BDYENgQ2BDYHfRgicDYENgQ2BDYENgQ2BDYEN'
    'gQ2BDYENgQ2BDYENgd9GCDycMQTOy8O57t7lvI+O7bu0fCy4t6Bv3fKx0/JnKLkC2wCE1t3y8PP0f8A2IHcytHXC8Novj2qHVhcP'
    'nrrcrxICnwbPzokHBg8ju2Ch9HA8i6pO41lUWwb4PCyKPBFVYuN79nsrjfon5kK0zL6/wShydpHORuWNjWfv9zS+nDt2nI+yEv0A'
    'jRSnSuO4Aj8wt9xmPzBO8AM0PJ69WWL+AzS0nHoYKcLfcFoVNFKs9APDAIKm1NKEhueODWffPsd5c8MLG44eZugaGt5GMnxM6DWN'
    'E/mpp9CMADkfP80MR1Ms9/204l02/dSxq29GNHwu5np4+DCShymzl17NDK8DGt7Qw7RKcC8DIo4yJuTl5JKRJ0LcmWlOus/4FhWN'
    'bitG3Y/dlZTbUzfkZXBDHkniprx8bA8SkgkkJFO7bFJ01mumbva95OH9lzr4Ul/fSx19qa/vpU6+1Nf3Uve+1Nf3Ug++1Ff3UvvO'
    'l/rqXurwVEjDkmfDKsmzfgLPAJKTFSQnW7c8Mdjq8rrf1pb/tqFfvBC6MYGxYNF0U/nmScQ0LH/eDGp5ST1xD54XJTJBee6XrOe4'
    'POs5W0L14OCalg+eLT99YYo0p9lymbNUCXcsP9fDKt5C85ddg/nOEeY7MxzPvr+N7PcOCVYtV5i/7AY2PiWYf+2vqiqa5mv7ufn2'
    'LWp95/QLreP8UmK3dj0tTT7XSv9C666sYvckaugHGs30DgP9wERTw/3VVR0PuIh4CFN1PJNOzDVqOjFPQ2YJv4SGo+R8GXJBw9Fr'
    'Og2va2Yf64iGjw3VqafEhmc0vFQ2vF1JyXc3kiLu1PeoQLxHBeLkV84WGj44uvZgdGmk2P9lhdZPjC4d+e57k/C+rzPo6+jr6Ovo'
    '6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jrhPR1Rn0dfR19HX0dfR19HX0dfR19HX0dfR19HX0dfR19HX0dfZ2Qvs6kr6Ovo6+j'
    'r6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6OvE9LX2ejr6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6OuE9HW2+jr6Ovo6'
    '+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6OiF9nZ2+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr6Ovo6+jr5ORF9nqk/4Ohn4'
    'Gblf7mcU8L0lL/c+CvCW6nLP6iT58/KxwCdJBfgkw3KPIi33wk47PxkL/Iwyvdz7mIuZYUxeejoextgdjOETjMkzjGlLheNhDDyk'
    'VWPOWb07N35izzM7N+fG07Am95V+AAZ/PQ3NSs4wWoRx0JedjH5goDE1/A0tjzRapLFcyjTSameKtOYiISJT82x64+HhrRtYrDKi'
    'aAIp8jKUhoIP9uxjB4OPng0vLPjo2PCeDQeiMk1E3uYus+DjUcHaFKwKVgWrglXBqmBVsCpYFawK1msWrIOCVcGqYFWwKlgVrApW'
    'BauCVcF6zYJ1VLAqWBWsClYFq4JVwapgVbAqWK9YsG4OTwhWJBan9s0F4BWKr/uQH4X8wpBvOyG/NORJyC8M+b48DnlK47D8T/Xp'
    'DGfvHxjbHv0JNf5PaPF/whD/J4zxf8IU/ydsov+ElNv59rH19ibQgAXtY+dwHB8cW5h7OFU4foJuI2zakSbYxAI2mSh0fFu16QV0'
    'k5/j7vUrm3UNdnt4TqeEtY2uRL23RH9Dwr9h6l/kvd1n20G2lW1lW9lWtr0A246yrWwr28q2su0F2HaSbWVb2Va2lW0vwLYb2Va2'
    'lW1lW9n2Amy7lW1lW9lWtpVtL8C2O9lWtpVtZVvZ9gJsu5dtZVvZVraVbS/AtgfZVraVbWVb2fYCbHuUbWVb2Va2lW3XZ9ves2Sy'
    'rWwr28q2l2Bbz5LJtrKtbCvbXoBt6/TK+v28+o6vMrPMLDNfJTMnyMy5nJXKN1K5VC6VS+VSeXQq30rlUrlULpVL5dGpfCeVS+VS'
    'uVQulUen8r1ULpVL5VK5VB6dyr0/6YL0fLZZkKb82Ev1hqbX91Kbd0C9wpfqLVOv8KVmX+qre6nDUy8192X5zeitLh7b92Bsy2Ds'
    'uHwS9uB29j6Dyb18bF0eo3ctNzB2Wj62Lq927gawcDO5Ib4DvkY+QxX17d0P9y5lHYfWFg+eurz8m6dU8/LBdXbNPTC41Wn54Ckt'
    'fuY0zt5a/dDgYYReSc+8m9qYNzQLy9z4xm62n73w+Ww3yS/1bv7+D+/fnZbxv/6w3Xy4ff/uw93dh5vP//63w+fDfmXPhV8B3xp0'
    'dTK9M75P9AP0gvaupxe0N2oDkSvCU0O3cp+GFzQcXZ6exolc4p2mjgzPXYfuie8GgkzOA0Em97mh4f2Ihk/op07orZYxo7vWc3lU'
    'ST510iBNyxVJ6ZarThR21OWqs3bL1WEFyrfVYfnYBlTRMK6SGcpTt9K5uSvJIs1ddjqbVWE7/2yYOTe+TDCr0n2brM0fP27u/rLd'
    '7P76/k+b283+w91vVnzfnvnJPNJMUQc1RR4ylQhUtQwstTRPerOaotarS14VKHNmGWP2A6m+KFO04ANzE/7d5u7HzfG+eJkLnh8a'
    'XdpcTPXdzcebTzef/3z49LePv1lHaS7XNR2/5Dz15dbeRO5Drr99cch1ny8OeS/kl4a8CPmlIa9CfmnIm5BfGvJByC8N+SjkF4Z8'
    '6O0tZW8pq7KtyrYqe93eUj+xbZFtZVvZVraVbS/AtlW2lW1lW9lWtr0A23ongGwr28q2su0l2NY7AWRb2Va2lW0vwbajbCvbyray'
    'rWx7AbadZFvZVraVbWXbC7DtRraVbWVb2Va2vQDbbmVb2Va2lW1l2wuw7U62lW1lW9lWtr0A2+5lW9lWtpVtZdsLsO1BtpVtZVvZ'
    'Vra9ANseZVvZVraVbWXb9dl27GRb2Va2lW1l2wuwbZJtZVvZVraVbS/Atlm2lW1lW9lWtr0A29rfVraVbWVb2fYSbGt/W9lWtpVt'
    'ZdtLsK39bWVb2Va2lW0vwbb2t5VtZVvZVra9BNva31a2lW1lW9l2ZbYdc9d1T54l68HFm31ZPrbW5cxMGL+A721p8dg8dZdl8Tmm'
    'rYyZa0ZM1bXKmHkYB8iclY2vIxs/wp1iSoxpO/b9fYLMX6bzMP8fP27u/rLd7P76/k+b283+w939FZhHuAWUPrEP1FwgudUJklsH'
    '6XP2rt1/+/D5v/Y394bnfm42PTy8zMmad5u7HzfHe6O7uWd5aHSpc2T18Oivp/U91k9PdX5MbbG+7dK0mO263IbFY/uuWz4W7FJ9'
    'X8GOtvy3lQa+dxzAddbLv7e25Ti0XMHYtnxsW75TdgO4qjtPQAWAuA8876xcezBGbKupgH6C8dzcWpobPzYY/8F4LsPx8HnqBFXD'
    'kOGuTsOnPtMPFPqBgW7nmW7nDX6gQZQaDGNTN9GIrnT0A/2ZQsAHJcMpBJnQ8MyGz2m8ueGFDB8qElN1GmY0yb6eItGnztnnPi/X'
    'GdMAxo7raJIGxg5AvwA9UDKIyPtxjej9pIvAM7QGdFFarknqsIp+SR3QJCmto3VaBppkAL71GfTL72/vfrgXm0xdBoPLrIp6YPAw'
    'gsFTWvwYaRxGJlhKDwXUAL+f2Rzzi2XWoE/rGvq5h+MLFIwDHM/wbPD5W03QJuuhTTatK3i78TwC+VwJjL5N8ANDB/UxzXiUNkJ9'
    'PCWqj4fVcyrTypZdgj96fh9amPF4SsVWpmL7uUTAItH7xPATzWU0fACGYxrnXIOHRp8epVs0+uf/fP/utFH//P/+5+f94fb333//'
    'xXue1/upU++r99X76n31vnpfva/eV++r99X7r1Xvdxv1vnpfva/eV++r99X76n31vnpfvf9q9f5Wva/eV++r99X76n31vnpfva/e'
    'V++/Wr2/U++r99X76n31vnpfva/eV++r99X7r1bv79X76n31vnpfva/eV++r99X76n31/qvV+wf1vnpfva/eV++r99X76n31vnpf'
    'vf9q9X5S76v31fvqffW+el+9r95X76v31fuvVu9n9b56X72v3lfvq/fV++p99b56X73/avV+r95X76v31fvqffW+el+9r95X76v3'
    'X6PeH096vz1Rv3+iqOUaqJ+7v/uBjX8cWiVipSwfnId6DWJl9trqh5VNWj54LIsfI5+4BNJb7uAHZlXTLOPC67a7SreZRn9Dgxer'
    'n/R+JfRWEF+l1mc0vCQ2HF7ozYa3zIajm9FHdjP6mCsbPqLhfWLDEZAj2+O6keCeUyXPnnNX0fChsOETGj6iZ+/zgIb3TIqg1ZRn'
    'TZuZ4Y0NH9AkqCOZ77mxOTOMaAKPFU2CqRvYcPRTp8QehuE+jeStlopoqdS+R8MR7oXNmcKkd2m5Q8PRjCwj+vaac2LDexY2sG8f'
    '2LfPeSkPBiVD7UgIM0eoD40+6cmKRqPvntsJHhp9mosdGt0/EjkNnZGTkZORk5GTkZORk5GTkZORk5GTkZORk5HTE5FTMnIycjJy'
    'MnIycjJyMnIycjJyMnIycjJyMnJ6InLKRk5GTkZORk5GTkZORk5GTkZORk5GTkZORk5PRE69kZORk5GTkZORk5GTkZORk5GTkZOR'
    'k5GTkdN85DQMJ026faIj3FCWdwsb++VRVu56MLYsH5tApNcjZm+IqsuQ0KKeBXqGA9jDjGjfOC07uEqJeKgldWx4z4aXxyb86IR3'
    'wr+lCb9zwjvh39KE3zvhnfBvZMJ/yX505YkJ3wrozFuWdyhu4+KJ2Q1peTfjIYPuwCPJ7DyWROqqMJ4DxiaM54BxEMZzwDgK4zlg'
    'nITxHDBuhfEMMKbNUzCOGTzW+Nif2l7uT02X+1O7y/2p/UX+VDt+uYjjqdtNyvLbQmoGY3tw68QAbpJI4CYJcJtFXzswFjzv3K0e'
    'sw31K2yQD8ezCw3u37Bxf3oVp5fTa73pVZ1eTq/1pldzejm9VptebXB6Ob3Wm16j08vptd702ji9nF7rTa+t08vptdb0Sjl9m+nF'
    'psw1T4MHjqd1eQIH36Zh8TfnbhrAwbfh65uI77/67Kt/q6++99W/1VdffPVv9dVXX/0bfPVf6lpb56t/zqu/D6Nq+Sww7oTxHDDu'
    'hfGFMNbDCaUn/eG2vOY/T8uLsPqWwNi8fOxUwNjlv63U5b+tgN9WpgSm6fLnbcDtapWMXT71uqEtHzvV5Usw92Ds8vMiqYBnqOPy'
    'scvnQ+oTcrhO82dE42uX0fgGHb1UChzfmKOXoANYJugYznz/Hz9u7v6y3ez++v5Pm9vN/sPd/ZWR5vqGPPnJ2RM2Cz5ZYLOmHnZG'
    'qrnQD4zwAz3tHzW3Jc02a5orDp79QJ3gBwb4SH03rtgLqB9R95LSdWx4XrOVCurRkae5FTDTuaKB0RPpipFzAk9S2tc9NO7LsklZ'
    'pixTlinLlGXKMmWZskxZdgWyrK/KMmWZskxZpixTlinLlGXKsm8ty3ZdNz15Kn95IzAoBdLLpcBDP7iWx7O2Tx27KH2/XFP1Bei6'
    'CnRdXUWrzXbxfenLzOMaL57pr5U0VZ66l2uqB8cu16xQW3R1DuO58XO6YGb8MA5Me/VMG6W2tvbqXnIW4vna7jfj//4P79+daOd/'
    'ffi/Hw637999uLv7cPP53/92+HzYv2aNmPsGP0Dvy+n71WXrXAPO8+lcLFt7qEJnQ+LzydbWn0m2zn4gtWvSufksdyvMiMVxNbFY'
    'G7sUIJ0vbbtVl6nL1GXqMnWZukxdpi5Tl12FLtupy9Rl6jJ1mbpMXaYuU5epy761LtsPJ8Kqbyhx+9MPbm/tBw9v7QePb+0Hb97a'
    'D57e2g/evrUfvHtrP3j/1n7w4Y394NzF+8H3f0IK/xPSMf5byPHfQn5rbNe/tR9c3hq9v7U3nN/SGx77R5sYfvmP9+9Ov+F/bG4/'
    'f/GSn36+33xkgf38wBeU+v7dzefvj4fb2833z/zU8/7yCdnvPmxvN5+f9ZHn/c1/6frf/T+/++7D/vC7/++Hw9334IPluR+s9IN/'
    'P+fGcxGpf//nzacPt8//4AJYF+VCVs2iPPI9dXz/rz9sN8+A4J+ffNkT/EuXF7zwR7+gvPQLlky5R9JCv/2fTiTz6fC7777f3H6/'
    '1N7/x7+cSKqdZtfHzceXfHTBS3n0i/rp/X+fXRmLPvnSJ2gnztzcfti85KMvfYZl/PfEV5SXf0Vb8BX3cy6//Pff//15H/rzD9/f'
    'nID8ePf8Xf1Xow+fbm5/fP+Hm9vbD/ub23sE3s1lSec+du/f37/r+l/G/uOfHvy+P90e7g6fv3//Hze/+uG//sfTN31JPf2Ynv35'
    'n65F/jE/+/M/1Zn82D/78z+dZ/2xPPvzP73BH+uzP/9T2+sf25yarV/aRjwh7q5VeryCrUzKw5R3b/Y+Yi84e529Vz57H+np4+x1'
    '9l7x7D2Uk05c1xb6fz//79Nv/vBfm+9PgUMsX+l5j/7tvannPfeLza2fQoXf/TTyd/2zPlWe9am6gqf19/HtG3hgC15fDCvtZT/k'
    'miy5l/2Sc1l7C5bKwk9XWN28vAz3zLbbAuCj+Hcv/SnX5AO+9LeczVBcsOcs/nx54efrIk/v5/985Mnvy7OsPFOeKc+UZ8oz5Zny'
    'THmmPLsmedYrz5RnyjPlmfJMeaY8U54pz65JniXlmfJMeaY8U54pz5RnyjPl2ZXIs23tunHzhDxbqFnufW2Z0NeeWUDd/43TOr9x'
    'c02/cVznN25X+dpxWOdpd+s8bVvnaffrfO1hHRDqOk97XOdpyypfW7t1nrZf52nTOk+b13nalb52HWzHdbCt55+3+75Lab/O1+7W'
    '+drtKl+bu3We9rjO156fxg9fuqqkdb42r/O1/Spf262DbXdcB4R1Np39Ogy2X4fGd+vohP062A4rvbJ1hOh+HTU+rfO1bZ2ZMKyz'
    'HIZ15Md+pa9dRzbv14kdhnWoZr9OKL1fJy7brBPz7tdZZZt1Yt7DOny7WeeVHdahms06r+ywzirbrhRK767IlCvpSh7m0OPt+Kpz'
    '2lecIH0is3kNKa2ZlEHXfvlf/vPz/nD7+++//9L/i3zBv3T5l//pBU/x68RFfvYn6yMLYTwTq3/bEou4S+DbJ9Mvkxz+9jndC+Vi'
    'r58O+md/spydgvqpS8eyvCjuHFvqiznsTIR0Ll45V8HMy75nWYeey5LN2Shj3XV/b0suO7Wp2lRt+o1rSlwILoRrWQhbF4ILwYXQ'
    'DaMLwYXgQugG/WsXggvhtBAmF4ILwYXQlfx6FoIppCs7H3pVqajXZCx/E0/6NVHiN09moU+2xwi8l8AlcAlcApfAYxJ4kcAlcAlc'
    'ApfAYxJ4lcAlcAlcApfAYxJ4k8AlcAlcApfAYxL4IIFL4BK4BC6BxyTwUQKXwCVwCVwCj0ngkwQugUvgErgEHpLAmwpcApfAJXAJ'
    'PCiBq8AlcAlcApfAgxL4RgKXwCVwCVwCj0ngWwlcApfAJXAJPCSBwxunJHAJXAKXwCXwq1HgOwlcApfAJXAJPCaB7yVwCVwCl8Al'
    '8JgEfpDAJXAJXAKXwGMS+FECl8AlcAlcAo+ZxEwSuAQugUvgEnhMAvdGHglcApfAJfCgBO6NPBK4BC6BS+AxCXzUA5fAJXAJXAKP'
    'SeCTV6pJ4BK4BC6BByVwT2JK4BK4BC6BByVwq1AkcAlcApfAgxK4VSgSuAQugUvgQQncKhQJXAKXwCXwoAReJXAJXAKXwCXwmATe'
    'JHAJXAKXwCXwkATeP1VGmLv3/2Nz+3mWB+R8OV/OX43z3+xuUd//z5vbu8Off/j+5vRNH91q4m811a3Grcatxq3GrcatZt2tprnV'
    'uNW41bjVuNW41azbSEEDza3Grcatxq3GrWblrUYDza3Grcatxq3GrWbdraaObjVuNW41bjVuNW4162415mrcatxq3GrcatxqVt5q'
    'Brcatxq3Grcatxq3mlW3mrJHByOftwPI3s9hb1nX44DS1gxtHaQtaUvakrZi0dZR2pK2pC1pK9YtqkXakrakLWkrFm1VaUvakrak'
    'rVi01aQtaUvakrZieVtJ2pK2LMJYm/0kr/l2OtrrUpAUJAV9OwoqnRQkBUlBUtA3o6Cm7S0FSUFS0DekIC1sKUgKkoK+IQUNUpAU'
    'JAVJQd+EgjZj1/fT+Y9x/+ojzztJfY5z4N/iDPeCv7kqWb7s75/jDPfLnuAcpLvgCVYvXXjpM7ycr1/6BI/zddij178iv23tumH3'
    '3BtX731Rnc70RcP+XE80nuuJDud6ouFcT3Q81xO1M33R2J3rieq5MNqe64s25/qisy2Rs83ss03Ic82j4Vyvv+QnvmhWWN6f2dsz'
    'fVHpz/RFMGZ+ngxc+jBTd0UP08YrepjxeE3ITNeEzOGakNlcEzL7a0Jme00Ps7umh7mq13RNq6m/JtIr17Q3lXIuHVHP9UXtXF80'
    'nOuLxjN8UTt23W6eLf5w+PjxFGbkYcEb/mXsOC0fO6WlY1Max8Vj+zRjfv7+9u6H49eDpy73ywenmpcPLl1bPngYweApLX7mNA5j'
    'XuiP/fxWSq1ofEsTG5/h9089Gj+MAxmfUunY+Dqy8ePExrPfm3Lqljp2v7zgVuAHphF9IKU2s7D/7cPn/9rf3B8+oOG5dMvyKT9/'
    '+ThHMg+Nzl2ay36MXzbszRNMmdpy9kvT8rF9W87A/VQXjy19Xj4WfG/NbfnY1i0eO8s1D42t/fLdpSS2JPLcC5n/AFtDXZ/pB/qO'
    'fgDyQD83u2eJI9MPTJl9oM3t3vMfqIQ85lTHDHnMHSash9M83z5FHoAQct8AIaTli7ySRb6cPGoFhDARQlhOjC1365DHsHxsXv7b'
    'Ul9m5sMfbj59uvn8z4zW4Xb3l83n/Ye7wwJ5VEco12peV37101XJr9ngYW58nRn/x4+bu79sv6Ql/7S53Xx5O/fX+9xm9uQn8wiZ'
    'Ow9pZY1YO8jcle5vtTX4gSlB2Vrqqjp3nFv8D+vc3DIZ3s/tbDPD53YbKLofHj4l9O1TRshMY1lrEz+9pPL8Lf+p0RnEIqU2NHpi'
    'o4EMKm3OAPru5uPNaSv68+HT3z4+QW/31dCoGlINqYZUQ6oh1ZBqSDX0ptXQpBpSDamGVEOqIdWQakg19KbV0EY1pBpSDamGVEOq'
    'IdWQauhNq6Gjakg1pBpSDamGVEOqIdXQW1ZDrVMNqYZUQ6oh1ZBqSDWkGnrTaiiphlRDqiHVkGpINaQaUg29WTW061L3RKbstKtW'
    'sAMPYOzy5kSJND2CrW9KP7Dxje3bZejgPt/DfRju23Nb0GxrHTa+75gumFVXdJ8/V/P02W2sT3Tfo9tYKXTfy48s7ZSfCHTa8i4y'
    '51muM1O+b3Q8k8I9pIR+QtLzpIgGOH5k4ycYKnSwO1dpkEJoI5+eSsaGW9Qw2Zs6vDjrBD+AZS9s5HMKYsfHlv/g8nf5u/zf6vIf'
    'FfYKe4X9axT2R3d2d3Z39je6s+fO5e/yd/m/1eWfFPYKe4X9KxT2Obu0Xdou7Ve2tNuxyyldm2if+x39XMnRgzUgpaFyl5rrQIaX'
    'uVt75oYXNHzuYR6sGsmkxuSEC6h2uQ/L/cmTnTxOnudOnt7J4+R57uQpTh4nz3MnT3XyOHmeO3mak8fJ89zJMzp5nDzPnTyTk8fJ'
    '89zJs3HyOHmeO3m2Th4nz3Mnz87J4+R57uTZO3mcPM+dPAcnj5PnGZNnrF23fSo9MXu/+UtrHs5Rx/BQu5BU+SHtbi6R/tiHZttP'
    'PPahe+0J7r+N4tu4ordRfRtX9Daab+OK3sbg27iit7H/VpWLz38bX/+E1Pr4P6GE/gnTdJrQT9XJ5W55t7u+65eP7cvysQ2MBd0E'
    'S17+vKWRrn+gm+DyWK2rI/jeqYBugiPoJghoPoPpn9ubORg12xVyrgx5DscFvfaGZ38S96nrHuOZp0oq+y4B7gA8Mw2AD8DYHnQX'
    'HQEngXXLOoauefAQHjvI8NhBn+AxhbWPNbDnme35ODe+r2w87G1aKV/Bg5wtw16lGfJhrfDYBzwmwvCZ750622YUHrM8rQB68nPu'
    '7Op8X9J+5bOls7PuXGdI5ufd7Adqg8dd4ZHd5xxr6V50DmaBKZ/g0ZzZU0oPNhKd6mzIlE864Kl6jdwv19kZ7O1914F4A3QZH0AM'
    'kQsYCzRDP67S6byAuKuQbusTwGwindnbOnEXif2A1qsAswZ+WwPvuFXQSZ7kFbtppTgR2CQZPMPyd0x7peNGGLO+xKw+znB8g/oY'
    'fn+Dv3eA3w/1boHxTO2ovod6Oq/cGGWE3z8Oq8YbDeLTMr2rgcVXA3yeIcN4I8N4g62vU3wC72pIMHrI9FaD3EPlnRv9wESb5Uzw'
    'L/Q9/NE9vZmhdD0N++j9FRWiVCZ8f8VAPzCt3msg0bCv0A8Ma7dFyvgDMHSdzS89fGlHQzdZpNm0wMzwng0v6MKRNnfzxcPDh1rY'
    '8IENZw8D71ZBJXOn4Y0Nn9hFLwSZ0yZDHibPtlebuUamQ/fC5CGz4YUNn9glNd2qd9r0bDgCsqCazzyrhWeGj2iKVTYjx4IeZqyV'
    '3faT2G0/5NtLQXOmVMTAZTZlOTO8VVb4i56d8XsZKiwrRtW2ZebR3x0+3dz++P4PN7e3H/Y3t/cLicpjhSVPni3pB+B0gTsTG6iI'
    'AC5T6rsBuCvgrsBKxpbHIN8L+aUhPwj5pSE/CvmFIX+yfbSQnx3yJOSXJpYnu55dAzTn+7nd2/q56W393PyWfm533Lytn7t7Wz93'
    '/7Z+7uFt/dzjm2Lm7m3tu93b2ne7/LZ+7pvSzN3mla/dBcckWNnGbAkdPSZEy+4fbFnRzWV4Z1pWLGuH8fN/vn/3bkjv/+3Dx4/f'
    'ffi8+fzYJEpOIifRSydRdhI5iV46iXonkZPopZOoOImcRC+YRGXoumn75JkqkO4A56TIhEvLJ3JKy8+kpDyBydmNL28P89DYMq22'
    'QPBZkBGeHe7h2dseLsACr0RL/cpXqHVwfH+eK9rmS+dhffRsxdH5jvZOjdZHj7Q+mlYvl7bysdhL3DMLj/bO8tX5jvbCkyHzy22u'
    '7jWh0js2vKRMKvX66fl1ffe33I1brluuW65brluuW65b7iW23J1brluuW65brluuW65b7iW23L1brluuW65brluuW65b7iW23INb'
    'rluuW65brluuW65b7iW23KNbrluuW65brluuW65b7gW23CePArrluuW65brluuW65brlnmXLTW65brluuW65brluuW65l9hys1uu'
    'W65brluuW65brlvuJXK5zS3XLdct1y3XLdct1y33Elvu4JbrluuW65brluuW65Z7iS13dMt1y3XLdct1y3XLdcu9xJY7ueW65brl'
    'uuW65brluuVeonyqd8t1y3XLdct1y3XLdcu9xJZb3HLdct1y3XLdct1y3XIvseWe8yahtW6LJFvuatuoW+PZtsbU+nW30tRibL1u'
    'pW99K3VnvNqdcevO6M7ozujO6M7ozujO+PPOOOau657eGfPi3S5Piy3SrgeWbt+W7879sHx3LrmAsdPysf24fOxyhdCVBp53blE/'
    'OBZgNi1/3pqBxd86MHb5nKzj8vdWAWYN/DagAk9jl6+hthyzdNp4gBIlqnUAY8EzLH/HJ/JnSrSfVlauc5w5O76x8Q1+f4O/d4Df'
    'P05s/Nw6m1P2HRwP31fNDJ/aBjZ+hN8/0u9n+DeIT8vw+yuKlLoBPs+QK4vEMoz02Po66eFynshtNvDpMg2tRviBRj8wp/XmPwD/'
    'Qt/DHz0rE+c+UDoYHpY+wQ9UiFKBodWXUIN+AEbdlf7oCuPJE18U+oGBRt0wnpyVQPMfoGH6MIAQMbU0oeE5o+E9G14SGj6OZPgw'
    'Nx3mhg9sOHuYhn7qODdv5oY3NhxNgnEiyJw2GfIwedaYmnFQusoMl8yGFzYcuT/9nN0+Nxx9++w2NDccATkr/h8ePquFZ4aPaIpV'
    'NiPHgh5mrAiZKSc0fCTfXgqaM6UiBi61NjS8oWdvGT074/cyoNdU8xxhL7E7fzX68Onm9sf3f7i5vf2wv7m9pyhO0u4xl3SnS6pL'
    'qkuqS6pLqkuqS6pLqkuqS6pLqkuqS6pLqkuqS6pLqkuqS6pL+mZd0vrlhPwTLulaJyf6bgCnFrrnnnC4/3Pb2/q5w9v6uePb+rnT'
    'm/m50/EUfD1FVat1HLGLyPMN4woPhOUGDUs4fhqhQTjA8fDAWR2ggZeggQcPqEEDcnauzVpZ1KTp+446Ij30KxI9SwWdqdNbnq6v'
    'w0djQhicXyqzPtnM6PwY7TdpX9qX9qV9af8t0X6S9qV9aV/al/bfCO3X/en97yJ4WoTKaQVA+TopcB+fvfg8is9BfB7Dp3Ti8yg+'
    'SXwexSeLz/hI17p6fByf81R/Pzi2vTxkOFcTr5OiSWs3j4K/4X4i6t57a53vLeR7631vId9b8b2FfG/V9xbyvTXfW8j3NvjeQr63'
    '0fcW8r1NvreQ723jewv53ra+t2jvre661BkHxHxvxgEx35s8GfO97Xxv0d7bl+5hTx4lyg10BGugaxbovoQ6bIHuS6WB751Id6sC'
    'ulCB8r48gpzj+O27UKW0SmcpVI6IO0tNK3dO6uD4Cd40BTsVVdiZqdFOSP2apYaned7BTkL0euVCSwHX7pJTYCuU+XLP+XuduvVa'
    'ZtDmCvc6DvxqA9ufAuv8VKFYrT0g7gRaDYL72Ye8nkiptKqyG6aVO+Pkr9/w/Vd28JVFe2VHX1mwV9Z3vrJoryz5yqK9suwri/bK'
    'el9ZtFdWfGWBXtlYu657ai+bPQH34Nh1rg+YjURfeiUAafMPrkYo43Jzc7a/3EuXxFhXad3f8rCGuXlaCG0dw3Ig1ADOZQ/Lfxu9'
    '7Pq0kBLtyEyPjXTYzWpru1n0rG0q/aqNfTvWepc9zFjO0ifyoTOtaZpLrsycgJ2Z9d/dfLz5dPP5z4dPf/v4m3zT3M99/ENzDdXa'
    'sUv1qUg4teU0lf9/9t6uuXLcSNf9K/MD5oL4Bi499vbs7TkV45jumYtzowAJcKywSnJI1TuO59cfVdvu6q4ulRZRi1xa+eRdd2nx'
    '400mMvNJgOCG7RisCxu+pmM3zLNtSJ1bvgyzZZ5tQ+p8cYB8cR5o61YMadf5l7DxSx0v7tN6rq0e8sb7yWHfrSTCxi8z+DN9meHl'
    '7yCkvfdu2LgVw/MBcesBZevLmmVrErUbc+LGXdSd27S78YtzPD8GcKMBXAO4BnAN4BrArzOAWw3gGsA1gGsA1wB+nQHcaQDXAK4B'
    'XAO4BvDrDOBeA7gGcA3gGsA1gF9nAA8awDWAawDXAK4B/OoC+McdYPp6xg99hNPflp1eXIbzxd/GXT4gYuKGhXUbdgp40x8muY6P'
    'jWz+WMdGvdt3nkZ+TOOIb2MEgR/T+Bha10lDq4ZWDa0aWjW0nju0Gg2tGlo1tGpo1dB67tBqNbRqaNXQqqFVQ+u5Q6vT0KqhVUOr'
    'hlYNrecOrV5Dq4ZWDa0aWjW0nju0Bg2tGlo1tGpo1dB67tAaNbRqaNXQqqFVQ+u5Q2vS0KqhVUOrhlYNrecOrVlDq4ZWDa0aWjW0'
    'nju0Fg2tGlo1tGpo1dB67tBaNbRqaNXQqqFVQ+u5Q+usoVVDq4ZWDa0aWs8dWhcNrRpaNbRqaNXQeu7Q2jS0amjV0KqhVUPruUNr'
    '19CqoVVDq4ZWDa3nDq26X6uGVg2tGlo1tJ45tJpJ92vV0KqhVUOrhtazh1bdr1VDq4ZWDa0aWs8eWnW/Vg2tGlo1tGpoPWdoDYvu'
    'fKWh9W2G1u0fNtz64UGbdg31L/rWS79PeeOHDd22VGLDeVKVpp5feEV5e7nqClJPXKfJ6n62mno09Zzy+/y2UpWmHk09V516nPbq'
    'NfVo6tHUo6lHG26vJpNg3aZf++lrqUfnMjT1aOrR1KOpR1PPwalHv82nqUdTj6YeTT2aeg5OPTrXo6lHU4+mHk09mnoOTj26vZim'
    'Hl08rKFVp9HPHlp1ezENrRpaNbRqaD17aNXtxTS0amjV0Kqh9dyhtb322Vzr4ukh8NrC8EvhREP25UJ2DqyetStvq2dtLtTjfjEF'
    'bss3H8Oj3H7yiwe8ZNWLv2zw6dffPdw9vH+4/76//8vdr7LMV99QaFmTlCYpTVKapDRJaZJ6q0mqaJLSJKVJSpOUJilNUm81SVVN'
    'UpqkNElpktIkpUnqrSapWZOUJilNUpqkNElpknqrSWrRJKVJSpOUJilNUpqk3maSeo69mqQ0SWmS0iSlSUqT1FtNUlGTlCYpTVKa'
    'pDRJaZJ6q0lK35PSJKVJSpOUJilNUm82Sel7UpqkNElpktIkpUnqzSYpfU9Kk5QmKU1SmqQ0Sb3ZJKXvSWmS0iSlSUqTlCapt5ik'
    'cvhocN0WVZOJfkdGvyOj35HRbWP3zVefpx6jqUdTj6YeTT2aejT1HJt6rKYeTT2aejT1aOrR1HNs6nGaejT1aOrR1KOpR1PPsanH'
    'a+rR1KOpR1OPph5NPcemnqCpR1OPph5NPZp6NPUcm3pmTT2aevTD3xpar36J8psLrYuGVg2tGlo1tGpoPXdobRpaNbRqaNXQqqH1'
    '3KG1a2jV0KqhVUOrhtZzh9ZVQ6uGVg2tGlo1tJ45tHrdqEFDq4ZWDa0aWs8eWnUjAg2tGlo1tGpoPXto1RftNbRqaNXQqqH17KFV'
    'XyTX0KqhVUOrhtazh1Z9UVpDq4ZWDa0aWs8eWvVFYA2tGlo1tOqLrmcPrVFDq4ZWDa0aWjW0nju0Jg2tGlo1tGpo1dB67tCaNbRq'
    'aNXQqqFVQ+u5Q2vV0KqhVUOrhladxjp3aNVNBTW0amjV0Kqh9eyhVTcV1NCqoVVDq4bWs4dW3VRQQ6uGVg2tGlrPHlp1U0ENrRpa'
    'NbRqaD17aNVNBTW0amjV0Kqh9dyhNeimghpaNbRqaNXQevbQqpsKamjV0KqhVUPrOUNrfw6bk1atGlr1Y+L6MXH9mLi+UnFw6tGq'
    'XlOPph5NPZp6NPUcnHp0K3VNPZp6NPVo6tHUc3Dq0a3mNfVo6tHUo6lHU8/BqUe34tfUo6lHU4+mHk09B6ce/VSBph5NPZp6NPVo'
    '6jk49einHDT1aOrR1KOpR1PPwalHd7bU1KOpR1OPph5NPQenHt35U1OPph5NPZp6NPUcnHp0Z1RNPZp6NPVo6tHUc3Dq0Z1jNfVo'
    '6tHUo6lHU8/BqUd31tXUo6lHU4+mHk09x6Yeo3u4aerR1KOpR1OPpp6DU4/u4aapR1OPph5NPZp6Dk49uoebph5NPZp6NPVo6jku'
    '9cR1mpb6SurxOZ2eIpw9/bchn/7b6DakqQ2pstg9UuVzGNkp9WxNJ3FjOknTtt+/ZL+X0kPY9s0Y46aN4Xvb77cO6+l5zGw7wL80'
    'Il48oGwM4C+OoxcP2Br8prQ1Hnt/pmj54gG/HAg//8aWfS6no8Y0jWka0zSmyYhpoX+04SsxzTp/8rh35WTkfhkxv9h6cPvEyg3x'
    'L5oNrQe/If6dfr+bWhrbWwRhY4sgbox/2+4nTGZjC2LatWURzcYWRJg2/t5ui99+Y0vBp31bHMVszCfpPN95/P1dffrTXJc/3/yx'
    'PtZ2+/SrCJbd1kRkds9caWMisnn3VGe3Zq6NH3x8MXp9sXdh/WRP70aY/NJw/uKvS9jQ6bCTiVv6Ir8srD7Pt1XzreZbzbeabzXf'
    'ar7VfLt7vp0132q+1Xyr+VbzreZbzbe759tF863mW823mm8132q+1Xy7e75tmm8132q+1Xyr+Vbzrebb3fNt13yr+VbzreZbzbea'
    'bzXf7p1vw6T5VvOt5lvNt5pvNd9qvt093xrNt5pvNd9qvtV8q/lW8+3u/eRV863mW823mm8132q+1Xy7Z771aTJTfm0Pn9P3uXk5'
    'd7wUY7ZuA+g3xqSU9t1mcIrbfm+2DrOwdUeXOO09zFL4mjsVdSd1p/O5U1V3Unc6nzvN6k7qTudzp0XdSd3pfO7U1J3Unc7nTl3d'
    'Sd3pfO60qjupO53FncIyTdkc4U4viYl2Yws2vjQ79FnL7W//e/PuXTI3/3Z7d/fd7X29f2kL7XDC8pJdzfDi525e9hq31WvC1idj'
    'd94wePNXLF78GM6LB5StX+J48dMRP/qIUx9RH3nFR5L6iPrIKz5S1EfUR17xkao+oj7yso88k+DkXn8FacMXDE9fSrXtS4N7fxEw'
    'h42fIykbCdCd5wt2Ly5f2ThyrNtImNZvHcxboezFJVMvf1Mvbh2b+VwfF/lx5AQdOTpydOQMjJyoI0dHjo6cgZEz68jRkaMjZ/vI'
    'SVZHDm/k7O/X53ZTp26qbvr23dSrm6qbvn031RaNuunbd9OqbqpUp1Q3MnKKjhwdOTpyto+cWed9deToyBkZOUZHjo4cHTkDI0d7'
    '8DpydOSMjBydFtCRoyNnZOToTIWOHB05IyNHu9I6cnTkjIwcXd+qI0dHzsjIyTpydOToyBkYOToTqiNHR87IyKk6cnTk6MjZNnI+'
    'bvu06hoCXV75BpdXfjrgu4e7h/cP99/393+5+5VzvrgvwsdP19jX9u+MNh/rr799eP8s5adf/2ZZ+tPTw+Nfb/5QH39bHx9v++PH'
    '//zKIe/64/Knev/xKxYnOHbKaVfHNtGf+Pt//MPNu+ex8H19f/s4fuC726en24f7f/9Lv+9t82mcu/mv2//5aOkTzvPqt0PMS+Fx'
    '/KsjJxzptybKuPGAtPF7JcFtPiBtTZRuYwSyaetGMVsP2LjZzXMM2bizjJu2RlETth4QN3xzxeSXouCXP9Hictn2RZfpLB+A+fLP'
    'i9l0M+WlUfbFn/v80uelXvi+TN7wfRlr/Kbvy5gtvy5bfh1fGlTv+vuPeey3D89JrD08/ixf/eLfb95N7u+//emfvpLAuyZwTeCa'
    'wDWBawLXBK4J/PoS+KoJXBO4JnBN4JrANYFrAr+6BP7q1sKawDWBawLXBK4JXBO4JvA3mMCNJnBN4JrANYFrAtcErgn8+hL4Kxtu'
    'XFtS1iR4wSQY7OYD9k5RA+E97hp+7YYQll9aFvtCwHsr4fHgEOY0hGkI0xCmIex6Q5jXEKYhTEOYhrDrDWGv7WjiYzg1hG3qGr/o'
    'Kmd408+9xPkv/n7jm4Qubfv9S+7y0u+33k+OG3+/7fwv9jBf+n3YZv8Qt9kzZLfx99vOH802e77o9y/9Pk7bJhOs3/Z7n3aarPj7'
    '79PGyZCyUW+x2950ndLG3+eNb+qGjb+Pb20awrmN1YUvaesn2MPWciR8LTElTUyamDQxaWLSxKSJ6S0lpqyJSROTJiZNTJqYNDG9'
    'kcSUwzRNyyuJKdhycmIKbjr9ty8535cSXjj5HsyU0i6bjJm0IelOeb8NybauQfXxOjYYe/H3m1dnbt77L2+cQ9m40d6z//qtB2zd'
    '+y9tndZJG2dpzAHzQOdabLl5Y7gvzwXlvOXXZdtc0IZlgnYyadMSRLdtLuhvPjcl95U84YPmievKE2Vbsbz7uw2ahzQPaR76uq+e'
    'ZQnDi+H/y7/2m9JW2mvBw7aV8+HF/Ze/KclFTXKa5DTJaZLTJKdJTmqSS5rkNMlpktMkp0lOk5zUJJc1yWmS0ySnSU6TnCY5qUmu'
    'aJLTJKdJTpOcJjlNckKTXNQFiteV5PZPWhtXCU9FZpIb34dC06OmxzeUHt9EmmmaZiSvg39mr40vY01WWeq0jZJM1jSjaeYCK/Q3'
    'raI/f94o6zTl1z5L9+I7Z98Yh8+yS9xLsdK6jbE47FryXyxWvryL2uYDNg4EE/KZRs53D3cP7x/uv+/v/3L3K+f8ZfHxmW+XSX1b'
    'fVuobxv1bfVtob5t1bfVt4X6tlffVt8W6ttBfVt9W55vtzQ9P9dXdr030W7oQacNPeiNrcAXdzV7+YCtmwRtbNQ9H7B1l/e41ad+'
    'uTXVz3evW6Yp1dcent+4U5jd2ND10X3t/uYz358v8VJ6Pk5G5dcW9nl3+m6BPqYNE1f+9EHoN0wabRjcG+frD39Wr019xpd2Sfvy'
    'h+6SMZt+7uOmz+htu5n80ozAF38eXlxg8NLPt3wCMHgzbfu52/Zzv2nuwAxkxJfM8/WD/NciQ9XIoJFBI4NGhl9Fhlkjg0YGjQwa'
    'GX4VGZpGBo0MGhk0MvwqMnSNDBoZNDJoZPhVZFg1Mmhk0MigkeHzyFBejQzFX2ruZGkfPyqz7f4+O3wqw4d3/3z4q995KuGSM2XN'
    'vXJ/LsUNsXrDt6XMhiUGZsP0bpg2vZcWtgxRH/NLc9opffy+0GvvjE1+gzHDhmTmv91Av3l8+uGXQcZM9qWx+4Uf55JOPrOdSnIn'
    '/9ikFz9Z86PZk5r9EmavavZLmH1Wsx9s9o9lTltkJ8rP5TaW3M6Su6Lk9okl17DkWpZch5K7viY3OHOJ2/Jv87bC27yt+DZvK73N'
    '28pv8bbMFEiBx0yRJTex5GaW3MKSW1lyZ5bchSWX04r5OCO1vNaKMaevHnjOamH0pdfP3sV9dZLhQreV3+Ztlbd5W/XN3VZcJ5vy'
    '27yt8jZv640+xPlt3tbyNm+rvbnbmk+hIDuZlw5fv7pY5OP/3Lzz4ebdw/2HtT8+1g83726fnm4f7v/9L/2+t5NT+Cu3kLcp+MqC'
    'k3/8w807527+6/Z/bvvjy7f8+ev9r9JzPH0rWGPMxq1XN+447vO236eNL/j7YrYeYL+2N/Grzcdp2rBoctsCJLdxcaO3287vndn2'
    '+2i3LaDKG7cmKNvuJ27cZ9ds3I7e2I37oaS8cXv8jb9/aUvXE/YJLqNHuji8Bf7WL8TEtPWArbsfp637i2xdAuhe2n785QP81i1P'
    'ysYAZ8s3RcTz74rzPNC3bvm8daOeaMO+m0q/vCH85i2fv7gvf7Tpa2kpaFrStKRpSdOSpiVNS28nLSVNS5qWNC1pWtK0pGnp7aSl'
    'rGlJ05KmJU1LmpY0Lb2JtDR/fL1gPs8U5ucTq2aP00592ee0bR8j2H3utu9y2nXaxwhun7vdx8HiLkaYkt/nbncywj5+G/fxhLiT'
    'bcM+p427nHba57RuHyO4ne427XJau09MsPsMXrvP4LX7DF67z+C1O/jtx8VWdp/Tun1OO+1z2nWf08Z9Tuv3Oe1ODmb2qcH2iWDz'
    'PqFmzvucdp/sMO+Ty+Z9Mu+8T7ydd4pgdZ/Ttn1OO+9z2n2Y1+7jt3anGmyfmGDLPqet+5x23ue0OzlY2+e0+3Q/7LoPkuyTed0+'
    '7OD2SehuH3Zw++Syso8n9HWf0q7sc9od4u3zSZM9+wszT0/1+Uf39cPzD2++r3f17tMpf/23gSt81lT/2//evHuXzM2/3d7dffd8'
    '/vuvSXY8yZ4nOfAkR57kwpOceJIzT3LlSZ55khee5MaT3HmSV5zkPPEkG55kHi9nHi9nHi9nHi9nHi9nHjxmHjxmXlck43i5TJkn'
    'ufAkAx175knmNYJWXldkXXmOPfEkG55kXldk5WHFyuuKrLyuyMrriqy8rsjKm63ovDmplTdBswJLEeAEDW+tSOa1CDJvrUjmdUUy'
    'Ly93HlZ0HlZ0HlZ0Xlek8yZbV6Bk3nrslVdjr8BpOF6NXXnhq/LCV+WFr8oLX5UXvgqvxi48Xi48Xi48Xi68UqTwZh4Lbxqu8Kbh'
    'Cm8arvBWBM28pzwDnzKv4Jx5BecMnKABrvviVV+dV311Xl7unveigeNJBj7lwJMceZKB1RdvGq7zpuE6bxqu86bhOm2lrnHe8SR7'
    'nuTKkzzzJC88yYEnOfIkJ57kzJNccJIdr+B0K8+xJ55kw5MM/OwObxou8t5sTbz9vixvvy/LC1+V92J+5YWvmbc8Zubl5ZkVvpZ2'
    'wqeQ+/uHx7/+048H/1P4yonidKYTvbqx8ckneq37EezNd7fzY71vJz3Kb7iT9GbuJL6ZOwlv5k78W7kT92b8JNo3Y5M347HRvRmb'
    'vJmx495MjHVvZxSXN3Mnb8dj65u5k7cT2eY3cyfmzdzJ8mbuZHozd9Leyp3Y9c3UbMu5IKGd60T9XCdaz3Qicy4iCxvKja/cTj/H'
    'WUI8y720s9xLOstZ8lkUzd96ltlP0/xa6WKnm3+tj/e3/fHkIX3S7fuzPBB/Fhfz61ke63SWs5iznMWf5SzuHGex51FkzzJoxu7l'
    'VHf/P/f/tz99uP3vvzX4vnIb9m3chn8btxHexm3Et3Eb6U3cxrIhmp18TnP+c859h3OuO2gP5z+nLzucM+9wzrSDPeMO9znvcJ92'
    'h3O6Hc7pd7BnPf851x3G+3r+8W6maYdzmh3OaXc45w7+ubYd4vwO8XPeIX7OO4yjtEOOm3fIcfMOcWneIR/NO+SjvEMNlvew57LD'
    'fe7hSzvEkLxHTbtDHZJ3iMl5h9om7PCMwg72DDvEz7DDODI7PPe4QwwJO9R1ZodcHHbIxWaHOiTscE5zZu3NTebcbPjjOeMO5zxz'
    'PurphKV4I+dcdjhn2+Gc0w7nNDuc0+5wTrfDOf0O59zD5+MO50w7nDPvcM6ywznPHJNnY1I4x3P/5zMuG9i6pnrb6b/tDb4Uolpr'
    'g7WSWmuDtbJaa4O1ilrrZGvFs3RDONbqaq0N1lrVWqdb6yxz7ZwoX9VaG3zLqLU2WMuqtTZYy6m1NljLq7U2WEt7EFuspT2ILdbS'
    'HsQWa2kPYou1tAexxVpay2+x1qzW2mCtRa21wVraDdxiLe0GbrGWdgM39Le81vJbrKW1/BZraS2/xVpay2+xltbyG6zltDrdYi2t'
    'TrdYS6vTLdbS6nRLlNe56i2+pfOJW6yl84lbrKXziVuspfOJW6ylPYgt1tKcuMFaVmv5LdbSWn6LtbSW3xK3dG3ghlmMxorym0//'
    'oh0/nfO3D+/fP9z/dJr//O2739z8+POf/+j3d/XpT3Nd/nzzx/pY2+3TJzP9+k83/1rf93/67kN9/LDpoU/h5n8/PD7173/48PB4'
    '+3z7mw6Of//Lf963/vibDx8+3tGWE/zLZP/+p1M8Zavfvnrkz7eBtcNHuuEj/fCRYfjI+LWRbXRk68jWkS1wZFsd2TqydWQLHNlO'
    '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'
    'YvmsieWzLpbPulg+62L5rIvlsy6Wz7pYPuti+ayL5bMuls+6WD7rYvmsi+WzLpbPulg+62L5rIvls1Usn61i+WwVy2erWD5bxfLZ'
    'KpbPVrF8torls1Usn61i+WwVy2erWD5bxfLZKpbPVrF8tkrlszRNYpUZscqCWGVRrLIkVlkWq6yIVVbFKpvFKlvEKpNaEScjtgYx'
    'VqwyJ1aZF6tMbEVsxFbERmxFbMRWxEZsRWzEVsRGbEVsxFbERm5F3MUqE9sjtmJ7xFYsn1mxfGbF8pkVy2dWLJ9ZsXxmxfKZFctn'
    'ViyfWbF8ZsXymRXLZ1Ysn1mxfGbF8pkTy2dOLJ85sXzmxPKZE8tnTiyfObF85sTymRPLZ04snzmxfObE8pkTy2dOLJ85sXzmxPKZ'
    'F8tnXiyfebF85sXymRfLZ14sn3mxfObF8pkXy2deLJ95sXzmxfKZF8tnXiyfebF85sXyWRDLZ0EsnwWxfBbE8lkQy2dBLJ8FsXwW'
    'xPJZEMtnQSyfBbF8FsTyWRDLZ0EsnwWxfBbE8lkUy2dRLJ9FsXwWxfJZFMtnUSyfRbF8FsXyWRTLZ1Esn0WxfBbF8lkUy2dRLJ9F'
    'sXwWxfJZEstnSSyfJbF8lsTyWRLLZ0ksnyWxfJbE8lkSy2dJLJ8lsXyWxPJZEstnSSyfJbF8lsTyWRbLZ1ksn2WxfJbF8lkWy2dZ'
    'LJ9lsXyWxfJZFstnWSyfZbF8lsXyWRZbERexFXERWxEXsRVxEVsRF7EVcRFbERexFXERWxEXsTVIEdsjLmJ7xEVsj7iIrYir2Iq4'
    'iq2Iq9iKuIqtiKvYiriKrYir2Iq4iq2Iq9gecRXbI65ie8RVLJ9VsXxWxfJZFctnVSyfzWL5bBbLZ7NUPisti1VWxCqrYpXNYpUt'
    'YpU1scq6WGVSq6vSJ7HKjFhlYqur7sQq82KVBbHKolhlSawysXzWxfJZF8tnXSyfdbF81sXyWRfLZ10sn61i+WwVy2erWD5bxfLZ'
    'KpbPVrF8torls1Usn61i+WwVy2erTD5L03z+fuO33uCnn7yrT3+tn27nb//78x9893D38P7h/vv+/i93n+z3i3/9tWBPExxogiNN'
    'cKIJzjTBhSa40gTPNMELTXCjCe40wStM8Plbs29dsKEJtjTBNB5eaTy80nh4pfHwSuPhlcbDK42HVxoPrzQeXmk8vNJ4eKXx8Arj'
    '4WWaaIINTbClCXY0wZ4mONAER5rgRBOcaYILTXClCZ5pghea4EYT3GmCaTxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxs'
    'aDxsaDxsaDxsaDxsaDxsaDxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTzsaDzsaDzsaDzs'
    'aDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzs'
    'aTzsaTzsaTzsaTwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaTwcaTwcaTwcaTwcaTwc'
    'aTwcaTwcaTwcaTwcaTwcaTwcaTwcaTwcaTwcaTwcaTycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDyc'
    'aDycaDycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTxcaDxcaDxcYDzcaHvTNtretI22N22j'
    '7U3baHvTNtretI22N22j7U3baHvTNtretI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j'
    '7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j'
    '7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j'
    '7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0+j7cXTaHvxNNpePI22F0/D7cVTaDxcaDxcaDxcaDxcaDxcaDxcaDxcaDxcaDxc'
    'aDxcaDxcaDxcaDxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTw803h4pvHwTOPhmcbDM42H'
    'ZxoPzzQenmk8PNN4eKbx8Ezj4ZnGwzONh2caD880Hp5pPLzQeHih8fBC4+GFxsMLjYcXGg8vNB5eaDy80Hh4ofHwQuPhhcbDC42H'
    'FxoPLzQeXmg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gk83Gk83Gk83Gk83Gk83Gk8'
    '3Gk83Gk83Gk83Gk83Gk83Gk83Gk83Gk83Gk83Gk8vNJ4eKXx8Erj4ZXGwyuNh1caD680Hl5pPLzSeHil8fBK4+GVxsMrjYdXGg+v'
    'NB5eYTzcp4km2NAEW5pgRxPsaYIDTXCkCU40wZkmuNAEV5rgmSZ4oQluNMGdJpjGw4bGw4bGw4bGw4bGw4bGw4bGw4bGw4bGw4bG'
    'w4bGw4bGw4bGw4bGw4bGw4bGw4bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw5bGw47Gw47G'
    'w47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw47Gw57Gw57Gw57Gw57Gw57Gw57Gw57Gw57Gw57Gw57Gw57G'
    'w57Gw57Gw57Gw57Gw57Gw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw5HGw5HGw5HGw5HG'
    'w5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw5nGw5nGw5nGw5nGw5nGw5nG'
    'w5nGw5nGw5nGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw5XGw5XGw5XGw5XGw5XGw5XG'
    'w5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGwzONh2caD880Hp5pPDzTeHim8fBM4+GZxsMzjYdnGg/PNB6eaTw803h4pvHw'
    'TOPhmcbDC42HFxoPLzQeXmg8vNB4eKHx8ELj4YXGwwuNhxcaDy80Hl5oPLzQeHih8fBC4+GFxsONxsONxsONxsONxsONxsONxsON'
    'xsONxsONxsONxsONxsONxsONxsONxsONxsONxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOd'
    'xsMrjYdXGg+vNB5eaTy80nh4pfHwSuPhlcbDK42HVxoPrzQeXmk8vNJ4eKXx8Erj4RXGw+s00QQbmmBLE+xogj1NcKAJjjTBiSY4'
    '0wQXmuBKEzzTBC80wY0muNME03jY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0HjY0njY0njY'
    '0njY0njY0njY0njY0njY0njY0njY0njY0njY0njY0njY0njY0njY0njY0XjY0XjY0XjY0XjY0XjY0XjY0XjY0XjY0XjY0XjY0XjY'
    '0XjY0XjY0XjY0XjY0XjY03jY03jY03jY03jY03jY03jY03jY03jY03jY03jY03jY03jY03jY03jY03jY03g40Hg40Hg40Hg40Hg4'
    '0Hg40Hg40Hg40Hg40Hg40Hg40Hg40Hg40Hg40Hg40Hg40Hg40ng40ng40ng40ng40ng40ng40ng40ng40ng40ng40ng40ng40ng4'
    '0ng40ng40ng40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg40Xg403g403g403g403g403g403g4'
    '03g403g403g403g403g403g403g403g403g403i40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi40Hi4'
    '0Hi40ni40ni40ni40ni40ni40ni40ni40ni40ni40ni40ni40ni40ni40ni40ni40nh4pvHwTOPhmcbDM42HZxoPzzQenmk8PNN4'
    'eKbx8Ezj4ZnGwwuNhxcaDy80Hl5oPLzQeLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjReLjT'
    'eLjTeLjTeLjTeLjTeLjTeLizeNhM3tEEe5rgQBOMG8OJJjjTBBea4EoTPNMELzTBjSa40wSvMMFhogk2NMGWJpjGw4HGw4HGw4HG'
    'w4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw4HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HGw5HG'
    'w4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw4nGw5nGw5nGw5nGw5nGw5nGw5nGw5nGw5nGw5nG'
    'w5nGw5nGw5nGw5nGw5nGw5nGw5nGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw4XGw5XGw5XG'
    'w5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGw5XGwzONh2caD880Hp5pPDzTeHim8fBM4+GZxsMzjYdnGg/P'
    'NB6eaTw803h4pvHwTOPhmcbDC42HFxoPLzQeXmg8vNB4eKHx8ELj4YXGwwuNhxcaDy80Hl5oPLzQeHih8fBC4+GFxsONxsONxsON'
    'xsONxsONxsONxsONxsONxsONxsONxsONxsONxsONxsONxsONxsONxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOdxsOd'
    'xsOdxsOdxsOdxsOdxsMrjYdXGg+vNB5eaTy80nh4pfHwSuPhlcbDK42HVxoPrzQeXmk8vNJ4eKXx8Erj4RXGw2aaaIINTbClCXY0'
    'wZ4mONAER5rgRBOcaYILTXClCZ5pghea4EYT3GmCaTxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxsaDxs'
    'aDxsaDxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTxsaTzsaDzsaDzsaDzsaDzsaDzsaDzsaDzs'
    'aDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaDzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTzsaTwc'
    'aDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaTwcaTwcaTwcaTwcaTwcaTwcaTwcaTwcaTwc'
    'aTwcaTwcaTwcaTwcaTwcaTwcaTycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaTycaTyc'
    'aTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTycaTxcaDxcaDxcaDxcaTxcaTxcaTxcaTxcaTxcaTxcaTxcaTxc'
    'aTxcaTxcaTxcaTxcaTw803h4pvHwTOPhmcbDM42HZxoPzzQenmk8PNN4eKbx8Ezj4ZnGwzONh2caD880Hl5otfRCq6UXWi290Grp'
    'hVZLL7RaeqHV0gutll5otfRCq6UXWi294Gpp2txSo80tNdrcUqPNLTUaDzcaDzcaDzcaDzcaDzcaDzcaDzcaDzcaDzcaDzcaDzca'
    'DzcaD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD3caD680Hl5pPLzSeHil8fBK4+GVxsMrjYdX'
    'Gg+vNB5eaTy80nh4pfHwSuPhlcbDK42HVxgP22miCTY0wZYm2NEEe5rgQBMcaYITTXCmCS40wZUmeKYJXmiCG01wpwmm8bCh8bCh'
    '8bCh8bCh8bCh8bCh8bBB8XCefJpogg1NsKUJdjTBniY40ATj0lKiCc40wYUmuNIEzzTBC01wownuNMErTHCm8XCm8XCm8XCm8XCm'
    '8XCm8XCm8XCm8XCm8XCm8XCm8XCm8XCm8XCm8XCm8XCm8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh8XCh'
    '8XCh8XCh8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8XCl8fBM4+GZxsMzjYdnGg/PNB6eaTw8'
    '03h4pvHwTOPhmcbDM42HZxoPzzQenmk8PNN4eKbx8ELj4YXGwwuNhxcaDy80Hl5oPLzQeHih8fBC4+GFxsMLjYcXGg8vNB5eaDy8'
    '0Hh4ofFwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwo/Fwp/Fwp/Fwp/Fwp/Fwp/Fwp/Fwp/Fw'
    'p/Fwp/Fwp/Fwp/Fwp/Fwp/Fwp/Fwp/Fwp/HwSuPhlcbDK42HVxoPrzQeXmk8vNJ4eKXx8Erj4ZXGwyuNh1caD680Hl5pPLzSeHiF'
    '8XCYJppgQxNsaYIdTbCnCQ40wZEmONEEZ5rgQhNcaYJnmuCFJrjRBHeaYBoPGxoPGxoPGxoPGxoPGxoPGxoPGxoPGxoPGxoPGxoP'
    'GxoPGxoPGxoPGxoPGxoPGxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPWxoPOxoPOxoPOxoP'
    'OxoPOxoPOxoPOxoPOxoPOxoPOxoPOxoPOxoPOxoPOxoPOxoPOxoPexoPexoPexoPexoteRoteRoteRoteRoteRoteRoteRoteRot'
    'eRoteRotBRotBRotBRotBdrsYaDNHgYaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaDwcaD0caD0caD0caD0caD0caD0caD0ca'
    'D0caD0caD0caD0caD0caD0caD0caD0caD0caDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDycaDyca'
    'D2caD2caD2caD2caD2caD2caD2caD2caD2caD2caD2caD2caD2caD2caD2caD2caDxcaDxcaDxcaDxcaDxcaDxcaDxcaDxcaDxca'
    'DxcaDxcaDxcaDxcaDxcaDxcaDxcaD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD1caD880Hp5p'
    'PDzTeHim8fBM4+GZxsMzjYdnGg/PNB6eaTw803h4pvHwTOPhmcbDM42HZxoPLzQeXmg8vNB4eKHx8ELj4YXGwwuNhxcaDy80Hl5o'
    'PLzQeHih8fBC4+GFxsMLjYcXGg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg83Gg93Gg93Gg93'
    'Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg93Gg+vNB5eaTy80nh4pfHwSuPhlcbDK42HVxoPrzQeXmk8vNJ4'
    'eKXx8Erj4ZXGwyuNh1cYD8dpogk2NMGWJtjRBHua4EATHGmCE01wpgkuNMGVJnimCV5oghtNcKcJpvGwofGwofGwofGwofGwofGw'
    'ofGwofGwofGwofGwofGwofGwofGwofGwofGwofGwofGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGwpfGw'
    'pfGwpfGwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwo/Gwp/Gwp/Gwp/Gwp/Gwp/Gwp/Gwp/Gw'
    'p/Gwp/Gwp/Gwp/Gwp/Gwp/Gwp/Gwp/Gwp/FwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFwoPFw'
    'pPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwpPFwovFwovFwovFwovFwovFwovFwovFwovFwovFw'
    'ovFwovFwovFwovFwovFwovFwovFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwpvFwofFwofFw'
    'ofFwofFwofFwofFwofFwofFwofFwofFwofFwofFwofFwofFwofFwofFwpfFwpfFwpfFwpfHwTHvCM4yHy/n3tfz9XX3601yXP9/8'
    'sT7Wdvv06VZ+/adzWupzZatUZeffqfLNKDNilVmxypxYZV6ssiBWWRSrLIlVlsUqK2KVVbHKZrHKFrHKmlhlYvksiOWzKJbPolg+'
    'i2L5LIrlsyiWz6JYPoti+SyK5bMols+iWD6LYvksiuWzKJbPolg+i2L5LIrlsySWz5JYPkti+SyJ5bMkls+SWD5LYvksieWzJJbP'
    'klg+S2L5LInlsySWz5JYPkti+SyJ5bMsls+yWD7LYvksi+WzLJbPslg+y2L5LIvlsyyWz7JYPsti+SyL5bMsls+yWD7LYvksi+Wz'
    'IpbPilg+K2L5rIjlsyKWz4pYPiti+ayI5bMils+KWD4rYvmsiOWzIpbPilg+K2L5rIjlsyqWz6pYPqti+ayK5bMqls+qWD6rYvms'
    'iuWzKpbPqlg+q2L5rIrlsyqWz6pYPqti+ayK5bNZLJ/NYiviWWxFPIutiGexFfEstiKexVbEs9iKeBZbEc9iK+JFbA2yiO0RL2J7'
    'xIvYHvEitiJexFbEi9iKeBFbES9iK+JFbEW8iK2IF7EV8SK3IhbbI17E9ogXsT3iJpbPmlg+a2L5rInlsyaWz5pYPmti+ayJ5LPZ'
    'mHmKYpUFscq8WGVOrDIrVtksVlkVq6yIVZbFKhNbg5hJ7DNbxSrrYpUtYpU1sRFEbK1vxNb6RmxFbIxYZWL5zIit9Y3YWt+IrfWN'
    '3FpfbL/RiK31jdha38itiMVSjBHbb7Ria30rtm60YinGiqUYK7bfaMXWjVZs3WjF9q6s2BrEyq1BxPZBrNg+iBXbB7FimdrJra7E'
    'dgus2G6BE1sRO7F1oxNbNzqxfRAntg/ixPZBnNha34mt9Z3YWt+J7fA4sRTj5VZXcvlMLMU4uRQjtt/oxdb6Xmyt78XW+l5sre/F'
    'duW82Frfi631vdyKWCzFeLH9Ri+21vdia30vttb3cmt9sf3GILbWD2Jr/SC21g9ia/0gtt8YxNb6QWxFHMRWxEFsVy4IJc9p2w5D'
    'v3l6qk9Pt/f1w+3D/c339a7effrxr/928865m/+6/Z/b/njz7vb5jw/3//6Xft/bzcfz/cvdw/Ln67Hbp5+8q09/rZ+s9Lf/vXn3'
    'Lpnno+/uvnu2wf3PFX5ucasWP9jiRi1+sMUntfihFq/rqhY/0uJmjmIZN4pl3CiWcaNcxhXbZ49i57OiWHqPYuk9iqX3KLbPHsXO'
    'Z0Wx81lR7HxWFLumJorts0exc/1RbN2YxPJZEstnSSyfJbG1fhJb6yextX4SW+snsf3GJLYPksRSTBJLMUksxSSxFJPF1o1Zbt0o'
    'l8/EMnUS22/MYmv9LLbWz2Jr/Sy21s9ie1dZbEWcxVbEWW5FLJaps9h+YxFb62exfZAslmKyWIrJYimmiK31i9hav4it9YvYWr+I'
    '7TcWsRVxkVs3iuWzIrYrV8TyWRFbERexFXGRWxGLJc8itt9YxfZBqtiKuIqtiKvYurGK7RZUsXVjFdsHqWL7IFUsn1W5NYjYurGK'
    '7fBUsUw9y62IxZLnLLciFtvhqWI7PLPYingWSzGz2Fp/Flvrz2I7PLPYWn8Wy2ez2Fp/FtuVm8VSzCKWYmaxFfEstyKWS55ie1eL'
    '2Fp/EVvrL2Jr/UVsrb+I7V0tYiviRSzFLHIrYrEUs4jtNy5ia/1FbK2/iK31F7m1vth+YxNb6zextX4TW+s3sbV+E9tvbGIppomt'
    'iJvYiriJ7co1seTZxNb6TWyt38TW+k1urS+2K9fF1vpdbK3fxdb6XW6tL7bf2MVWV10sxXSxFNPFUkwX22/sYmv9LrbW72Jr/S63'
    '1hfbb1zF1vqr3FpfbkUstiu3iuWzVWytv4qt9Vextf4qttZfZfYby+QEdb8//eRdffpr/aTjb//78x9893D38P7h/vv+/i93n27v'
    'F//6a0tVtdSJlupqqRMt1dRSJ1pqUUudZilBc2N7W8qqpU60lFFLnWipSS11YkRf1VIn+lRUS51oqaCWOtFSXi11oqWyWupESyW1'
    '1ImWUu471VLKfadaSjt5p1pKO3mnWqqopU60lPY8T7TUql2XUy2lXZdTR5/2Ek71Ke1PnWop7SWcainlvlMtpZ28Uy2l/alTLaXz'
    'fadaSgn5VEtp1+VUSykhn2op7bqcaimdcTjNUn5SQj7VUsp9p44+7SWcainteZ5qKZ3vOzVOKSGfaintT51qKe0lnGop7SWcaimd'
    'xTrVUtp1OdVSSsinWkq7LqdaSnsJp1pKZ7FOtJTRXsKpPqW9hFMtpb2EUy2lvYRTLaWzWKdGdO0lnGop7SWcaikl5FMtpbNYp1pK'
    '+1OnWkq571RLKfedaimdmznVUtqfOnFmdFafOtVS2kc/1VLaRz/VUhqnTrWUVgmnWkorzxMttWgf/VSf0j76qZbSPvqpltI++qmW'
    '0j76qRFd++inWkr76KdaSnuep1pKZxxOtZTOOJxqKaWZUy2lhHyqpbTneaqltD91qqW053mqpbSXcKqltJdwqqW0l3CqpbSXcKql'
    'dL7v1J3ktZdwqqW0l3CqpbSXcKqltJdwqqV0vu9USyn3nWop7bqcaintupxqKZ3FOtVS2h0+wVIlGX9+S711wYkl2FpDEzzBBJuV'
    '9oQjTXCgCfY0wY4m2IIEz8b4WGmCZ5rgQhO8wASnifaEG03wShPcaWM40AQbmmBaaZk8TbCjCabl4YQrLWl4mGi0lGg8nGm0lGmV'
    'VsZVWjQ8TDQ8zLRaOtNq6ZBogjNNMK20DLQoHWi1dKDxcKDxcMBNtdAKj4hb8kBrAATc7CGt4xFpeBhp8BBp88ORxsMxwgRXWmlZ'
    'abRUaTw80wqPGTeZRktLmVZ4ZFoezrS0lGnwkHFrPGht2kybW8q0uaWCW8VDw8OCq6VpfelCKy0LDR4KrRFfaNOlhTZdWmjwUGjw'
    'UGjwUGhNvELreBTc3BINHgoOHnAdD9x0KQ0eKg0PKw0eKg0PK61NW2m1dKXhYaXhYaXRUqX1pQONljyNljzu3UNaLR1wb4jT4CHQ'
    'aulAawAEWuFhaVHa0lza0tISbst0S2sAWFoDwNIaAJbWxLO0wsPR0pKjpSVHoyVHa+I5Wi3taIWHw6UlGg87WqXlaLW0o808ONpa'
    'S0dbEe9oHQ9HW3roafDgaTzsaTzscXiIW+NBgwdPawB4Gjx4Gh56VsdjKrCtaZ4FF5rgTBOcaIJhbVraEzbAJxxgYxj2/eFnwRNM'
    'MOyj6c+CO01wo41hGi0lXFryNMGOJtjSBM80wbQWT6K1eBKtxZNwLR4aLSUaLSUaLaWFJhiGh2uDBa11oT3hpdMErzTBC01wpglO'
    'NMGeJjjSBNPatLjp0kzrS2daXzrT+tIZ9s7DNNHwcKXBw0rDw5XWAFhpeLjSaGmtNMGFJpjW8VhnmmBaA2ANNMG0ntbqaIItTTBs'
    'RfzacXhIawB0Gg93Gg93WmnZafDQaXjYaS2eTut4dFpPq9PwsNPwsNPwsNO2am20DcQabbelRtsTb8YJxo1h2n5aDZeWaJsAzrQ9'
    '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'
    'bK3fxdb6XWyt3+XW+mL7jV1sddXFUkwXSzFdLMV0sf3GLrbW72Jr/S621u9ya32x/cZVbK2/yq315VbEYrtyq1g+W8XW+qvYWn8V'
    'W+uvYmv9VWy/cRVb669ia/1VbK2/yq31pfYb58mIVSa3bhRLMatcihHZbwxhmr62W81v+92dNdmWm49//pe7h+XPP7/EF3/spi0/'
    'dlt+7L/841+Z++Pvp8lbt+33ftr2+xw2/T5Om85vjCvbfu/ztt/HTfY0zrhtv/fb7t+FaePvN95P+IXenw2D2KfJma8PA5NLMqc6'
    '68cf29M9O/oNYybltOXHecOPywsO/Xko+dGewfvwkj3XyXxta3q15xfs6d1LYfbL5jfJbfu5P+PDLfpw5T7cqg9X7sOd9eHKfbiL'
    'Ply5D7fpw5X7cLs+XLkPd9WHK/bhVu0bCH64Vh+u3Ifr9OHKfbheH67chxv04cp9uFEfrsiHu7hpmsxrk82faf9sls6mrx8/lWJO'
    'd45pchtmtjf9OIaw4cenO/TmCXb/8lCbelNrntGaXa15NmuamtWaZ7RmUWue0ZpVrXlGa85qzTNac1FrntGaWiGdyZo5TNOsFdI5'
    'rbmqNc9nza99okitudmaRq15RmtateYZrenUmme0pldrntGaQa15RmtGteYZram993NaU/ub57Sm9jfPZM0fZ+leZSGbTp7OnEo4'
    '/S3Pj8/Jnj65m0ze8ONshh/q5wZ6bUeSm3ex3PzHw9wfP/yuf1fnu/61s5VvOttX7Znjy0LWacr5cpe+oOp6uUvPl7v0crlLt8td'
    'ul/u0uvFLl2my13aXO7S9nKXdpe7tL/cpcPlLh0vd+l0uUtfLl+Xy+Xrcrl8nS6XudLlMle6XObKl8tc+XKZK18uc+XLZa58ucyV'
    'L5e58uUyV75c5kqXG9f+ctEsXE51uFw0C5eLZuFy0SxcLpqFy0WzcLloFi4XzcLl6vBwuTo8XK4OD5frm8XLpY94OQSIlwOfeLlG'
    'Zbygm11ucMXLhRRzuWdtLveszeWetbngs75c0jSXKxXM5Qokc7my0FyuGDaXQwBzOfAxl8M9cznIdZcLpO5ygdRdLpC6ywVSd7lA'
    '6i4XSN3lAqm9nIfby3m4vZyH28t5uL2ch9sLevjlSgV7uVLBXq5UsJcrFczl2jjmcm0cc6E2zsdljelyl86Xu7S/3KXj5S5dL3fp'
    'C65Busy4no1J7WyD6+mpPj3d3tcPtw/3N9/Xu3r36US//tupp31Xn/5aP93S3/735t0U//6X/7xv/fE3Hz58/MjRlhO8S+bm327v'
    '7r57vqv7Lx/53cPdw/uH++/7+7/cffqm0i/+9flG7C9/9zVTRzX1UaYOauqjTO3V1AeZOqpXH2ZqTYuHmTqrqY8ytVYgh5m6qqmP'
    'MnVRUx9j6rxqsXeYqZ2a+ihTWzX1UaY2auqj0uKspj7I1Od7J0VN/ZpXr2rqo0zd1dRHmbqpqY8y9aKmPiotKi0eZmqlxcNMrbR4'
    'mKmVFg8ztc4tHmXqRevqw0ytdfVhpta6+jBTa2fvMFPrNO5hplZaPMzUSouHmVpp8TBTKy0eZmqd8DrK1LNWIIeZWheSHWZqXfR7'
    'mKl1Kfthptb11YeZWvvVh5laafEwUystHmZqpcXDTK2dvcOmcZUWDzO10uJhplaEOczUCuaHmVpp8ShTV50xP8zUWoEcZmqtQA4z'
    'tabFw0ytxd5hYK4v0x1mal30e5ipddHvYabWuvowU+v66qNMnbUCOczU2gM5zNQ6Y36YqXXC6zBT6+KEw0ytixMOM7UuTjjM1LqU'
    '/bAJL203HWZqbTcdZmoF88NMre2mw0ytTdTDKhBNi4eZWtPiYabWAHLYjLk2UQ8ztTZRDzO1NlEPe51fF5IdZmpdSHaYqXUa9zBT'
    'awVymKm1AjlsyY1ODRxW7GkP5DBTaw/kMFNrD+QwU+sszFGmLgrmh5laVzcdZmpd3XSYqXV102GmVoQ5zNRaVx9mai32DjO1Lrk5'
    'zNS6c8JhplYwP8rUq87CHGZqnRo4zNQ64XWYqbXddJipdXHCUaZu2tk7zNTa2TvM1NrZO2wdiM6YH+bV2kQ97K0B7ewdZmrt7B1m'
    'au3sHWZqXcp+mKmVFo8wdQ6Tib8s9r5ir9/2u7tp8iVsN/U/Do2jhwabxg/NXz7093f16U/zx0f0x/pY2+1T/+xI56cvH/n/PDz/'
    '/P6//+Ph4b397JjJvnDMu/7+4fGvN799eHy8bQ+Pnx+W/ZcP++Njf+r3H24+XuvzY559dfMxafqaL3T1BfWFv/vCor6gvvB3X5jV'
    'F9QX/u4LTX1BfeFvvpAm9QX1BTst/vmv5VRf+CJ3nUA+nzHTjzdlTZjOQ1ify5lkyTGy5FgxctqzGLNIkmPmIuvpNFlPp8p6Ol3W'
    '05llPZ1V1tMRFaitnWQ9nSbr6RhZT0dUoJ4+W2V37XImWSVoF1ZRr7LGjhf1dFqUlXesrKeTZD0dJ+vpZFlPR1hkk9XJsUHW05HV'
    'ybFR1tOR1cmxSdbTEdbJEZZGiyxnE9aYqrJoNMjq5Miaruqy5CyTrLEjrPUhqmYz1ch6OrKaulXWIhYrK1BXJ+vpyFomUb2spyNr'
    'mUSVVRU4WRPxVVYnp2ZZcmS13J2sycRaZcmR1aN2suZGqzDekdUFdbKmemuX9XRkTfXWVdbTkTXVO0+yno4sQJhldUGNsEX7sgBh'
    'llWCzrL6bEbYKxWyipxZVtvQCItsstZRG2GBWtYCMONlLZOQ1fowslZMNVmtDxNlPR1ZrQ8jKo1OXdZ6ti6sV5BlPR1RFfXkhIUC'
    'WSumTJH1dIR1cmS9g9BlVdRdVgnahQVqYb2CWdbTEbaRppyqIC3P3vZtvQLjnv/r/e3jzbvb57893P/7X/p9b2f6doWdbv61Pt7f'
    '9p1OH//xXzuc3Lmb/7r9n71u3ZWb/7WX1X24efdw/2Htj4/1wy5XCPnmDz/Mdaf73+lDKm9u4C46cHXg6sC9uoH7jW9f6MDVgasD'
    '9yID1+rAVffnur9T99fMokNrD5Zrb3doaVl1Ked/cwkgaALQEabp5fqmLGTNj3lZC7e9rLcEvKxVM17WMhMvZ11GdB9f7dSSREuS'
    'g0sSe/Pd7fxY75tWPBviwh/64w9P9a5/+grrT/+yzZm/e7h7eP9w/31//5e7T1+p/cW/3ryb7C9/97UYom1djSEaQzSGfEsM0Tld'
    'jSEaQzSGDMaQFqcpfdskwDUP85Po9dlEcVETvWKi1NVEr3mRDrRXvaioiV7zIh1or3pRVRO95kWrmug1L5rVRK+ZaFITvWYioyZ6'
    'zURaXX/NRLP/5l7xzia60HKkz21k1Eav2mhSG71mI7OqjV61UVcbvWqjpjZ61UaL2ug1G/WqNnrVRkVt9KqNstroVRsltdGrNopq'
    'o1dtFNRGX7WRmdq6+1eZfvvw/v3D/U+n+c/fvvvNzY8///mPfn9Xn/401+XPN3+sj7XdPn2aU/31n54fy/v+T999qI8fNq0rncLN'
    '/354fOrf//Dh4fH2+fY3HRz//pf/vG/98TcfPny8oy0n+JfJ/v1PN//n/v/2pw+3//03U55laeyrR/b3D49//acff/1PdvhIN3yk'
    'Hz4yDB8Zv+b4szq+Oj7R8Ys6vjo+0fGzOr46PtHxqzq+Oj7P8ftk1PHV8YmOP6njq+MTS51VHV8dn+j4XR1fHZ/o+E0dXx2fWON7'
    'dXx1fKLjO3V8dXyi41t1fHV8YI2fgjq+Oj7R8bXGV8dHOr4uUlPHRzq+LlJTx0c6flLHV8cnOr6uzlTHRzp+VMdXxyc6vi5SU8dH'
    'Or4uUlPHRzq+LlJTx0c6vm4voo6PdHzdXkQdn+j4XSew1PGRjq8TWOr4SMfXPr46PtLxdVmyOj7S8XVZsjo+0fGbTmCp4yMdXyew'
    '1PGRjq8TWOr4SMfXCSx1fKTj63p8dXyk42tXRx0f6fi6oZQ6PtLxdUMpdXyk4+uHIdTxkY6vH4ZQxyc6/qLv3KrjIx1flyyo4yMd'
    'X5csqOMjHV9nbtXxkY6va3XU8ZGOrzO36vhIx9c3sNTxkY6vSxbU8ZGOr0sW1PGRjq9LFtTxkUsW9FNA6vhIx9ed1NTxkY6vO6mp'
    '4yMdX3dSU8dHOr728dXxiY5fdJGaOj7S8XWtjjo+0vF1daY6PtLxtY+vjo90fN1QSh2f6PhZXz1Ux0c6vnZ11PGRjq9wq46PdHyt'
    '8dXxkY6vfXx1fKTjaztTHR/p+LosWR0f6fi6LFkdH+n4uixZHR/p+LosWR2f6PhVSx11fKTja6mjjo90fC111PGRjq97Z6rjIx1f'
    'txBUxyc6/qyfAlLHRzq+rsdXx0c6vq7HV8dHOr6uzlTHR+6WrN+5VccnOn7Xro46PtLx9cMQ6vhIx9cPQ6jjIx1fa3x1fORuyTqB'
    'pY6P7OroLgvq+EjH15fN1fGRjq8vm6vjIx1f38BSx0c6vr6BpY7Pc3zjqk5gqeMjHV8nsNTxkY6vE1jq+ETHLzqBpY6PdHx9A0sd'
    'H+n4+gaWOj7S8fUNLHV8pOPrWh11fKTj6zew1PGRjq+L1NTxkY6va3XU8YmOrx9/U8dnOr7W+Or4SMfXro46PrLG1xdR1PGJ6/FX'
    'hVt1fKTj6xdR1PGRjq9fRFHHRzq+7p2pjo90fH3nVh0f+Q0sfedWHR/p+PrOrTo+0vH1nVt1fKLj6zu36vhMx9d3btXxiY6ftY+v'
    'jo90fO3jq+MjHV/bmer4SMfXdqY6PtLxtZ2pjk9z/KVMk/22Gt+45/96f/t48+72+W8P9//+l37f29euZw++njn4etOx1zPrsdfz'
    'B+tzB+tz/eDrtYOvtxx8vfm463U/TVPa+Xr/PH5yOz2n7Mf7277T6eM//muHkzt381+3/7PXrbty87/2sroPN+8e7j+s/fGxftjl'
    'CsE+V3LzY71v+5w+3/zhh7nuZJ74bJ76XAbuc/Jy8x8Pc3/88Lv+XZ3v+ssVeHX1sIH7u/q+Pi0/PP10xn/8w7bTbK1NPxecaIIL'
    'TXCkCc40wStNcKcJbjTBM03wAhO8O8K/McGlVJrgQhOcaYITTfBKE9xpghtN8EITzCotjZsbTfBCE0xz6WZpgg0MDy2ta2kDTbCn'
    'CXY0wRYm2NBmDw2ta2lofWlDmy41tNlDM9EE02ppQ8vDE21CfKJNiE+0wmOilZYTrdKaaGs8Jtr8cMUJDjTBtBUANdIE09ZLT7Su'
    '5YSjJRgPlxWHh7gWDy1oGVpaMrT5YUObHzaw+eGy0FbTLjR4WGg8vODGMKzwKDNOMO29pUp752G2NMG0BkCdaYJpr/FU2lstlfZ2'
    'aaW9qLXQBDdapbXQojTtrZay0GrplebSK63wWGlpaaXBw1phL1sumSaY9v7wgnNp2ms8E21+eMItTKO9qDXRVgBMnhaladtaLIYm'
    'eKJtTbPSBHeaSyea4EgTHGiCcYWHowmmpaUFl5Zoux42Wmm50PYAcLQGgKNtEedo7y052suWDrfkgTYhvtDmhxfa0kPaZFphTYiH'
    'afrGvXhO/Njj5xddLnHR+RIXrZe4aLnERfMlLpoucNESL3HRcImL+ktc1F3iovYSFzUHX3RZnuP9t4XBV78c/LPLpefLfSPYbrnc'
    'R3W+HXu5fuzl1kMvF6ZjL2cOvdw37tm++XIHqzv22ZljPdMcO+7MsVHlG/ea33K5Z+Zpye17uU+s8of++MNTvevvfzrjT/+y6Tzf'
    'BnktWZpgQxM8wQTHlSV4WTpNcKMJXmiCZ5rgChPcHE2wpQmeaGOYVng0QxOcaYITTXCkCfY0wYEmmEZLjUZLjUZLDUdLBdbECytN'
    'cKcJbjTBC03wTBPsaYJp06WBNl0aAk0wq6dlnIk0wZUmuNAEZ5pgWJu2+UgTTMvDnlZLe1ot7WkT4h0nmDY/3GlLHhpuyQOtTeto'
    'XUtH61q6ShNMm0xzmdbEo73z4GnTpZ6Whz1tutTTVvGstFp6pb23tNJW4q00eJgm2sxDpwluNMELTTBtNW2nveTRaS95dNo7D532'
    'VkunzR5OtK7lRGviTbRFLRNtUcuEa8TTXNrRXNrRli05WuHhcCviaZVWwL1siZsfpuXhgFsvTdvm0dOWPDjakgeHW3qIm2qhzR5O'
    'tNnDaYUJtoEm2NOCFu0JG9wTdjTBliaYtumBpbm0pbm0xbk0bukhrQEQaQ2ASHvnIdLWS0fay5YRt2yJNl060VYATLilh7RNACdS'
    'Lb3UabLfOD/sbv7r9n9u+4mfOXy+YIoHX9AefcF0tEm/tfO8XWE+WqE/+ILfujBmu0J3tMJ6tEJ7tML56AsuR5vUHHjB5/RY8+4m'
    '/ZTYflff16flh6efTvmPf9h4nm+rCGquPMmFJznzJCee5IUneeVJbjzJHSe5TDzJvFKk8EqRwitFCq8UKZEnmVeKFGBe5lVfhYcV'
    'hdcISrwklQJPsudJ5pUiyeEkR15ejry8HHl5OfK6IhHXFZmnlSe58yQ3nmRgkuJVXxUo2fIkG55kHi9X3szjyutjrzxeXnnwuPKq'
    'rxXIy7wp9cibrYi8PnbkTdBEXsG58Ehq4ZHUwsOKmbciaOaRVAVK5sFj5cFj5ZFU5fFy5cFj5a26rzxerjxerjxeXnhJauGFr4WX'
    'pBZewbkAZyt4Y3nljeWVV32tvOprBb5OwutjJ14fO/I6nJHXuk+0aTjjQudJbjzJC09y5EkOPMkzT3LlSS48yZknOfEkG55kYI3t'
    'eJI9TzKvK5J57b7Ma+pm3nrszHuZNwOXoANfNOBNwy28iL3wwtfCKkWWNk3fuI1wsDff3c6P9b6d9jWS5yv6ePQVv3F36BGN4XCN'
    '9XCN/nCN8+Ea3dFXTIdf0dvDNR7uOd4crvHwCOCnwzUeHsnderjGdLjGfugV+zSZb8wd+eYPP8z19vH0C5ajL5iPvmA6+oLx4At+'
    '454CAxc8XOHRzzAe7aXx6HEYj4w0H7dNdG7vC55EdJvO8407RTrLk2x4kiecZLvynnLmSU48yYEn2fMkR57kypO88CQXnuSZJ7nh'
    'JHsgSXWeZB5WeB48el6LwPMKTs8jKc8jKc9r6npeV8Tw8rLhVV+GhxWGB4+G1xUxPHg0vBrb8Kovw6u+DA8rZqBk3lieeWN55uXl'
    'mZeXKw8eKw8eKw8eZ17rvvLg0fNaBJ63VsTzVvd53loRzwtflYcVlYcVlTe/XHldkQrsivCS1MwrRWbelPrMi9iGx8uRF74iL3xF'
    'XviKvPAVeV2RwCs4A4+XA4+XAy98BeB6bN7MYwC+W8GbbPW8ydbAg8fEK0USr+BMvIidgGOZV2MX4LovnmMX4FI3XsQuwFfDeO0+'
    'w2vdG94EjQG+vwxcHsNbtlp5EbvywlflJalKi9jGxZUnueMk4xpBz0858yQDw1fjSZ55kitPcuFJXniSI09y4En2PMmOJ5k382h5'
    'c1KW1/uyvDkpy3t/2fL62JG3cCLyxnLkjeXIy8uwrsiSp8l+G1bE8HwDj7f1tA9ZfryeO/h69uDrmYOvNx17vW/cXHz79frB12sH'
    'X2852F/CsdfrB9uzH+wv/eDxsB483teD49l6cLxeD85H68H5th8YX2Zj4jduwPf69T5VPn/ojz881bv+/qdT/vQvIzder/XGy7Xe'
    '+HKtN96u9MbDdK03bq/1xs21+vh6rTfer9VV0rXeeLzWGw/XeuP+Wm/cXeuNX2utEq61Hg/XWo+Ha63HQ77SG4/XWmTFq63Hr7U6'
    'DFdbHV4rc/prTfn+WpnTXy1zXms4dNcaDudrLbLma63H52utx921lrXuWsva+Vopf77WlD9fa8qfrzVzztdaq9RrTfn1WgmoXmvK'
    'r9ea8uu1Mme81hmJeK0zEvFaa5V4rbVKvNZapV6rj9dr9fF6rT5er9bHr7Wsna+V8uerpfxrXfYxX2uRNV9rAsrX6ir5Wl0lX62r'
    'XGutkq+2Hr/Wvkq8Wsq/1oZQvNaGULzW6cJ4rWVtvNo1Wddaq7hrjePuWuO4u9Y47q52Lv9a43i92hu/1gRUrzUB1WtNQPVqYfla'
    'p8TLtXZry7Uu+8jXWmTlay2yyrXWKuVaU3651pRfrjVzliutVVKfr/XG+7XeeLvWG1+u9cavdn+VayUgf61x3F8rAflrnS70Vztd'
    'eK1lbb7WcJivtazN1xrH8zWm/GWdpm/dNKPc/MfD3B8//K5/V+e7/rUrtaOu5MxhmvphmqbDNK1HXckedqV4mPXsYR4RD/Nye9jI'
    '/dYF8xs0HRb3vvXthQ2a5sM0+cM01cMi7GHPyR3i5bOZXPs2L7fxH//1jWXJlhN92/cBXJt5kitPcuFJzjjJ3fAkTzzHXnmSO09y'
    '443lyJMceJI9T7LjSbY8yYknmQePnQePnQePHQiPPKzoPKzoPKxYeS2CDuxj86qvxuPlxuPlxuPlxuPlhZeXFx48Ljx4XHilyMLj'
    '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'
    'e+flJmff3Ly/vk23h4ztVmN/P2N3q7G/n7H71djfy9ii5DcqNuWArDSeqkzvlcaOurICrCs3tPR1edHO1VezDVxlMWDnloMzDTY2'
    'tQd2w51eh/01DrtZh/01Drtdh/01Drtbh/01Drtfh/01DntYh/2VDft2f7nkwcZrH/Z9k4mS8xvCqLotc6Nl5fW+7nqnKq+v1B9c'
    '3SMIFequt7Ly+kp+pX1s0JXX+8rrI/eRSBSV1xvulBMBE5l/f5Me/tal/u9Xf0n3abh+yBPLSiVrHwZVNrCiOqZXPkhxtu7pkRTe'
    'V2YNWZtmXGUDFevMOu8isw2krW3gKhvMbcNOtlU/Xx2tL796k2tc+dXGzn0e+P3dzd2Hu9sf84efb6ZTQcwFpUON1FzkO9zIHNiy'
    '167oIXdlhDOVD5VdbVHhKyNWZUS0tQ98ax8pnxB2Qm0UqZzj0jhy2JG1YUfWFtyzjtFMYJsemyl4TWLjXXUFmK6r0TcFc13BZirP'
    'pFhXWYC5ygIy1vFdXTgQTlVeX/mEUIrK62u/hC0tN/yZ2iM4pjZeGudrG1QewbG1R3Csrg1/WtRGZF0bkUV9fSCFOqGomN3Z2EW1'
    'cY1qa1Rbo9oa1S4pqlmzRrU1qq1RbY1qFxXV7BrV1qi2RrU1ql1KVOsGsYlAJdvaxbP2mZ/NeXf98HB9d/vvP+fbPBz4QZ7sm1ES'
    'mlESm1GSmlHStaBkN3dkM0pEM0pCM0pcM0psM0pMK7NY5maUDM0o6ZtR0jWjpJm8I5vJxbKZ+kQ2U7NJ14wS24ySdqJ9M6sMqZpR'
    'IptRIlpRIsZWlKhm8o5qJu+oZvJOamZ0UjOVUmwmF8dm/CQ2M3diMx4b2/HYZtY7sZk1oGpmFqtmKmrVTEWtTDM7Oc34SdEr2Ca6'
    'AwjtFyOK3v8/omJ5R4o+PnEEoZcj1HKEXI4QixF2XIbY/rbRsBhR9rGmwyoAiG75iITlc2Q5wi2c7Hn7xHgxQorlKpaFnO1LRWVP'
    'S0Ltd7r8kjMHU4mxfYlD+xJz0xJ3Z9GLPqVia7/Kag7d0n//W6bvf8vuu95yG2ND6a8ifqn2DiRhiWMFB9QlgLosjlX8o68lugyQ'
    'pYEsBbRXBrIGIKsHsjogKwFZEcgKwLm9xCfqlrlFv3+9lTS0J6lvT1LXnqTUnCQPCi06HN1ErWMlIAsY8nx1OVO6eWVoZO9oZAsj'
    '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'
    'rmP+6sY8rmP+6sY8rWP+msY82OkPXs6OuZC1L1vaOnttVk6VIyJV7YjIykrSxEOVpFtUSU6G6vP/Xr175+XVn69vbt5f36a5zWU3'
    'Tr8bWnj3KcMCGG45Y8wAxriYIYUAMCSAoRYzlC/SYW2sfUtbcN/S3gRaWx7bZIi66mpTcXW0vurqcGg41DocLQ2HXoejpeEw63C0'
    'NBx2HY6WhsOtw9HIcPRh+rsw8x/M0Sc823d2o+j+OpV9x3grJrUkJrYkJrQkxrckxrUkxrYkxrQkRjckJqmWxDRlmZZ8JrU0m1JL'
    'cSa1FIFTS7kptZS1U0v1jBctiZEtiWkpHfiW0oFvKR34U5YqU0YCMCKAEQAMv4zhxuMfYTny6dDZBtYeuunwEjfNL3BTaV7ipuIl'
    'bipf4qbqJW6qX+Km9iVu6l7ipv4lbhq+8023ZxVs4TydO79ovJAnvNNekm53aMlDKx5a89CGh7Y8tOOhPQ8deOjIQyceuuOhewp6'
    '92ZQpqGF5KEFDW0MDd3zVPc8Ww+Oh9Y8tOKhPQ/Nc77B8qYMcaLzhlGPPIPwVAviMPLCkyAGVV4M6YmqeR7S8yrVRJoyApvRKdub'
    'AlvQ0DTqM9Co2ta4dXXPm0Wet96LvB2BqGhzX0ke2tLQ0vFU82zNysTipM9IFaM9zyBED+l5qnnOJzqeQQYeOvPQvKpH8Upux1uU'
    'OV7x6njVvONV8463KHO83RfH28dwiYcmhqfEQ/NUC94+hos0dMebjYno17yNeDfwNnaIe0Y8W5vAQ/P82vAin+l4s5HoIbwElnge'
    '0vHKSUFcywQeOvLQvLQriCuw4Qw22ngPdyUvGEleCJW8wO95iyLPWxR5XhmmeLaOvFop8qZM5BXqibePkHj7CIk3ZRJnyqTt87WR'
    'hiYd10qn/UJSMTry0IaHtjy046EzD83za9LBp0Q8+BQ2K5dyW3+pzA7QBiith9I6KC1BaRFKC1Cah9IclGahNAOlaShNIWkJOhcS'
    'dJ4maAxJ0PhWcTaogFbx1kQJTUJpUH/roHOhg87TDhpDPHQueOhc8NC54KFzwUC910Bnlob2VENHQUM9REO9V0OzjIZWXBpacWlo'
    'xaWhFZeGVlwaGi01NJJraJbR0AyoofFNQ+ObgsY3BY1vChrfAnTWd8tmVu0DkaKfSAxVG2zfVVZoU1ZsU1ZqU1bXpqy+TVlDm7Jy'
    'k7K8bVKWVG1aq83kY0+oTErZZuSxe0lkKyJb89g2EdmRyA5EtieyHZFtiWxDZDP9mzgvLTGedMw4SIrfg97+6iSRbYhskg9mf9qO'
    'WzF7ILIzkR2J7ERkd8R40hPZA4/tmDmNaG/FHMtM1M2s2Yh5RxHrQUdckyhiremINYQi1rGOWFcpYjxxxFqzJ8ZvR5w7PTM3EGOV'
    'I65JHDE39MTc4Jg+SFxfjsQYOzB1E9kDMQ6ORPZAzDsjkR1PmJelZ3Bz4rFFx2P3RN1x5LGTII4l0d6iJ44lUbci6o6eyA5EdiSy'
    'mfOS6CeR6ScDcc4T/SQT/TsbEtsf//WHJWwxEnVLInsgsjORTbS3YPoJcSyFIrI1kU2c88IS2Y7I9kR2R2QHIjsS2YkYq4h+Iol+'
    'IonxRBLjiWTWEMR4IolzRzLnTk9kE+sTwaxPmPGEGL8laSwHtwnf5XMnf7i7//Rmh3mjDyArDnCXIqPBq/R4lRqv0sGRFZ/EV+7q'
    'x3STbhZ/rKlYm2lYm25YW9eutordmu9vt9Sw3Roe0z42bLeGx7QPDdut4THtfcPaXLvauhNiSL2aL01nH5KiXdVfZLe6dJmj5S5z'
    'tOJldouwICSs3ghLLYVHSjgymUVeN6ENFklLGqoN2tOKz2uW0CS0p1gadhSwdhNIWsXZnxJahtIGJK0TbeSa6XCOTcqKJ/hsMVsS'
    '2YLHTpnHDiNR90DUTbRJ6om6iTZJHVE30SYpEXUTbZIikR2IbE9kOx57IM75gTgvNXHuKKJNFNEmimgTTZzzmpjnNXEsNXMsiTWE'
    'JuaGgZnTLFE30b8Hpr2J+XIg5suBmC8HYr7UxPWOIvqJJq4BFTM3aB5bMnUbom5mnifGWMmsB4lzXjJrCGIclMQaQhH9xDN1E/1E'
    'Eee8YuYdZm4gxu9AXDcoYl0VmDZhjiUxVgWmf7Pq2O03zjoiOxHZkcjORPZAZJPqqt03zkYe2wgiWxLZisjWRLYhsi2R7YhsT2QH'
    'IpsUB7tU9Q7j8ZOQE7ZURLbgsUUksjPRJoGoe+Cwt7WPZbJHIps5lsR5KUYim+iDUhJ1J56fCEFkM3V3RHZP9JNEZPc8mwRDZFse'
    '2xH920kim1mfDER2JuY0on87TWQT545jzh1HZHsiOxB9kGgTS7SJZdokEtnEGsISa4hA9JNAtEkg+kkg+kmveOxItElPrCF6Yu3T'
    'EdeuHbGG6Ijr+Y5Yn3iif3ti7eOJtY8n1j6eGL89Mc97YqxyxPjtiDnNkfK8DkIJTWQrIps4L5l71IG4dg3EPdNA3NeUI+WLEe/v'
    'bu4+3N3+mD/8fJO/wPb+evVOqP3rDsg05jxk2rOQqYgPmRRxM1sRN7YMMfAY4satIT5QMcTNbEMMxoYYjJUmsg2RbXls3Z9F2NPD'
    'ecjM5yHzTCoHcRYyXXceMs9jprvzmOnuPGa6O4+Z7oiZ2REzsyNmZtZjuB3bEysK4nEbTRxLzayyiGOpiWNp5HkUCuo8ZOqzkOnP'
    'o+zy5+Gb/jx8UxHX9Iq5pifuc9jzKOzteRT29jwKexXPQ2Y6D5lnMoXCecg8j2cU1p2HTH8eMs8jINkzCUjnsSGiz6MG1+dRg+vz'
    'qMH1eawP7Xlsfdoz2fo8k4cc5zHT3ZnMdOKJBU08saCJJxYccd/YEe3tiPb2Z7JjeB5HvPx5LJ8M8WGBYT4sIE5gRbSJItpEEW1i'
    'iUcBDfHcqiUeM7TEY4aW+JDakh5sWjv9RaI/X9/+NNx9Jf+Qb242t3dihuDy9Ash1YRx+g35kwhxMSEtJnRLCLuxMEcJ0kX7fKJ5'
    '9nLlrKu43PhgKi63SlVdbkx8/vJ36eFTGr+52lZd7aqurlJiRdHVn//36t07LzcWuLl5f32bbg/MHFPiMcovMPG+i8r939Jh3PCw'
    'JZUIFWOqZKy42jjpK8ZUWV11dZV3CVNztZSnz4rJAO//htMLDDBxyIxTNYOgjFrdQa7usLrDV3dQqzus7vDVHfTqDqs7fHWHsBaH'
    'lz3AcR3gyx7gtA7wxQ5wsEL0HXqDqHoLB+Q+M5cXbrSs5UMDvgnZBtt5db969erVF+fVw+rVq1dfnFfn1atXr744rx5Xr169+tK8'
    'ehCrV69efXFeLVevXr36krx6exTIHV8tKuVllVfXXW6kmt9aVvvfEWlQX2hcX2xcX2pcX9e4vr5xfY3HF9N4fDGNxxfTeHyxjccX'
    '23h8sQ3Hl8FPP4zSoL7UuL6ubX2iYIcsaF1xQxmdqnmTQceaZZQyrkaMsa5mxWgqX6twoUqMt3VvYfhDIycL1stRiLqRM1UjFyJx'
    'oG30vKGYX9XWDoX304+1zPReV73fo3WNI6qoZNXloW4fxetDvU+vuvf5Vfd+fK29357LkwW9rwxjk8unu0kFzqZclUGMqMt4tq5W'
    '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'
    'Wre6VapbXSXpVteVutWVuG61HtOt1mO61VMIuTLyHznwt0NaPFLhkQaKdLrocFn14clKv1nfb8C/3/AW63iyg/uyTHhkhCMTXmUi'
    'qAx4pMcjHR5p8Eh4JpBBopFiyHjkCEdmgUcqPBI+PKoTeCRBJb5C6fClWYef4x2+2uvwwa3Dh2Aflpdm060+gUYq7/EqJV6lw6tU'
    'eJUWr1LjVRq8SjhS24hHCjxS4pEKj9R4JGHELR7p8EiPR+IThRlf2bYA97MFW5Miosdq0n2TytWkaJOq1aRok+rVpGiTmtWkaJPa'
    '1aRok7rVpGiT+tWkaJOG1aRok8bVpGiTptWkaJN2q0nRJu1Xk6JNOqwmRZs0ryZFm3TdL0Wb1K37pXCTrvulcJOu+6Vwk677pXCT'
    'rvulcJOu+6Vwk677pXCTrvulcJOu+6Vwk677pWCTqnVBijfpum0CN+m6uQc36boFDTfp+qAEbtL1cR7cpGsRBTfpWurDTbouSOEm'
    'XbdN4CZdN/fgJl23oOEmXR+UoHei+rWIgpt0LaLgJl2LKLhJ1yIKbtK1iIKbdC2i4CZdiyi4SdczUXCTrif34CZdz5eiTdqtD53h'
    'Jl0fOsNNuj50hpt0fegMN+n60Blu0vWhM9yk634p3KTrfincpOt+Kdyk634p3KTrfin6CampXT098+sA0x9MGJYjl1ppKmlsT1Ju'
    'StLuabmC+sIOKfFIAUeaEY8c0EjpEh7Z4ZE9HkmwZcYj4U4kvcAjJR6p8EiNRxo80sKRHV5lh7dlhx/xDu+XHX72JPwcT/hIlPDx'
    'MuGjesLnnoTPkNW/RVSAjPhqo2+umDRde5JSe5Jie5JCe5J0e5JUe5Jke5JEc5L02Jyk0bUnybcnqb24pNtLKKNpT5Jtb+Dac2/d'
    'XBCQybcnqUEr2fYkmfYk6fYkqfYkyfYkNVfCyTi2Jym3J2loT1LfnqSuPUntVZW5vaVlbm9pObS3tBzae8o8DO1JajAutVfC+fZq'
    'b9/eCsWH9iTF9iSl9iS1Vwn45uKS6HN7kppLu2IQ7UmS7UlS7UnS7Umy7Ulqb5O5vYFTDVoptfdQPjV4dKF2xhUgDR7p8UgHR1af'
    'RTp+ZL36xFQBcoQisxJCKDxS4JESbkvV45EdHpnwyIhHejzS4ZEWjzR4pMYjFR5JmJACjpQjHomP6hIfiSQ8ncnQ4ZEJj4x4ZMAj'
    'PR7p8EiLRxo8UuGR8BAsBodHejwy4JERj0x4ZIdHDngkoWTFjniMm1p9b/a8v7u5+3B3+2P+8PNN/sL8Id/cbK60M8vjQ41UOKVR'
    'VPWNtLKHumleRzft6+imex3d9K+jm+F1dDO+jm6mi++m7YXouSFIihMUKz+n2I1COXt2is/Pxv7sFIezUxzPTnE6O8Xd2Snuz07x'
    'cHaK8zkp3hUj5V4R3GLF0xKhOLSqoA9x4omckyqq6c2LM9oRY9jyTiyv8Pb3TbQuDsBSybnPa4XNXQp2Efb+evVuY5T9vzxP721Z'
    '5XwafatdDky60lTLdFS6pdK5PuOodE+lB6ZHCqq/75+agNN7aiTIVO0dVbumaudGYEPVHqnaLVW7pNK5cUZR6Z46qlS64M5VR6VT'
    '56qkeuT+ORq4ZaiRQHKjGHWuSm72oMZIyc3a3GqJ6u+Kql1xR5VaRypFXR1IKl1Q6dzVMDVGKmpNoLgeSY1iilpxKGpeVdQ1n+Lu'
    'LVGrJUXN2ipSIwE3AlPnqshM7bzdzh29p9Kpu52Sm1dHKp3qM4LrM9SKQ1J3mSW1npHUKCape9iSuv8uqU8meOvVHZ2a+dA7KP/3'
    '9jf93T/y/VPqb+8fPo5faLv/+81br5X4+kzyy7/+IX3Ib35//T+/eaukc08eWr5LD5/SV8rn/716987Lqz9f39y8v75Nt0+UvJVG'
    'qzn+7+7uHh8e79PPb97nx8fr258efvPWGvnkbj/cfdj070ur//6fq3+9u3/Im+uMfYK9+m1/P3nyKbWJT3Xop734cul/ptu/v1Hb'
    'TvontD/l+48P6SZ/PYX+5S9X75zd2OD+Ol29u354uL67/fef820e9roc9bGXrX99Rm/22nlbKkK5qx/TTbo5IMKb46OWP9zdf3qz'
    'a/HG7rfWde+Lf/sbYpuRV6Xd0fHqXz5c3x/ojTzQm50xrdm9Zv21hXh6939OH9JD//HhS5tf/7C5t7766/X/XucDd4+hDCX1ZlS2'
    '/fjj7T/yw+P1T+lxw9sjuTmn3f7PZlzF1R/S/e1hNU+95Jk5vXHRuBmVLt8//nN+n7q9yPA2Vg7stx8SeBtVtZvOGiTEWh+ZR8nD'
    'tjWbiXt3+zjm+/v0OG/ePczSQPzWHxlwu2l73d2n22G+Y3tzsSw2zbNEsZ5ZC7l4JPJaMXv5gdljw9WfPnbp0BC7UDx95hmucjLP'
    '20HXONy8IHU8UAv3y7/81+2Q73/7+Jj6v1cz7Ofk+ePHx7uNj9zstZd1yWIvHth4vPHvNpPkl/+eNYQNtRF7HiWrp8zT1uKYgz89'
    'lrYpReqMt9/YLP2xyrd7FVPRBJt1af10KP+8qciGadFinNsbfL3nebtubqq2+/vr4e7+qxX2/77xRf3LtV/+9BRZ6Yxqr7GotOe2'
    '9Sf/FKEO56TPtZvdO6D3VvnDLiOjnL38myH7fAcT3WyTf7tLw2Z0tl1Q06JS7kVftZeAHh7SZuRvP8+XXWr+GrO+/beyemTvDjM+'
    'Y/d7b2od9mljPVv+bG+mZND7BlBHKkcllCpt8Jz77Y+SrMwuT9uKJUNVsi5ZxD9QVO6Ry89RL1RUUqvIUFzv7C1/ajL7XMNn54JS'
    'Xs62mAs2TumKNs8UzU8bu8LFqRKzzZ6bdj7a+eufyaH7aUTaJZ5wfP1oFuGPLxH3bvD8wIsQZ1v8/iY9/K3bFnV/Sfeb0P7w1Vzf'
    '/tPVbvPk/WO63/c9XVwcz7aqtUzhmmrvJs+v3oWZbVC2xCyyxGffU3HftdUSExxfJ0hZNMVVRZsnBpitLPcQ9cH1eLG4d4NDkcSL'
    '2WZFZf7etk5Z49nFyh7gwLT75fUJ7WYbz4+kr2gzM5Lzmp8PLnHvTZm3h1fowlk7d/Vcr4zbu0E4Wr9Krcxci2ei02znK9rZYoXP'
    'O4qt7aG0RUp/MbrZ8wt/JCTKaPeuP1plT3dAjyRgGUIlXuq5Bs+GdGXk3PUHyw5f1IlvR39PnS1x6f0lnC1a9e2vvI+MuIxzV5/0'
    '2dC3x4uMuPe+11tzfJnpJpsZx1ZLcn93T5dNs98J9eaf3ry/HvKb//iYHx7nEJMHPu/yff+3TXG+icxHbvVsVXn4EdHGAWavft66'
    'Nvq5BuVvEhY3239xcK/ZoQnkYlWnrLFursHszNH7xUqVY/9abjz8cJ8nBUXBrZURlU2mTwLlkbjoZvs2E+bqBU3WPsf9Wno/24Vn'
    '1mJCz/b4eR9QXlU1kEGGujsY5avMaoydu/5o1abnh6T8beOnzb4plT/77jFf2qz55Hynf96kr9uPT7aWPv+hxJhauBpjKq9PMsj+'
    'y8Nvy5YxE2X/7//+PwAAAP//AwDTxwSyuc1PAA=='
)

# Tabla header -> BAO de datos Ogg (1359 pares, gzip+base64)
_EMB_OGG = (
    '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'
    'a/yoiK/qCkV1HfyosBttDBfMnCcqY61lVQf+UZfCj2osLFfIj6rrNxTeK+RHSfz4KswF5EeSzlOm+VGRHyWxwU5Ve35U1HPW139n'
    'qOrs0qLqx4+quqO/rlXeq6BOraZwuqGqU8lFwj7mIPKj78byqzKgHxXSfu5o6t6AHxWdEm6uY7iP/Cjnka8z30Wf6l2SSppfRv77'
    '1a692Sv0X/nqz2EeBYWkj1CbGYtbBWSfXTbfvQqH9VtVIT6qqtfNNbfRFHXri/uugGZ7pZCar9LvzFh1f04pYfCsVL3uxF0OS6zK'
    'j4SH6TD3ozp1LjvZWI+iQlqDj5N5hPzo+J71rbY/KpC478byyVqmkJog5m6ZWQGJS9c1Y+tw68uXD+rbzn9U1De+20md4dFR2bGE'
    'ZoaKTomdzm3MI/Q/z7uP7mP8UVVc16vzvFeqehmur431CP3PN9XbzU4mhcT55o1FQv/z9jI8mF+G10jzg8yYqupIe+sTKD+q0iOf'
    'juN9Rh9y3ZLxdTMrdDs0P8Yxs0Ld+8NxLn83Kz1KktPxnJH/9hPEehsq9rk0b/cK+e/4WiEsFXp0v0MKbK+Q/+Yu3sjoL/LfIVsx'
    'rqFW1Bjv6UYHVR/ymB/cwlTgdHVJeMb2CvnvkjTUxhvIf4X5/SSzInWKZH0nspgKOymaX7yZM/KyPMOshopTJEe2OfOckf+e4quz'
    'VOjRkHQ386yQ/5abkje+TN2+0o8/xqcg/xUN883ogupDXleCNzMr1IElnd9GQ9GHvGtJI7JlADZR4vkuLGBqx0kB73dnySmqvrGz'
    '7oH8USesShV7x1qmsAlZbq5s65B3l3P7tVw4aievriH/qMiPajwusbdC3j18L83EosAmdp+9J+YvsIkj5qxm5i+wieaG16d1flTU'
    'r9aWFRsq/GD5zrvzXqnbVyR1rs58F3HsljD2spdEH3KR9Eh3C/+oqAMPd4OxG+hDHt8FHN7MCmc8JTfsxqegD1lC4Lm2+a6qq7Qb'
    'hpkz6lcjrWO0G/WN8x2MN/uMCkYva8zO30UFY/W52+UVoYIh6Xwbl7mPCkauXycbSx0qGEVC8zbMd/Up+6JvbPtRgdTkEGx8hQqG'
    'hHWpD7NefYuChLGsKahgxJxm34Y6Vd0sLBMzoILhazmhsOVHBUNEQ1bM3EcF4+5VrvELTUcyvXjeZ1QwUgt5OR7b1S0ZYiU3Sywq'
    'GCJzsijeK1QwxFWVZCIKVcEo4lUWywYqGCXHav0RKhhb7G3a5rtV1QnHXmYsPKxkgzGaWeF+pNtWNNGIuuVm5jii+WXk3WLozmb+'
    'omdb1juusSqqZzsON7v5ZfRRSGKVKnMfPdsfzn4q74bq2f7Oq5vYGz3bx+esK64/KjKRtOuIrCno2T4SxOp7en9UVCCdRDrGw6Jn'
    '29043TZj4WG32H7j2dGzXXKr3sRXQ1WoahjbrKirm4j2NRHFUKfs77HRCHq2y1pfMZepiKBSExfKNnaokz4nn27WiwpkXicZ+zwU'
    'f3NZJouZCmkV12XyI/Rsn5jEl/F6Vc+25CzeSB16tkVBt1vmlxUSN48zUoee7ZO3xF8sOejZ/lrQ82V5Rs+2l0zZR+YvbrkZX0Ow'
    'ybvVLTf71hXZquCWmy/xSsb/4pabekdLjjUFt9zUuYPGB3/Urao9os3mu8iA5jgusDzjlhsxC2L7eUW45aYnX3X3+48KBDDsrwLC'
    '1KDQfwmTOPrCLTf5bLcjrwi33KS72w7MQdwYc1ababE8qxtjugSMJvrCjTGSL9xpKmO4MeaOHpOpfeHGmFt2qIaKG2PyF7Ya2cCN'
    'MUPyY2+yY9wY08Z3qJXXi5MCvhxxwOa78GV1pThZU3BjjCRDPho/iBtj+pJ0N7Au4BzBFLI+v/+j4nadtncyPMI5gi3pT5k8Z5wj'
    'kADrXJOJ4BxBrnvbzOuoDsktNpqlDucIvqxzOuY+zhHs3/1mrIM4R/CdVugmzsHtK5IqxrzML1eFmMwWWCZx+4rk7J+3YyrOauUq'
    'isYyidtXvsMe+pzIj4rMa3vxsaxl6vaV6lZZhooKVfdf0Ympqlc8jW78Pm5f+Vpd6mIO4vaVfcKNRrtx+4q4ZkkZeEW4fSVIdtAM'
    'YoLbV1oXgZ68Vzjr0c5X/jBjUTm5koWauA5nPXpJN0Tzy6hAStrWTayCsx5DXGQzVUSc9Vjze3/D7JW6f6OOe8yc0YFTvrOYrL9X'
    'vRogtMpSd5F5lX3F1DP1KMsQqrH896qbeFdnDfUOiPbILrHd8MDLokQcjiNkD7yszFLrKUyFX1hdfPViKs5qSaZyOK7zwMvOGWF3'
    'MxYIggzsHD974GVF1Gj3xFQgRCLsl6vxHnjZ2Hu6ZX5Z8VecsTO//PjrJYUdw1CXuq1Cklyzk+gcmOG7PYup0N/4ASqRqcjLVlqJ'
    'Y0KPDsmyxzA+xaND8qQ9ZuZfRodk6+c01lCvOiRHG8dIjld+X0LkZL6rKp/zJMNBIIBVVOVw5OaBALqaJDAfTFWdA2WmXJkK/a1e'
    '3JGZlXoXoLbSzXenkqt+t9krdP58l3A5MyucUPCSLrKGqhcWmlj2bfQICGBa416OVdQLC6m2kbkOrF5YaGJh+mIOAgHsV/jAWIx6'
    'YSGs773Uy1TcwLBdvZ33GQhgDrJkIxtBVbZDr8fMCpVtsf2Ro2u8lRyvH2NypOqBAMb0xem8z0AARxh5G3kGAviF5YHRB/Xuw3c/'
    'sE+GincfpiQAjGmqdx+a+MkdeTcUxieJpueKq3rZYey6G+eD+mUHkbnZzdioOm9FepiDwPjGLjlxvV297NDqlBWwhqqe/ORKGMwF'
    'YHyjiH4mMxY9kGe56Myc0dtzfM3coaFedhBjt6v9ZXXavZSzzV6p2vVa01hvYHypdhnKVjSq0+45D0Z51MsO4uZS5/xXveyQzqye'
    'kXT1skOc69TMs1IY3/qAHNb9pLqUxWVe5i/uKXJlzmW/i3tOus8S5jEVcWw9tS1DHfpGvuNZQ4EAniYJ3jbUpU7pjngMdavTspLh'
    'sWwkhRFIgMgVZvXCwghllchzVj2uq4pk8XeB8Y3v9W4TFQDjc22OarQMGJ+YyVQ49lYvLMy8hw/mu+DRl/9yHVi9sHAluEqcAak3'
    'FEr3dRhfBhQv17zyMCtCDfl8QseWECieCEff3vwyaoxl19lZy4DiueRbN9qtbhPykrFzVU29oSATrPpG+h9VdbGKpeRqnnpDoTQZ'
    'a39ZobS5LM7Z1RsKI4saMhbj9Wm7IMkEWySgeJJptjjMrNClvMMa3Bmi3lBoMeRrolygeKGFfYy3Ut2zc0sEbX4ZvqynWkw0AhTv'
    '7tvLNWMRq4hun2x2A12sJaxj5EqheF/DSmSJBYqXv94txjXUGwqh9NKPGQsU79w4KnscoHhfP0PmrE2/oVDTaowuqTcU8mrbm9gM'
    'KF7ye5mcXb2hcK+Ycu4cUG8o5BX6bez3q9Lf9l3EzFTY2CUJ4zJ7NVVtZGW7G6pu5mYwXgMoXhM/WIJZL2rIW1zdYf5WdROvLD7z'
    'itClXIZk5Vz9UG8onPE9icqzAsZ3+3SD8TL1hoLwqDjDwabuchx+Z/Nd3AvhJfjiupl6Q6HfEYOxwMD4PqhmV/NdxKJzDm/0Fxhf'
    'nn3fwnoEJK61UHtii9RUV1genTERr7qFJaZPZr1dRYxBkiCWWGBtVaRjmNgbWFsJ+97K8gysrZwzh8kmFNaWyt7cQ+WBtZUZSjYZ'
    'QVenZtLe9rtN3TaT3OKdBNa2VnfVcAFYmwTI3tTb1YsS38vg1vJ3dRJTfsjEk1299RacQVrVixJfL8Qx8TOwtniPRFg8Z2Bt4iO/'
    'q5eY6vUbKC6xPKv7ke641VQwgLW5foIEQkxVN5aH5ox9Bpr23WtRj6EinnTfq4nMX6BpV2SyRbNecPCsUE1GDzSt9O0G42XqzQi/'
    'vYsmcgOaVstMkfs21ZsR6XgJks3YozCvnRbbWKBpq8lnjJ0EmlaT/053MBV9uaFJ7shcUG9G5O8CHd7JqbrQz5rDUJO6r6A17u1R'
    'b0bId0XimQsaTRNTaCRWoWniI7rJcIGmuSimbhgq+lVijM7EKkDT+urHGR8KNC3c7yZts884B+TPdyEwU9FPGE6vRp6Bpokwl2vq'
    'hEDTahuncg+zejNCTMgYgccCIVrprFPYayiEKHxIK8szEKIt9vYOMxYaKopiKwlbnVsctXF3ln5TQNRz2V/GDWbfkVZTCcSbAqOL'
    'tePeePWmwHcfo/ULeFPALYlHivll1S/6vXrBmrJVtjj6LWZFCg0fxdpY4FaSOC/HpyrUqwHhe9aCOwfUqwFrDboL7kdFVr677yYf'
    'BG6VXB2Xez7VqwHfo1qOu2jUqwGr19gc77PCrb73ck10Ddwq3VmqqcgBt/pe+J3GpwC3umI2bjVzxs2WPZXBHUfq1YDzRcEmWwRu'
    'tSSVjM3sFTBc4YHpZFOvBpT73WFmvqv6kW6+jP+qVwO+l7D1/Rs/KvL9M5PnHjn1LsB3LfVK7I+uivp6WSauUwhRO/2aFQEhGiu6'
    'OZhHV92gkvoylUAgRCvs6ZpZ71Z3C8eWWVOAEAmHag/mu+o2v7QGW+AAhMiduyJHqsHpM9pflYqpOIOfst9crQ1AiLzY2MzV2gCE'
    'qMY9LtucAISoliQKbuas7sARlozGVPXybKp1me/itqgkOQxjbeodBO/F1a3AVNzhfF0PyewG7v0QWxa92cmlbE4ezqwImiImNF4z'
    'Vr2PIwluNCtS71utFBLPGQiRJDSpsY1VLyyUPqrBNdQLC3l/j5ttpsKXrfrdAsxUZG39azU1s0LdbLrUGG1RLyzMe0TgzZxRf/76'
    'stnmqBcWpsQxl2N+9cKCRHVttcRUVNWGxNbVrEj31tZsuK/e4N5r7m32CvxtKwz2OOqFhRNaCdGM1XcslG7mrN7gFksezZzVG9yz'
    'lsoZrnphQWK+EdgfqRcWbh1usuVXLyyEO+Pmvmv1wkIPYRzuy1UvLEi+L8bBMbWqO6xO6eaXFb7wPZ/EcqXOiN1c1zZjcUZMzErk'
    'XEO9sJBu6iOb3ViqCjHNCbKgzohtse7cGxCAEJ0cS+T8KOCMWPKrVK4jBXUKrHz3ijF/o/J06Xbuvgvq7e/vFg3OQwMQovyl3ddQ'
    's7ppuWXOQ9WLEqVL4Me98epFCQlbWjccBEIkaahsF3MBCJG7V7SU+RsVxudu5LpZAEIkJvOUxFIHhOi7+c4Fs6KtXuj+XkJgqjqd'
    'VKup5ql3LmRK0/H5I/WShXctLKP7OMnVdvkwYKbiJqJWmufTsuolC3t70o+KlyxkwbOa7+IkZpBM1MgzOnDKjN8ZX1C/uwyx3ipe'
    'QaPSTZ/CltWI7DimYjdW6FlnIk2fwpa4rXptkZo+hS2Cn3Y1s8Ip7FLp9Y0fVXWD3+I0ctH0Key9VqST1E2fwq5nZ/0m5o/a1Wtf'
    'bg8zK1SoJHh22j43fQpbPlqd9nRNn8IWp5C7ruQ3fQq7p9H0bWA/KpCa31UWi6nIf9dK13xXvcrk+s2Ox6qYYVenX+74UdF1kHep'
    'h7mPmEHitu9tAKaqd1vC6ol30qvTHDPlxlxAVFDiPlvdwf6jNtWjPnNhuVJRwcyh21mpVy/76rrq0vTJcVmwX93sJGqMN0sgZHYD'
    '/cBfeXIzB9XJccnJzzRzRlQwJL3XNfOmT47fXlM7LM/qZi0J3W5nmURU0L63KgrvhooKJCQ43lCVhtaTN3NB3fHrfauL5QpRQTlO'
    'RJr5q6KCUfOdZs6oUIl3PoW5gKjge7B4LENVfUF7N6Mp6uT4/7CEiArqSSK1Zs5b3Wk8RYmZqm7zk+RQ5TgnKxuby0pbv5P+o/5x'
    'MEue4jTi+aP+cTD31ldQt63+qH8czOKOqj79/aP+cTCvcudRdxr/qH8czOLWJCgws/rjYJawfeVlVjQf9WtoVkjrj/q3k7nN7wpg'
    'x9T95iwmJyhM5Ef928lc+651m/XeN3aLrCtP91GfrcvDj3Md/7LHPkvuoLujf9S3z3uWmd35Lxcmu35BnwAA'
)

if __name__ == '__main__':
    multiprocessing.freeze_support()
    if len(sys.argv) > 1:
        run_cli(sys.argv[1:])
    else:
        run_gui()
