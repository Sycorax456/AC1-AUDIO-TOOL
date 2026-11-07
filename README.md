# AC1 BAO Tool

Herramienta en un solo archivo (`ac1_bao_tool_v22.py`) para **extraer, editar e inyectar audio en español** en los archivos `.forge` de Assassin's Creed 1 (formato BAO de Ubisoft). Tiene interfaz gráfica y línea de comandos.

> ⚠️ Proyecto de modding para uso personal. No incluye ningún archivo del juego: necesitas tu propia copia. Haz copias de seguridad de tus `.forge` antes de modificarlos.

## Características

- **Extracción rápida en español**: descomprime solo las entradas necesarias en vez de los ~18 forges completos y genera `spanish_map.csv` (stream ↔ header ↔ rate).
- **Exportación a WAV** de las voces (IMA de Ubisoft con decodificador interno, y Ogg Vorbis).
- **Inyección de WAV editados** en los forges:
  - **Ogg**: dos métodos, *agregar al final y repuntar* (recomendado) o *mismo hueco*.
  - **IMA**: reemplazo en el mismo hueco del forge de voces.
- **Sample rate automático**: cada audio se encodea con el rate, canales y muestras del Ogg original de su hueco (48000, 44100, 16000… el que tenga). El WAV puede venir a cualquier rate o en estéreo; se adapta solo.
- **Verificación** tras escribir (índice, FILEDATA, CRC de chunks, lectura de cada audio) y **copias de seguridad `.bak`**.
- **Datos incrustados**: el plan de extracción y la tabla de audios Ogg ya vienen dentro del script; no necesitas archivos auxiliares.

## Requisitos

| Qué | Para qué |
|---|---|
| Python 3.8+ | Siempre |
| [`ffmpeg`](https://ffmpeg.org/) con `libvorbis` en el PATH | Inyectar audios Ogg (obligatorio) |
| `customtkinter` (`pip install customtkinter`) | Solo para la GUI |
| `numpy`, `python-lzo` | Opcionales (mejor remuestreo IMA / más velocidad LZO) |
| [`vgmstream-cli`](https://github.com/vgmstream/vgmstream) | Opcional: exportar WAV completos y comprobar el decodificador |

Comprueba ffmpeg: `ffmpeg -encoders | grep vorbis` (Linux/Mac) o `ffmpeg -encoders | findstr vorbis` (Windows).

## Uso rápido (GUI)

```bash
pip install customtkinter
python ac1_bao_tool_v22.py
```

1. **1 · Extraer**: elige la carpeta de los `.forge` y una carpeta de salida; pulsa *Extraer español rápido*.
2. **2 · WAV**: exporta los WAV para editarlos (`<salida>/spanish/wav`, y `<salida>/spanish/ogg` para los Ogg).
3. Edita los WAV **sin cambiar sus nombres**.
4. **3 · Importar**: indica la carpeta con tus WAV editados, marca el idioma (Español / Inglés), elige el método de inyección y pulsa *Encodear e importar al forge*.

*Restaurar forges desde .bak* deja los forges como estaban.

## Uso por línea de comandos

```bash
# 1) extracción rápida + mapa (+ WAV con --wav)
python ac1_bao_tool_v22.py fast  CARPETA_FORGES CARPETA_SALIDA [--wav] [--vgm vgmstream-cli]

# 2) exportar WAV (necesita haber hecho "fast")
python ac1_bao_tool_v22.py wav   CARPETA_FORGES CARPETA_SALIDA [--vgm vgmstream-cli]

# 3) importar WAV editados
python ac1_bao_tool_v22.py import CARPETA_FORGES CARPETA_SALIDA CARPETA_WAV \
       [--lang esp|eng|esp,eng] [--modo append|hueco] [--destino CARPETA] \
       [--plantilla _plantilla.csv] [--dry-run] [--no-backup]

# utilidades
python ac1_bao_tool_v22.py check CARPETA_FORGES CARPETA_SALIDA --vgm vgmstream-cli
python ac1_bao_tool_v22.py full  CARPETA_FORGES CARPETA_SALIDA
```

Ejemplos de `import`:

```bash
# Copias modificadas en otra carpeta (los originales no se tocan)
python ac1_bao_tool_v22.py import forges salida wavs --lang esp --modo append --destino forges_mod

# Modifica los forges en su sitio (guarda un .bak del original la primera vez)
python ac1_bao_tool_v22.py import forges salida wavs --lang esp --modo append

# Solo simular
python ac1_bao_tool_v22.py import forges salida wavs --dry-run
```

## Métodos de inyección (Ogg)

**`append` – Agregar al final y repuntar (por defecto, recomendado)**
Los chunks modificados del paquete `.compressed` se guardan sin comprimir, el paquete crece y la entrada completa del forge se copia al final del archivo repuntando el índice. El audio queda a **calidad completa y sin recortes por falta de espacio**. El forge **cambia de tamaño**.

- Con `--destino`: escribe copias y **no toca los originales**. Con este modo se omiten los IMA.
- Sin `--destino`: crea un temporal, lo verifica y lo sustituye; el original se conserva como `.bak`.

**`hueco` – Mismo hueco**
Escribe en el hueco original con exactamente el mismo tamaño; los chunks LZO se recomprimen hasta caber. El forge **no cambia de tamaño**, pero la calidad puede bajar si el audio es largo o complejo.

## Nombres de los WAV

Deben conservar los nombres exportados: `BAO_0x<header>.wav` (Ogg), `esp_0x........wav` o `Spanish_BAO_0x........wav` (IMA). La herramienta usa el nombre para saber qué BAO sustituir.

## Sample rate

El rate de cada audio **es el del Ogg original de su hueco**; no se cambia el rate declarado en el header del BAO. Si tu WAV tiene otro rate o canales, se remuestrea/mezcla automáticamente y el informe lo indica, por ejemplo:

```
OK [48000 Hz, 1 can.] | WAV 44100 Hz -> 48000 Hz | WAV 2 can. -> 1
```

Si el WAV es más largo que el audio original, se recorta con un fade de 10 ms (`RECORTADO` en el informe); si es más corto, se rellena con silencio. El informe completo queda en `<salida>/spanish/import_report_v21.csv`.

## Limitaciones conocidas

- Si un audio aparece en varios forges, el modo `append` usa solo el primero válido; el modo `hueco` los escribe en todos.
- Un forge no puede superar 4 GB en modo `append` (el índice usa direcciones de 32 bits + banderas).
- ffmpeg no se puede incrustar en el script: debe estar instalado en el PATH.
- Probado con pruebas sintéticas y el experimento original; prueba siempre sobre copias de tus forges.

## Solución de problemas

| Mensaje | Causa probable |
|---|---|
| `no encuentro ffmpeg (con libvorbis) en el PATH` | Instala ffmpeg con libvorbis y reabre la terminal |
| `BAO de datos no encontrado` | El WAV no figura en el mapa; ejecuta *Extraer español rápido* o indica `--plantilla` |
| `no cabe en el hueco…` (modo `hueco`) | Audio demasiado largo/complejo para su hueco: usa `--modo append` |
| `la verificación encontró N problema(s)` | No se aplica nada al forge; revisa el registro y repite con copias |

## Licencia

Añade aquí la licencia que prefieras (por ejemplo MIT). Assassin's Creed y los archivos del juego pertenecen a Ubisoft.
