# Validación de Uniformidad dR (Fontaine–Perrin–Riou)

## 📋 Descripción

Este módulo implementa la generación automática de certificados de compatibilidad Fontaine–Perrin–Riou (dR) para curvas elípticas. Los certificados documentan la validación de la uniformidad dR: las dimensiones de $H^1_f$ comparadas con las dimensiones de $D_{\mathrm{dR}}/\mathrm{Fil}^0$ en primos p-ádicos.

## 🎯 Objetivo

Validar la compatibilidad entre la cohomología de Galois y la filtración de de Rham para representaciones p-ádicas asociadas a curvas elípticas, verificando:

$$\dim H^1_f(Q_p, V_p(E)) = \dim D_{\mathrm{dR}}(V_p(E))/\mathrm{Fil}^0$$

## 📂 Estructura del Sistema

```
adelic-bsd/
 ├── certificados/
 │    ├── template_certificate_dR.tex
 │    ├── certificate_dR_uniformity_11a1.tex
 │    ├── certificate_dR_uniformity_14a1.tex
 │    └── ... (20 certificados en total)
 ├── scripts/
 │    └── generate_dR_certificates.py
 ├── validation_dR_uniformity_results.json
 └── VALIDATION_dR_UNIFORMITY.md (este archivo)
```

## 🔧 Componentes

### 1. Datos de Validación (validation_dR_uniformity_results.json)

Archivo JSON que contiene:
- Metadatos del proyecto y autor
- Resultados de validación para 20 curvas elípticas
- Para cada curva: label, conductor, rango, validaciones p-ádicas
- Para cada primo p: dimensiones de $H^1_f$, $D_{\mathrm{dR}}/\mathrm{Fil}^0$ y estado de compatibilidad
- Resumen estadístico global

**Ejemplo de entrada:**
```json
{
  "curve": "11a1",
  "conductor": 11,
  "rank": 0,
  "validations": [
    {"p": 2, "H1f": 1, "dR": 1, "ok": true},
    {"p": 3, "H1f": 1, "dR": 1, "ok": true},
    {"p": 5, "H1f": 1, "dR": 1, "ok": true},
    {"p": 11, "H1f": 1, "dR": 1, "ok": true}
  ],
  "passed": true
}
```

### 2. Plantilla LaTeX (certificados/template_certificate_dR.tex)

Plantilla base para generar certificados con:
- Encabezado institucional (ICQ - Instituto Conciencia Cuántica)
- Identificación de la curva
- Tabla de resultados locales p-ádicos
- Conclusión automática según validación
- Firma institucional y trazabilidad

**Variables de sustitución:**
- `\VARcurve`: Label de la curva (ej: '11a1')
- `\VARpentries`: Entradas de la tabla p-ádica
- `\VARconclusion`: Texto de conclusión

### 3. Generador de Certificados (scripts/generate_dR_certificates.py)

Script Python que:
- Lee la plantilla LaTeX
- Carga los datos de validación JSON
- Para cada curva, genera un certificado .tex individual
- Reemplaza variables en la plantilla con datos específicos
- Genera conclusiones apropiadas según el estado de validación
- Reporta el progreso y estadísticas

## 🚀 Uso

### Generar Certificados

```bash
# Desde la raíz del repositorio
python scripts/generate_dR_certificates.py
```

O con SageMath:
```bash
sage -python scripts/generate_dR_certificates.py
```

### Compilar a PDF

Para compilar uno o todos los certificados:

```bash
cd certificados
# Compilar un certificado específico
pdflatex -interaction=nonstopmode certificate_dR_uniformity_11a1.tex

# Compilar todos los certificados
for f in certificate_dR_uniformity_*.tex; do 
    pdflatex -interaction=nonstopmode "$f"
done
```

## 📊 Resultados Esperados

- **20 certificados .tex** generados automáticamente
- **18 con ✅** (compatibilidad perfecta confirmada)
- **2 con ⚠️** (desviaciones menores en 32a1 y 50a1)
- Cada certificado puede compilarse a **PDF** con pdflatex
- **Firma institucional ICQ** en todos los documentos
- **Totalmente reproducible** a partir del archivo JSON

## 🔬 Fundamento Matemático

### Teoría de Hodge p-ádica

La compatibilidad dR es fundamental en la teoría de Hodge p-ádica de Fontaine. Para una curva elíptica $E/\mathbb{Q}$ y un primo $p$:

1. **Representación de Galois**: $V_p(E) = T_p(E) \otimes_{\mathbb{Z}_p} \mathbb{Q}_p$
2. **Cohomología de Selmer**: $H^1_f(\mathbb{Q}_p, V_p(E))$ (condición finita)
3. **Módulo de de Rham**: $D_{\mathrm{dR}}(V_p(E))$ con filtración
4. **Compatibilidad**: $\dim H^1_f = \dim D_{\mathrm{dR}}/\mathrm{Fil}^0$

### Casos Especiales

**Reducción buena ordinaria**: Las dimensiones coinciden perfectamente (1 en cada lado).

**Reducción multiplicativa**: Compatible vía parametrización de Tate.

**Reducción aditiva**: Puede haber desviaciones dimensionales, especialmente en $p=2$ o $p=5$, debido a estructuras de torsión local complejas.

## 📝 Ejemplo de Certificado Generado

Para la curva 11a1:

```latex
\documentclass[12pt]{article}
...
\textbf{Curva:} EllipticCurve('11a1')
\textbf{Fecha:} \today
\textbf{Autor:} José Manuel Mota Burruezo (JMMB Ψ·∴)

\section*{Resultados Locales (p-adic)}
\begin{tabular}{cccc}
...
2 & 1 & 1 & \OK\\
3 & 1 & 1 & \OK\\
5 & 1 & 1 & \OK\\
11 & 1 & 1 & \OK\\
...
\end{tabular}

\section*{Conclusión}
✅ Compatibilidad dR confirmada. La dimensión de $H^1_f$ coincide 
con la de $D_{\mathrm{dR}}/\mathrm{Fil}^0$ en todos los primos analizados.
```

## ✅ Validación y Trazabilidad

Cada certificado incluye:
- **Repositorio**: motanova84/adelic-bsd
- **Versión**: dR-Uniformity v1.0
- **Fecha automática**: `\today` en LaTeX
- **Firma institucional**: ICQ
- **Datos fuente**: validation_dR_uniformity_results.json

## 📚 Referencias

- Fontaine, J.-M. (1994). "Le corps des périodes p-adiques"
- Perrin-Riou, B. (1995). "Fonctions L p-adiques"
- Bloch, S. & Kato, K. (1990). "L-functions and Tamagawa numbers"

## 🎓 Autor

**José Manuel Mota Burruezo (JMMB Ψ·∴)**  
Instituto Conciencia Cuántica (ICQ)  
Proyecto Adelic-BSD — Validación Noésica

---

*Generado por el sistema automatizado de certificación dR del framework adelic-BSD*
