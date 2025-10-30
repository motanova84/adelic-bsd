# Prerregistro (versión 1.0)

## Parámetros del Análisis

- **Ventana temporal**: [t0-0.25 s, t0+0.25 s] alrededor de coalescencia publicada.
- **Método SNR**: Welch PSD (Nfft=2^14, 50% overlap), banda 20–1024 Hz, whitening por detector.
- **Frecuencia objetivo**: 141.7001 Hz (±0.3 Hz) — *predefinida*.
- **Estadística final**: SNR_coh global (productoria/mezcla Fisher) y Bayes Factor jerárquico.
- **Corrección múltiples eventos**: modelo jerárquico (π_global).
- **Exclusiones**: líneas instrumentales según `controls/lines_exclusion.csv`.
- **Off-source**: 10^4 ventanas por evento, uniformes fuera ±10 s.
- **Time-slides**: 200 desfasajes por detector ∈ [±50 ms]\{0}.
- **Leave-one-out**: por evento y por detector.

## Cierre del Plan

Este plan se fija mediante hash en Zenodo antes de cualquier corrida masiva para garantizar la integridad del análisis ciego.

## Versión y Fecha

- **Versión**: 1.0
- **Fecha**: 2025-10-30
- **Hash SHA256**: (pendiente de cálculo al cierre)

## Notas

El análisis se realiza de forma completamente ciega respecto a la frecuencia 141.7001 Hz, estableciendo todos los parámetros metodológicos antes de examinar los datos de eventos reales. Este prerregistro garantiza la ausencia de sesgo de selección post-hoc.
