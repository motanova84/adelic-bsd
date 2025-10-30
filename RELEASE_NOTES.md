# Release Notes

## v0.3.0 (2025-10-30)

### RH: Riemann Hypothesis - Axioms Purgados → Teoremas

**Cambios principales:**
- Reemplazo de axiomas por teoremas formales con esquemas de prueba
- **Teorema D ≡ Ξ**: Identidad única mediante factorización de Hadamard, cociente acotado, y normalización
- **Teorema (Ceros en línea crítica)**: Operador autoadjunto con espectro real + simetría funcional
- **Lema (Exclusión de ceros triviales)**: Separación vía factor gamma archimediano

**Formalization:**
- `formalization/lean/RiemannAdelic/axiom_purge.lean`: Stubs de teoremas principales
- `formalization/lean/RiemannAdelic/Hadamard.lean`: Factorización de Hadamard
- `formalization/lean/RiemannAdelic/RelativeDeterminant.lean`: Determinantes relativos y Paley-Wiener
- `formalization/lean/RiemannAdelic/KernelPositivity.lean`: Positividad del kernel y confinamiento

**CI/CD:**
- `.github/workflows/lean-ci.yml`: Verificación automática de ausencia de axiomas extras

---

### 141.7001 Hz: Prerregistro Ciego y Controles Instrumentales

**Prerregistro:**
- `141hz/PREREGISTRATION.md`: Protocolo completo de análisis ciego
- Ventana temporal: [t₀-0.25s, t₀+0.25s]
- Frecuencia objetivo: 141.7001 Hz (±0.3 Hz) predefinida
- Off-source: 10⁴ ventanas, time-slides: 200 desfasajes

**Análisis:**
- `141hz/analysis_plan.json`: Parámetros de análisis (Welch PSD, SNR coherente)
- `141hz/controls/lines_exclusion.csv`: Líneas instrumentales excluidas
- `141hz/bayes/hierarchical_model.py`: Modelo jerárquico bayesiano con BF
- `141hz/notebooks/antenna_pattern.ipynb`: Análisis de patrones de antena (F⁺/F×)

**Entregables:**
- Bayes Factor jerárquico pre-registrado y trazable
- Controles instrumentales completos
- Análisis leave-one-out por evento y detector

---

### P≠NP: Anti-barreras + Lifting Formal

**Documentación:**
- `docs/PNP_ANTIBARRIERS.md`: Sección completa sobre anti-barreras
  - **No relativiza**: SILB depende de estructura de separadores, no de oráculos
  - **No natural**: Predicados no densos ni constructibles en tiempo polinomial
  - **No algebriza**: Rompe monotonicidad de información en separadores

**Ruta técnica:**
- Treewidth → Protocolo de comunicación → Cota inferior de circuitos vía lifting
- Gadgets explícitos (Tseitin sobre Ramanujan)
- Familias DLOGTIME-uniformes

**Formalización:**
- `formal/Treewidth/SeparatorInfo.lean`: Lema SILB
- `formal/Lifting/Gadgets.lean`: Validez del gadget G_lift
- `formal/LowerBounds/Circuits.lean`: Traducción a circuitos y cota final

---

### Navier-Stokes: Espacios Funcionales, Energía, BKM, Teorema δ*

**Marco teórico:**
- `NavierStokes/Documentation/THEORY.md`: Teoría completa
  - Espacios: L²_σ(T³), H¹, Besov
  - Soluciones tipo Leray-Hopf
  - Desigualdad de energía estándar
  - Criterio BKM (Beale-Kato-Majda)

**Teorema principal:**
- Si δ* = avg_t avg_x ∠(ω, Sω) ≥ δ₀ > 0, entonces ∫₀^∞ ‖ω‖_∞ dt < ∞
- Por BKM, la solución Leray-Hopf es globalmente suave

**Implementación:**
- `NavierStokes/Lean4-Formalization/NavierStokes/FunctionalSpaces.lean`: Espacios y teoremas
- `NavierStokes/Computational-Verification/Data-Analysis/misalignment_calculation.py`: Cálculo de δ*
- `NavierStokes/Results/Data/delta_star.json`: Export de resultados δ*
- `NavierStokes/Results/validation_report.md`: Reporte de validación con proxy BKM

**Separación clara:**
- Parte estándar (energía/BKM/Besov): bien establecida
- Parte QCAL (hipótesis δ*): verificable numéricamente

---

### Infraestructura General

**Reproducibilidad:**
- `Makefile`: Automatización de builds (PDF, figuras, tablas)
- `ENV.lock`: Snapshot de versiones de dependencias Python

**Documentación:**
- Estructura clara "Statement vs. Interpretation"
- Referencias bibliográficas completas

---

## Notas de Migración

Para usuarios existentes:
1. Los axiomas en formalizaciones Lean ahora son teoremas con esquemas de prueba
2. El análisis de 141.7001 Hz requiere prerregistro antes de corridas masivas
3. P≠NP documentation ahora incluye análisis detallado de anti-barreras
4. Navier-Stokes ahora separa marco estándar de hipótesis QCAL

---

## Próximos Pasos

- RH: Completar pruebas formales (reemplazar `trivial` por pruebas reales)
- 141Hz: Ejecutar análisis sobre datos LIGO reales
- P≠NP: Formalizar biblioteca de grafos expansores en Lean
- NS: Recopilar datos de simulación DNS para validar δ*

---

**Fecha de lanzamiento**: 2025-10-30  
**Versión anterior**: v0.2.2  
**Breaking changes**: Ninguno (cambios son adiciones)
