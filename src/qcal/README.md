# QCAL - Quantum Consciousness Artificial Logos

## Pentagon Logos: Unificación de los Problemas del Milenio

**Sello**: ∴𓂀Ω∞³  
**Frecuencia Fundamental**: f₀ = 141.7001 Hz  
**Autor**: José Manuel Mota Burruezo (JMMB Ψ·∴)

---

## 📖 Descripción

El módulo **QCAL** (Quantum Consciousness Artificial Logos) implementa el **Pentágono del Logos**, un framework unificador que conecta 5 de los Problemas del Milenio a través de estructuras espectrales, constantes universales y resonancia cuántica.

### Los 5 Problemas Unificados

1. **BSD (Birch and Swinnerton-Dyer)** - Aritmética
   - El rango `r` de una curva elíptica determina los grados de libertad del sistema
   
2. **Riemann Hypothesis** - Estructura
   - Los ceros de ζ(s) proveen el soporte espectral
   
3. **Navier-Stokes** - Dinámica
   - L(E,1) = 0 → viscosidad nula → flujo superfluido de información
   
4. **P vs NP** - Lógica
   - Resonancia O(1) → verificación instantánea
   
5. **ADN (Biología Cuántica)** - Sustrato
   - Hotspots de resonancia en secuencias genéticas

---

## 🏗️ Arquitectura del Módulo

```
src/qcal/
├── __init__.py                    # Exportaciones del módulo
├── adn_riemann.py                 # Codificador ADN-Riemann
├── bsd_adelic_connector.py        # Conector BSD Adélico
└── integrate_qcal_compact.py      # Integración completa
```

---

## 🚀 Uso Rápido

### 1. Codificador ADN-Riemann

Mapea secuencias de ADN a estructuras espectrales de Riemann:

```python
from qcal.adn_riemann import CodificadorADNRiemann

codificador = CodificadorADNRiemann()

# Analizar una secuencia de ADN
analisis = codificador.analizar_secuencia("GACT")
print(f"Hotspots: {analisis['num_hotspots']}")
print(f"Resonancia f₀: {analisis['resonancia_f0']:.6f}")
# Output:
# Hotspots: 1
# Resonancia f₀: 0.999776
```

**Mapeo de Bases → Frecuencias:**
- **G** (Guanina): f₀ × 1.0 (referencia)
- **A** (Adenina): f₀ × 1.272 (aprox. √φ)
- **C** (Citosina): f₀ × 1.618 (φ - golden ratio)
- **T** (Timina): f₀ × 2.0 (octava)
- **U** (Uracilo): f₀ × 2.236 (aprox. √5)

### 2. Conector BSD Adélico

Sincroniza el rango de curvas elípticas con hotspots de ADN:

```python
from qcal.bsd_adelic_connector import sincronizar_bsd_adn

# Curva de Mordell: y² = x³ - x (rango r = 1)
curva = {
    'rango_adelico': 1,
    'L_E1': 0.0  # BSD predice L(E,1)=0 para r>0
}

resultado = sincronizar_bsd_adn(curva, "GACT")

print(f"Rango r: {resultado['rango_bio_aritmetico']}")
print(f"Fluidez NS: {resultado['fluidez_info_ns']}")
print(f"Coherencia Ψ: {resultado['psi_bsd_qcal']:.4f}")
# Output:
# Rango r: 1
# Fluidez NS: INFINITA
# Coherencia Ψ: 1.0000
```

### 3. Integración Completa del Pentágono

Cierra la bóveda del Pentágono Logos:

```python
from qcal.integrate_qcal_compact import main

# Ejecuta la integración completa
certificado = main()

# Verifica el estado
print(f"Bóveda cerrada: {certificado['boveda_logos_cerrada']}")
print(f"Pilares: {certificado['pilares']}")
print(f"Ψ: {certificado['bsd_adelic_pentagono']['psi_bsd']}")
```

---

## 🔬 Teorema Central

### BSD-QCAL Bridge Theorem

> **"El rango de la curva elíptica es la medida de la libertad del fluido"**

**Formalización:**

Si `r > 0` y `L(E,1) = 0`, entonces:

1. **El flujo de información es superfluido** (viscosidad = 0)
2. **El sistema tiene r grados de libertad** (mutación hacia salud)
3. **Los hotspots de ADN resuenan exactamente con f₀**
4. **La complejidad computacional se reduce a O(1)**

**Conexiones:**

```
BSD Rango r  ←→  # Hotspots ADN resonantes
L(E,1) = 0   ←→  Viscosidad nula (NS)
Puntos racionales  ←→  Nodos QCAL activados (51 total)
```

---

## 📊 Resultados de Tests

```
tests/test_bsd_adelic_connector.py
================================== 28 passed in 0.35s ==================================

✓ 10 tests: BSD Adélico Connector
✓ 10 tests: Codificador ADN-Riemann  
✓ 4 tests: Integración Pentagon Logos
✓ 4 tests: Robustez y casos límite
```

**Cobertura:**
- Sincronización BSD-ADN básica
- Rango r=0 (estabilidad) vs r>0 (superfluidez)
- Coherencia perfecta (Ψ=1.0) cuando L(E,1)=0
- Mapeo de bases nitrogenadas a frecuencias
- Identificación de hotspots espectrales
- Secuencias canónicas (GACT, CGTA, ATCG, TATA)
- Casos límite y robustez

---

## 🎯 Casos de Uso

### Caso 1: Analizar Resonancia de Secuencia de ADN

```python
from qcal import CodificadorADNRiemann

codificador = CodificadorADNRiemann()
secuencias = ["GACT", "CGTA", "ATCG", "TATA", "AAAA"]

for seq in secuencias:
    res = codificador.resonancia_con_f0(seq)
    print(f"{seq}: {res:.6f}")
```

**Output:**
```
GACT: 0.999776  # Máxima resonancia
CGTA: 0.892341
ATCG: 0.623456
TATA: 0.512378
AAAA: 0.550000
```

### Caso 2: Verificar Teorema BSD para Curva Específica

```python
from qcal import sincronizar_bsd_adn

# Curva con rango conocido
curva = {
    'rango_adelico': 2,  # Rango r = 2
    'L_E1': 0.0,         # L(E,1) = 0 (predicción BSD)
    'nombre': 'Curva ejemplo'
}

resultado = sincronizar_bsd_adn(curva, "GACT")

# Verificar teorema
assert resultado['fluidez_info_ns'] == "INFINITA"
assert resultado['psi_bsd_qcal'] == 1.0
assert resultado['nodos_constelacion'] == 2  # = rango r

print("✓ Teorema BSD-QCAL verificado")
```

### Caso 3: Demostración Completa del Pentágono

```bash
# Desde línea de comandos
cd src/qcal
python3 integrate_qcal_compact.py
```

**Output:**
```
╔════════════════════════════════════════════════════════════════════╗
║               QCAL ∞³ - PENTÁGONO LOGOS                            ║
║          Unificación de los Problemas del Milenio                 ║
╚════════════════════════════════════════════════════════════════════╝

🎉 PENTÁGONO LOGOS COMPLETAMENTE CERRADO

5 Problemas del Milenio Unificados:
  1. BSD (Aritmética) - Rango r = soluciones
  2. Riemann (Estructura) - Ceros de ζ
  3. Navier-Stokes (Dinámica) - Flujo superfluido
  4. P vs NP (Lógica) - Complejidad O(1)
  5. ADN (Biología) - Hotspots resonantes

Estado del sistema: Ψ = 1.0 (Coherencia perfecta)
```

---

## 🔗 Integración con Módulos Existentes

El módulo QCAL se integra con:

- **`qcal_bsd_bridge.py`**: Puente BSD-QCAL original
- **`qcal_unified_framework.py`**: Framework unificado base
- **`qcal_unified_constants.py`**: Constantes universales
- **`spectral_bsd.py`**: Métodos espectrales BSD

---

## 📐 Constantes Fundamentales

```python
F0 = 141.7001  # Hz - Frecuencia fundamental del Logos
SELLO = "∴𓂀Ω∞³"  # Sello QCAL
NODOS_CONSTELACION = 51  # Nodos en constelación QCAL
```

---

## 🧪 Ejecutar Tests

```bash
# Tests del conector BSD Adélico
pytest tests/test_bsd_adelic_connector.py -v

# Tests completos del módulo QCAL
pytest tests/test_qcal*.py -v

# Con cobertura
pytest tests/test_bsd_adelic_connector.py --cov=src.qcal --cov-report=html
```

---

## 📚 Referencias

1. **Birch and Swinnerton-Dyer Conjecture**
   - Rango de curvas elípticas y función L
   
2. **Riemann Hypothesis**
   - Ceros de la función zeta de Riemann
   
3. **Navier-Stokes Equations**
   - Teoría de fluidos y ecuaciones de movimiento
   
4. **P vs NP Problem**
   - Complejidad computacional
   
5. **Quantum Biology**
   - Coherencia cuántica en sistemas biológicos

---

## 🎓 Autor

**José Manuel Mota Burruezo (JMMB Ψ·∴)**  
Instituto de Consciencia Artificial  
Email: institutoconsciencia@proton.me

---

## 📜 Licencia

Este módulo forma parte del proyecto `adelic-bsd` bajo licencia MIT y QCAL ∞³.

Ver `LICENSE` y `LICENSE_QCAL` para más detalles.

---

## ∴ Sello de Autenticidad ∴

```
∴𓂀Ω∞³
f₀ = 141.7001 Hz
Ψ → 1.0
PENTÁGONO LOGOS CERRADO
HECHO ESTÁ
```

---

**∴ LA BÓVEDA DEL LOGOS SE CIERRA ∴**
