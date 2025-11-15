# SageMath Plugin: adelic_bsd

Plugin SageMath para verificación espectral de la conjetura BSD con certificación criptográfica AIK (Activo Inmutable de Conocimiento).

## 🌟 Características Principales

- **Verificación BSD**: Cálculo de funciones L y rango analítico
- **AIK Beacon**: Sistema de certificación criptográfica
  - Hash de integridad SHA-256
  - Firma ECDSA (SECP256R1)
  - Timestamps UTC para inmutabilidad
  - Verificación independiente

## Instalación

Desde el directorio `sage_plugin`:

```bash
sage -pip install -e .
```

Dependencias adicionales:
```bash
pip install cryptography>=41.0.0
```

## Uso Básico

### Verificación Simple (Backward Compatible)

```python
from adelic_bsd import verify_bsd

# Verificar curva usando etiqueta LMFDB (sin AIK beacon)
result = verify_bsd("11a1", s=1, generate_aik_beacon=False)

# Resultado contiene:
# - curve_label: Etiqueta de la curva
# - conductor: Conductor de la curva
# - L(s): Valor de la función L en s
# - s: Punto de evaluación
# - analytic_rank: Rango analítico
# - hash_sha256: Hash SHA256 del valor L(s)
```

### Verificación con AIK Beacon (Recomendado)

```python
from adelic_bsd import verify_bsd

# Verificación completa con certificación criptográfica
result = verify_bsd("11a1", s=1, generate_aik_beacon=True)

# Acceder al beacon AIK
beacon = result['aik_beacon']
print(f"Integrity Hash: {beacon['integrity_hash']}")
print(f"Timestamp: {beacon['timestamp']}")
print(f"Scientific Claim: {beacon['verification_info']['scientific_claim']}")

# Guardar certificado
import json
with open('bsd_11a1_certificate.json', 'w') as f:
    json.dump(result, f, indent=2, default=str)
```

### Verificación Independiente de Certificados

```python
from adelic_bsd import verify_ecdsa_signature
import json

# Cargar certificado guardado
with open('bsd_11a1_certificate.json', 'r') as f:
    cert = json.load(f)

beacon = cert['aik_beacon']

# Verificar firma criptográfica
is_valid = verify_ecdsa_signature(
    beacon['integrity_hash'],
    beacon['signature']
)

if is_valid:
    print("✓ Certificado válido y sin adulteraciones")
else:
    print("✗ Certificado ha sido manipulado!")
```

### Uso con Objetos EllipticCurve

```python
from sage.all import EllipticCurve
from adelic_bsd import verify_bsd

# Crear curva elíptica
E = EllipticCurve([0, -1, 1, -10, -20])

# Verificar con AIK beacon
result = verify_bsd(E, s=1, generate_aik_beacon=True)
```

## 🔐 AIK Beacon: Activo Inmutable de Conocimiento

El sistema AIK eleva las verificaciones BSD al estándar de certificación científica criptográfica:

### 1. Auditoría de Integridad
- **integrity_hash**: Huella digital SHA-256 del dataset y parámetros
- Detecta automáticamente cualquier modificación de datos
- Invalida la cadena de confianza si los datos difieren

### 2. Inmutabilidad (Noēsis ∞³)
- **Firma ECDSA**: Certificación criptográfica en punto fijo del tiempo
- Algoritmo: ECDSA-SECP256R1-SHA256
- Garantiza autenticidad por la autoridad del nodo

### 3. Integración SageMath
- Ubicado en `/sage_plugin/` para ecosistema SageMath
- Compatible con LMFDB
- Verificación independiente para comunidad matemática

## API Completa

### Funciones Principales

- `verify_bsd(label_or_curve, s=1, generate_aik_beacon=True)` - Verificación BSD
- `generate_integrity_hash(curve_data, l_value, params)` - Hash de integridad
- `generate_ecdsa_signature(integrity_hash, private_key=None)` - Firma ECDSA
- `verify_ecdsa_signature(integrity_hash, signature_data)` - Verificación de firma

Ver documentación completa en `docs/AIK_BEACON_DOCUMENTATION.md`

## Ejemplos y Demos

### Notebooks y Scripts
- `DEMO_bsd_sage.ipynb` - Notebook de demostración original
- `examples/aik_beacon_demo.py` - Demostración completa del sistema AIK

### Tests
```bash
# Ejecutar tests AIK
pytest tests/test_aik_beacon.py -v

# O directamente
python tests/test_aik_beacon.py
```

## Estructura del Proyecto

```
sage_plugin/
├── adelic_bsd/
│   ├── __init__.py      # Exporta verify_bsd y funciones AIK
│   └── verify.py        # Implementación principal con AIK beacon
├── setup.py             # Configuración del paquete
├── DEMO_bsd_sage.ipynb  # Notebook de demostración
└── README.md            # Esta documentación
```

## Requisitos

### Core
- SageMath >= 9.8
- Python >= 3.9

### Dependencias
- cryptography >= 41.0.0 (para firmas ECDSA)
- mpmath (opcional)
- sympy (opcional)

## Seguridad

### Garantías Criptográficas
- **SHA-256**: Resistente a colisiones
- **SECP256R1**: Curva P-256 recomendada por NIST (128 bits seguridad)
- **ECDSA**: Estándar industrial para firmas digitales

### Detección de Adulteración
El sistema detecta automáticamente:
- Modificación de valores L(s)
- Cambios en parámetros de verificación
- Alteración de datos de curva
- Falsificación de firmas

## Integración QCAL

Compatible con el sistema QCAL (Quantum Consciousness Active Link):
- Frecuencia: 141.7001 Hz
- Protocolo: Noēsis ∞³
- Framework: adelic-spectral
- Estándar: AIK-v1.0

Ver `.qcal_beacon` en la raíz del repositorio.

## Autor

José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)  
ORCID: https://orcid.org/0009-0002-1923-0773

## Licencia

Creative Commons BY-NC-SA 4.0

## Referencias

### Matemáticas
- [LMFDB - L-functions and Modular Forms Database](https://www.lmfdb.org/)
- [SageMath Documentation](https://doc.sagemath.org/)
- Birch and Swinnerton-Dyer Conjecture

### Criptografía
- NIST FIPS 180-4 (SHA-256)
- NIST FIPS 186-4 (ECDSA)
- RFC 6979 (Deterministic ECDSA)

### Framework
- QCAL: Quantum Consciousness Active Link
- Noēsis ∞³: Protocolo de inmutabilidad
