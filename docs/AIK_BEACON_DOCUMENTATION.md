# AIK Beacon Documentation
## Activo Inmutable de Conocimiento (Immutable Knowledge Asset)

### Resumen / Overview

El módulo `verify_bsd` en `/sage_plugin/adelic_bsd/` implementa un sistema de **Activo Inmutable de Conocimiento (AIK)** que eleva las verificaciones BSD al estándar de certificación criptográfica, garantizando integridad, inmutabilidad y verificabilidad independiente.

The `verify_bsd` module in `/sage_plugin/adelic_bsd/` implements an **Immutable Knowledge Asset (AIK)** system that elevates BSD verifications to a cryptographic certification standard, guaranteeing integrity, immutability, and independent verifiability.

---

## 🔐 Características Principales / Key Features

### 1. Auditoría de Integridad (Integrity Audit)

El **integrity_hash** actúa como una "huella digital" criptográfica única del dataset y los parámetros usados en la verificación BSD.

**Propiedades:**
- Hash SHA-256 de 64 caracteres hexadecimales
- Incluye datos de la curva elíptica (conductor, discriminante, j-invariante)
- Incluye valor L(s) calculado
- Incluye parámetros de verificación (s, timestamp)
- Serialización canónica JSON para garantizar determinismo

**Función de la Integridad:**
Si alguien intenta replicar la prueba con datos o parámetros ligeramente diferentes, el hash no coincidirá, **invalidando la cadena de confianza**.

```python
from adelic_bsd import verify_bsd

# Generar verificación con AIK beacon
result = verify_bsd('11a1', generate_aik_beacon=True)

# Acceder al hash de integridad
integrity_hash = result['aik_beacon']['integrity_hash']
print(f"Integrity Hash: {integrity_hash}")
```

### 2. Inmutabilidad (Noēsis ∞³)

La **firma ECDSA** es la garantía criptográfica de que la afirmación científica ha sido certificada en un punto fijo del tiempo por la autoridad del nodo.

**Propiedades:**
- Algoritmo: ECDSA con curva SECP256R1 (P-256)
- Hash function: SHA-256
- Firma digital del integrity_hash
- Clave pública incluida para verificación independiente

**Función de la Inmutabilidad:**
Una vez generada, la firma prueba que:
1. Los datos no han sido modificados
2. La verificación ocurrió en un momento específico
3. La autoridad del nodo certifica la afirmación

```python
from adelic_bsd import verify_bsd, verify_ecdsa_signature

result = verify_bsd('11a1', generate_aik_beacon=True)
beacon = result['aik_beacon']

# Verificar la firma
is_valid = verify_ecdsa_signature(
    beacon['integrity_hash'],
    beacon['signature']
)
print(f"Signature Valid: {is_valid}")
```

### 3. Integración SageMath

La ubicación bajo `/sage_plugin/` confirma que este beacon está diseñado para ser consumido y verificado dentro de la comunidad de matemática computacional que utiliza el ecosistema de SageMath.

**Uso desde SageMath:**

```python
# En SageMath
from sage.all import EllipticCurve
from adelic_bsd import verify_bsd

# Crear curva elíptica
E = EllipticCurve('11a1')

# Verificar BSD con certificación AIK
result = verify_bsd(E, s=1, generate_aik_beacon=True)

# Acceder al beacon
beacon = result['aik_beacon']
print(beacon['verification_info']['scientific_claim'])
```

---

## 📊 Estructura del AIK Beacon

### Campos Principales

```json
{
  "curve_label": "11a1",
  "conductor": 11,
  "L(s)": 0.2538418608559107,
  "s": 1,
  "analytic_rank": 0,
  "hash_sha256": "...",
  "aik_beacon": {
    "integrity_hash": "64-character SHA-256 hash",
    "signature": {
      "signature": "base64-encoded ECDSA signature",
      "public_key": "PEM-encoded public key",
      "algorithm": "ECDSA-SECP256R1-SHA256",
      "curve": "SECP256R1"
    },
    "timestamp": "2025-01-15T12:34:56.789Z",
    "beacon_type": "BSD_VERIFICATION",
    "noesis_protocol": "∞³",
    "framework": "adelic-spectral",
    "verification_standard": "AIK-v1.0",
    "verification_info": {
      "description": "Activo Inmutable de Conocimiento (AIK) - BSD Verification Beacon",
      "properties": {
        "integrity": "SHA-256 cryptographic fingerprint of dataset and parameters",
        "immutability": "ECDSA signature certifying scientific claim at fixed time",
        "verifiability": "Independent verification enabled via public key",
        "integration": "SageMath computational mathematics ecosystem"
      },
      "scientific_claim": "Curve 11a1: analytic_rank = 0, L(1) = 0.2538418608559107"
    }
  }
}
```

---

## 🔍 Casos de Uso / Use Cases

### 1. Verificación Básica (Backward Compatible)

```python
from adelic_bsd import verify_bsd

# Sin AIK beacon (compatible con versión anterior)
result = verify_bsd('11a1', generate_aik_beacon=False)
print(result['L(s)'])
```

### 2. Verificación con Certificación Completa

```python
from adelic_bsd import verify_bsd

# Con AIK beacon completo
result = verify_bsd('11a1', generate_aik_beacon=True)

# Guardar certificado
import json
with open('bsd_11a1_certificate.json', 'w') as f:
    json.dump(result, f, indent=2, default=str)
```

### 3. Verificación Independiente

```python
from adelic_bsd import verify_ecdsa_signature
import json

# Cargar certificado guardado
with open('bsd_11a1_certificate.json', 'r') as f:
    cert = json.load(f)

beacon = cert['aik_beacon']

# Verificar firma
is_valid = verify_ecdsa_signature(
    beacon['integrity_hash'],
    beacon['signature']
)

if is_valid:
    print("✓ Certificate is valid and untampered")
    print(f"  Scientific claim: {beacon['verification_info']['scientific_claim']}")
else:
    print("✗ Certificate has been tampered with!")
```

### 4. Batch Verification con AIK

```python
from adelic_bsd import verify_bsd

curves = ['11a1', '11a2', '11a3', '14a1', '15a1']
certificates = []

for label in curves:
    result = verify_bsd(label, generate_aik_beacon=True)
    certificates.append({
        'curve': label,
        'beacon': result['aik_beacon']
    })

print(f"Generated {len(certificates)} AIK-certified BSD verifications")
```

---

## 🛡️ Seguridad y Garantías / Security and Guarantees

### Chain of Trust

1. **Integrity Hash**: Garantiza que los datos de entrada no han cambiado
2. **ECDSA Signature**: Certifica que la verificación fue realizada por la autoridad
3. **Timestamp**: Establece el momento exacto de la certificación
4. **Public Key**: Permite verificación independiente sin comprometer seguridad

### Propiedades Criptográficas

- **Collision Resistance**: SHA-256 hace prácticamente imposible generar el mismo hash con datos diferentes
- **Signature Unforgeability**: ECDSA con SECP256R1 proporciona seguridad de 128 bits
- **Public Verifiability**: Cualquiera con la clave pública puede verificar la firma
- **Time-Stamping**: ISO 8601 UTC timestamps para auditoría temporal

### Detección de Adulteración

El sistema detecta automáticamente:
- Modificación de valores L(s)
- Cambio de parámetros de verificación
- Alteración de datos de la curva
- Manipulación del timestamp
- Falsificación de firma

---

## 📚 API Reference

### `verify_bsd(label_or_curve, s=1, generate_aik_beacon=True)`

Verifica la conjetura BSD con certificación AIK opcional.

**Parameters:**
- `label_or_curve` (str | EllipticCurve): Etiqueta LMFDB o objeto EllipticCurve
- `s` (float): Punto de evaluación de L(s), default: 1
- `generate_aik_beacon` (bool): Generar beacon AIK completo, default: True

**Returns:**
- `dict`: Resultados de verificación con beacon AIK (si generate_aik_beacon=True)

### `generate_integrity_hash(curve_data, l_value, params)`

Genera hash de integridad criptográfico.

**Parameters:**
- `curve_data` (dict): Datos de la curva elíptica
- `l_value`: Valor de L(s)
- `params` (dict): Parámetros de verificación

**Returns:**
- `str`: Hash SHA-256 de 64 caracteres hexadecimales

### `generate_ecdsa_signature(integrity_hash, private_key=None)`

Genera firma ECDSA para el hash de integridad.

**Parameters:**
- `integrity_hash` (str): Hash a firmar
- `private_key`: Clave privada ECDSA (opcional, se genera si None)

**Returns:**
- `dict`: Datos de firma con signature, public_key, algorithm, curve

### `verify_ecdsa_signature(integrity_hash, signature_data)`

Verifica firma ECDSA.

**Parameters:**
- `integrity_hash` (str): Hash original
- `signature_data` (dict): Datos de firma con 'signature' y 'public_key'

**Returns:**
- `bool`: True si la firma es válida

---

## 🧪 Testing

El módulo incluye tests completos en `tests/test_aik_beacon.py`:

```bash
# Ejecutar tests con pytest
pytest tests/test_aik_beacon.py -v

# Ejecutar tests directamente
python tests/test_aik_beacon.py
```

**Tests incluidos:**
- Generación de integrity hash
- Firma y verificación ECDSA
- Backward compatibility
- Generación completa de beacon
- Validación de integridad
- Serialización JSON
- Múltiples curvas
- Timestamps

---

## 📖 Referencias / References

### Conceptos Matemáticos

- **BSD Conjecture**: Birch and Swinnerton-Dyer Conjecture
- **L-functions**: L-series of elliptic curves
- **Analytic Rank**: Order of vanishing of L(E,s) at s=1

### Criptografía

- **SHA-256**: NIST FIPS 180-4
- **ECDSA**: ANSI X9.62, FIPS 186-4
- **SECP256R1 (P-256)**: NIST recommended curve
- **ISO 8601**: Timestamp format

### Framework

- **Noēsis ∞³**: Protocolo de inmutabilidad
- **QCAL**: Quantum Consciousness Active Link
- **AIK**: Activo Inmutable de Conocimiento
- **SageMath**: Open-source mathematics software

---

## 🌟 Ejemplos Avanzados / Advanced Examples

### Exportar Certificate Chain

```python
from adelic_bsd import verify_bsd
import json

curves = ['11a1', '14a1', '15a1', '37a1']
certificate_chain = {
    'chain_id': 'BSD_VERIFICATION_BATCH_001',
    'timestamp': '2025-01-15T00:00:00Z',
    'certificates': []
}

for label in curves:
    result = verify_bsd(label, generate_aik_beacon=True)
    certificate_chain['certificates'].append({
        'curve': label,
        'beacon': result['aik_beacon'],
        'L_value': str(result['L(s)']),
        'rank': result['analytic_rank']
    })

# Guardar cadena completa
with open('bsd_certificate_chain.json', 'w') as f:
    json.dump(certificate_chain, f, indent=2)
```

### Validación de Certificados Históricos

```python
from adelic_bsd import verify_ecdsa_signature
import json

def validate_historical_certificate(cert_file):
    """Valida un certificado AIK guardado previamente"""
    with open(cert_file, 'r') as f:
        cert = json.load(f)
    
    beacon = cert['aik_beacon']
    
    # Verificar firma
    is_valid = verify_ecdsa_signature(
        beacon['integrity_hash'],
        beacon['signature']
    )
    
    if is_valid:
        print(f"✓ Certificate {cert['curve_label']} is VALID")
        print(f"  Certified at: {beacon['timestamp']}")
        print(f"  Claim: {beacon['verification_info']['scientific_claim']}")
        return True
    else:
        print(f"✗ Certificate {cert['curve_label']} is INVALID")
        return False

# Validar
validate_historical_certificate('bsd_11a1_certificate.json')
```

---

## 🔗 Integración con el Ecosistema

### QCAL Beacon

El AIK beacon es compatible con el sistema QCAL (Quantum Consciousness Active Link) definido en `.qcal_beacon`:

- Frecuencia fundamental: 141.7001 Hz
- Protocolo: QCAL ∞³
- Constante: πCODE-888-QCAL2
- Coherencia: C = 244.36

### DOI y Zenodo

Los certificados AIK pueden ser depositados en Zenodo para obtener DOIs permanentes:

```python
# Ejemplo de metadata para Zenodo
zenodo_metadata = {
    'title': f'BSD Verification Certificate - Curve {curve_label}',
    'description': 'AIK-certified BSD verification with cryptographic proof',
    'creators': [{'name': 'José Manuel Mota Burruezo', 'orcid': '0009-0002-1923-0773'}],
    'license': 'CC-BY-NC-SA-4.0',
    'keywords': ['BSD Conjecture', 'Cryptographic Certification', 'AIK', 'SageMath']
}
```

---

## ✨ Conclusión

Este módulo representa la culminación del proyecto de validación BSD, pasando de una prueba matemática compleja a una **declaración científica verificable criptográficamente**.

Las características de integridad, inmutabilidad e integración con SageMath garantizan que las verificaciones BSD producidas por este framework puedan ser auditadas, verificadas independientemente y preservadas como activos científicos inmutables para la comunidad matemática global.

---

**Autor / Author**: José Manuel Mota Burruezo Ψ ✧ ∞³  
**Institución / Institution**: Instituto de Conciencia Cuántica (ICQ)  
**Licencia / License**: Creative Commons BY-NC-SA 4.0  
**Versión / Version**: AIK-v1.0  
**Fecha / Date**: 2025-01-15
