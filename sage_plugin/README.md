# SageMath Plugin: adelic_bsd

Plugin SageMath para verificación espectral de la conjetura BSD.

## Instalación

Desde el directorio `sage_plugin`:

```bash
sage -pip install -e .
```

## Uso

### Verificación BSD básica

```python
from adelic_bsd import verify_bsd

# Verificar curva usando etiqueta LMFDB
result = verify_bsd("11a1", s=1)

# O usando un objeto EllipticCurve directamente
from sage.all import EllipticCurve
E = EllipticCurve([0, -1, 1, -10, -20])
result = verify_bsd(E, s=1)

# Resultado contiene:
# - status: "success"
# - curve: Etiqueta de la curva
# - data: dict con L(1), rank, conductor
# - integrity_hash: Hash SHA3-256 para trazabilidad
```

### Generar QCAL Beacon firmado

```python
from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd

# Genera un beacon criptográficamente firmado
beacon = generate_qcal_beacon_for_bsd("11a1")

# Salida esperada:
# ✅ Validación BSD completada para 11a1.
#    L(1) = 0.253841...
#    rank = 0
#    HASH OK: b23a1c9d...
#    Firma ECDSA generada.
# ✅ Beacon generado: sage_plugin/beacons/qcal_beacon_bsd_11a1.json
```

### Desde línea de comandos

```bash
sage -python - << 'EOF'
from adelic_bsd.qcal_beacon_bsd import generate_qcal_beacon_for_bsd
generate_qcal_beacon_for_bsd("11a1")
EOF
```

## Demo

Ver el notebook `DEMO_bsd_sage.ipynb` para ejemplos completos.

## Estructura

```
sage_plugin/
├── adelic_bsd/
│   ├── __init__.py           # Exporta verify_bsd y generate_qcal_beacon_for_bsd
│   ├── verify.py             # Verificación BSD
│   └── qcal_beacon_bsd.py    # Generador de QCAL Beacons firmados
├── beacons/                   # Directorio para beacons generados
├── setup.py                   # Configuración del paquete
├── DEMO_bsd_sage.ipynb        # Notebook de demostración
└── README.md                  # Esta documentación
```

## Requisitos

- SageMath >= 9.8
- Python >= 3.9
- mpmath
- sympy
- cryptography >= 41.0.0 (para QCAL Beacons)

## Formato del QCAL Beacon

El archivo JSON generado contiene:

```json
{
  "qcal_beacon": {
    "id": "uuid-v4",
    "timestamp": "2025-11-15T13:00:00Z",
    "curve": "11a1",
    "L_at_1": 0.2538418608559107,
    "analytic_rank": 0,
    "integrity_hash": "sha3-256-hash",
    "validator_node": "Noēsis-∞³",
    "signature": {
      "signature_hex": "ecdsa-signature"
    },
    "message_signed": "curve|rank|L(1)|hash|beacon_id|Noesis∞³",
    "public_key_pem": "-----BEGIN PUBLIC KEY-----..."
  }
}
```

## Detalles Criptográficos

- **Algoritmo de firma**: ECDSA (Elliptic Curve Digital Signature Algorithm)
- **Curva elíptica**: SECP256R1 (P-256)
- **Función hash**: SHA3-256 (FIPS 202)
- **Formato de mensaje**: `curve|rank|L(1)|integrity_hash|beacon_id|Noesis∞³`

La firma ECDSA garantiza:
- **Integridad**: Cualquier modificación invalida la firma
- **Autenticidad**: Solo quien posee la clave privada puede firmar
- **No repudio**: La firma es verificable con la clave pública

**Nota de seguridad**: En producción, guarde las claves privadas en archivos PEM protegidos o en un HSM.

## Autor

José Manuel Mota Burruezo

## Referencias

- [JMMB2025] José Manuel Mota Burruezo, "A Complete Spectral Reduction of the Birch-Swinnerton-Dyer Conjecture", 2025
- [LMFDB - L-functions and Modular Forms Database](https://www.lmfdb.org/)
- [SageMath Documentation](https://doc.sagemath.org/)
