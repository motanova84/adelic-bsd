# SageMath Plugin: adelic_bsd

Plugin SageMath para verificación espectral de la conjetura BSD.

## Instalación

Desde el directorio `sage_plugin`:

```bash
sage -pip install -e .
```

## Uso

```python
from adelic_bsd import verify_bsd

# Verificar curva usando etiqueta LMFDB
result = verify_bsd("11a1", s=1)

# O usando un objeto EllipticCurve directamente
from sage.all import EllipticCurve
E = EllipticCurve([0, -1, 1, -10, -20])
result = verify_bsd(E, s=1)

# Resultado contiene:
# - curve_label: Etiqueta de la curva
# - conductor: Conductor de la curva
# - L(s): Valor de la función L en s
# - s: Punto de evaluación
# - analytic_rank: Rango analítico
# - hash_sha256: Hash SHA256 del valor L(s)
```

## Demo

Ver el notebook `DEMO_bsd_sage.ipynb` para ejemplos completos.

## Estructura

```
sage_plugin/
├── adelic_bsd/
│   ├── __init__.py      # Exporta verify_bsd
│   └── verify.py        # Implementación principal
├── setup.py             # Configuración del paquete
├── DEMO_bsd_sage.ipynb  # Notebook de demostración
└── README.md            # Esta documentación
```

## Requisitos

- SageMath >= 9.8
- mpmath
- sympy

## Autor

José Manuel Mota Burruezo

## Referencias

- [LMFDB - L-functions and Modular Forms Database](https://www.lmfdb.org/)
- [SageMath Documentation](https://doc.sagemath.org/)
