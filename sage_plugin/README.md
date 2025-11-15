# SageMath Plugin: adelic_bsd

Plugin SageMath para verificación empírica de la conjetura de Birch y Swinnerton-Dyer.

## 📦 Estructura del Plugin

```
sage_plugin/
├── adelic_bsd/
│   ├── __init__.py      # Exports del módulo
│   └── verify.py        # Función verify_bsd()
├── setup.py             # Instalador del plugin
├── DEMO_bsd_sage.ipynb  # Notebook de demostración (kernel SageMath)
└── README.md            # Este archivo
```

## ✅ ¿Qué hace este módulo?

Permite verificar empíricamente la conjetura de Birch y Swinnerton-Dyer para cualquier curva elíptica reconocida por LMFDB (ej: "11a1"):

- Evalúa la función L en s=1
- Calcula el rango analítico
- Devuelve un hash de integridad (sha256) de los valores para trazabilidad simbiótica

## 🚀 Instalación

### Opción 1: Instalación local en SageMath

```bash
cd sage_plugin
sage -pip install -e .
```

### Opción 2: Instalación sin modo desarrollo

```bash
cd sage_plugin
sage -pip install .
```

## 📖 Uso

### En un script Python con SageMath

```python
from adelic_bsd import verify_bsd

# Verificar usando etiqueta LMFDB
result = verify_bsd("11a1", s=1)

# Mostrar resultados
for k, v in result.items():
    print(f"{k}: {v}")
```

### En Jupyter Notebook con kernel SageMath

Ejecuta el notebook de demostración:

```bash
jupyter notebook DEMO_bsd_sage.ipynb
```

Asegúrate de seleccionar el kernel **SageMath** en el notebook.

### Ejemplo de salida

```python
{
    "curve_label": "11a1",
    "conductor": 11,
    "L(s)": 0.2538418608559107,
    "s": 1,
    "analytic_rank": 0,
    "hash_sha256": "a7f3d2e1..."
}
```

## 🔧 Parámetros de verify_bsd()

```python
def verify_bsd(label_or_curve, s=1):
    """
    Args:
        label_or_curve (str | EllipticCurve): 
            - Etiqueta LMFDB (ej: "11a1", "37a1")
            - O un objeto EllipticCurve de SageMath
        
        s (float): 
            Punto de evaluación de la función L (default: 1)
    
    Returns:
        dict: Diccionario con resultados del análisis:
            - curve_label: Etiqueta de la curva
            - conductor: Conductor de la curva
            - L(s): Valor de la función L en s
            - s: Punto de evaluación
            - analytic_rank: Rango analítico
            - hash_sha256: Hash SHA-256 para trazabilidad
    """
```

## 📊 Ejemplos Adicionales

### Verificar múltiples curvas

```python
from adelic_bsd import verify_bsd

curves = ["11a1", "37a1", "389a1"]
results = []

for label in curves:
    result = verify_bsd(label)
    results.append(result)
    print(f"Curva {label}: L(1) = {result['L(s)']}, rango = {result['analytic_rank']}")
```

### Usar objeto EllipticCurve directamente

```python
from sage.all import EllipticCurve
from adelic_bsd import verify_bsd

E = EllipticCurve([0, -1, 1, -10, -20])  # Curva 11a1
result = verify_bsd(E, s=1)
print(result)
```

### Evaluar en diferentes puntos

```python
from adelic_bsd import verify_bsd

# Evaluar L en s=2
result = verify_bsd("11a1", s=2)
print(f"L(2) = {result['L(s)']}")
```

## 🔗 Integración con el Repositorio

Este plugin complementa el framework espectral adelico principal:

- **Repositorio principal**: https://github.com/motanova84/adelic-bsd
- **Framework espectral**: `/src/` y `/spectral_RH/`
- **Validación numérica**: Scripts en raíz del repositorio

## 📚 Referencias

- [JMMB2025] José Manuel Mota Burruezo, "A Complete Spectral Reduction of the Birch-Swinnerton-Dyer Conjecture", 2025
- LMFDB: https://www.lmfdb.org/EllipticCurve/Q/
- SageMath: https://www.sagemath.org/

## 🤝 Contribuciones

Para reportar issues o sugerir mejoras:

1. Visita el repositorio: https://github.com/motanova84/adelic-bsd
2. Abre un issue describiendo el problema o mejora
3. Si deseas contribuir código, abre un pull request

## 📄 Licencia

Este plugin forma parte del repositorio adelic-bsd y está bajo la misma licencia (MIT License).

## ✨ Autor

**José Manuel Mota Burruezo**
- Repositorio: https://github.com/motanova84/adelic-bsd

---

**Versión**: 0.1.0  
**Última actualización**: 2025
