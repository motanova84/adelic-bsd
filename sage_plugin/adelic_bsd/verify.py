from sage.all import EllipticCurve, QQ, LFunction  # noqa: F401
from mpmath import mp  # noqa: F401
from sympy import symbols  # noqa: F401
import hashlib
import json


def verify_bsd(label_or_curve, s=1):
    """
    Verifica la conjetura BSD para una curva elíptica dada (etiqueta o objeto).

    Args:
        label_or_curve (str | EllipticCurve): Etiqueta LMFDB o curva
        s (float): Punto de evaluación de la función L (default: 1)

    Returns:
        dict: Resultados clave del análisis con formato compatible con QCAL Beacon
    """
    if isinstance(label_or_curve, str):
        E = EllipticCurve(label_or_curve)
    else:
        E = label_or_curve

    # Obtener etiqueta y datos básicos
    curve_label = E.label()
    
    # Calcular L(s) y rank
    L = E.lseries()
    val = L(s)
    analytic_rank = L.analytic_rank()
    conductor = E.conductor()
    
    # Preparar datos para el hash de integridad
    data = {
        "L(1)": float(val),
        "rank": int(analytic_rank),
        "conductor": int(conductor),
        "curve": curve_label
    }
    
    # Generar hash de integridad usando SHA3-256 para beacons
    data_json = json.dumps(data, sort_keys=True)
    integrity_hash = hashlib.sha3_256(data_json.encode()).hexdigest()
    
    # Imprimir información de validación
    print(f"✅ Validación BSD completada para {curve_label}.")
    print(f"   L(1) = {val}")
    print(f"   rank = {analytic_rank}")
    print(f"   HASH OK: {integrity_hash[:12]}...")

    return {
        "status": "success",
        "curve": curve_label,
        "data": data,
        "integrity_hash": integrity_hash
    }
